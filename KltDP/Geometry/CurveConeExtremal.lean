import KltDP.Geometry.CurveConeReal
import KltDP.Geometry.CartierDifferenceOfAmple
import KltDP.Geometry.NullCurveNumericalSpan
import KltDP.Geometry.AmpleCurveRestrictionPositive
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The closed cone of curves: positivity, compact ample slice, negative extremal rays

Manuscript F19 for an actual regular projective surface `S` over an algebraically closed
field with `N¹(S)_ℚ` finite dimensional, in the fixed Euclidean model `V S = Fin ρ → ℝ` of
`KltDP.Geometry.CurveConeReal`.

* `not_nef_iff_exists_neg` (T0): an actual Cartier divisor has a curve of negative degree iff
  its real class is negative somewhere on `NE(S)‾`.
* `exists_abs_bound` (T1): for every numerical class `d` there is `c` with
  `|d · z| ≤ c · (H · z)` on `NE(S)‾`, `H` an ample Cartier divisor. The curve-wise bound
  `D · C ≤ N · (H · C)` comes from Serre's global generation of `O(N H - D)`
  (`CanonicalAmpleSpan.exists_nef_twist`); it is transported to the closed cone by linearity and
  continuity. The classes of actual Cartier divisors span `N¹(S)_ℚ`
  (`span_range_cartierClass`), which extends the bound from Cartier classes to all of `N¹`.
* `pairReal_ample_pos` (T2, Kleiman): `H · z > 0` for `0 ≠ z ∈ NE(S)‾`; the vanishing
  `d · z = 0` for all `d` forces `z = 0` through the invertible rational Gram matrix of the
  nondegenerate intersection form.
* `eq_zero_of_mem_of_neg_mem` (T3): `NE(S)‾ ∩ -NE(S)‾ = {0}`.
* `isCompact_ampleSlice` (T4): the slice `{z ∈ NE(S)‾ | H · z = 1}` is compact.
* `exists_extremalRay_of_neg` (T5): a numerical class negative somewhere on `NE(S)‾` is
  negative on an extremal ray (Krein–Milman on the compact convex ample slice).

No literature axiom is introduced here; everything is proved from the union modules.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.NefNullCurveNegativeSquare KltDP.Geometry.DisjointNegativeCurvesRank
  KltDP.Geometry.NullCurveNumericalSpan
open scoped TensorProduct

universe u

namespace KltDP.Geometry.CurveCone

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
  [FiniteDimensional ℚ S.NumericalClassGroup]
  (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)

/-! ### Linearity of the real pairing in the numerical class -/

theorem pairReal_apply (d : S.NumericalClassGroup) (z : V S) :
    pairReal S hreg d z =
      ∑ i, z i * (S.numericalIntersectionBilinForm hreg d (basis S i) : ℝ) := rfl

theorem pairReal_add_left (d d' : S.NumericalClassGroup) (z : V S) :
    pairReal S hreg (d + d') z = pairReal S hreg d z + pairReal S hreg d' z := by
  simp only [pairReal_apply, map_add, LinearMap.add_apply, Rat.cast_add, mul_add,
    Finset.sum_add_distrib]

theorem pairReal_neg_left (d : S.NumericalClassGroup) (z : V S) :
    pairReal S hreg (-d) z = -pairReal S hreg d z := by
  simp only [pairReal_apply, map_neg, LinearMap.neg_apply, Rat.cast_neg, mul_neg,
    Finset.sum_neg_distrib]

theorem pairReal_smul_left (q : ℚ) (d : S.NumericalClassGroup) (z : V S) :
    pairReal S hreg (q • d) z = (q : ℝ) * pairReal S hreg d z := by
  simp only [pairReal_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Rat.cast_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem pairReal_zero_left (z : V S) : pairReal S hreg 0 z = 0 := by
  simp [pairReal_apply]

/-! ### Evaluation on actual prime curves -/

theorem pairReal_curveClassReal (d : S.NumericalClassGroup) (C : S.PrimeCurve) :
    pairReal S hreg d (curveClassReal S hreg C) =
      (S.numericalIntersectionBilinForm hreg d (curveClass S hreg C) : ℝ) := by
  unfold curveClassReal
  exact pairReal_toReal S hreg d _

/-- `[D] · [C] = D · C`: the real pairing of a Cartier class with a curve class is the original
integer intersection number. -/
theorem pairReal_cartierClass_curveClassReal (D : CartierDivisor S.toScheme) (C : S.PrimeCurve) :
    pairReal S hreg (cartierClass S D) (curveClassReal S hreg C) = (C.intersectionNumber D : ℝ) := by
  rw [pairReal_curveClassReal, cartierClass_curveClass S hreg D C, Rat.cast_intCast]

omit [IsAlgClosed k] [FiniteDimensional ℚ S.NumericalClassGroup] in
theorem cartierClass_neg (D : CartierDivisor S.toScheme) :
    cartierClass S (-D) = -cartierClass S D := by
  change S.picardNumericalMap (cartierPicardHom S.toScheme (-D)) =
    -S.picardNumericalMap (cartierPicardHom S.toScheme D)
  rw [map_neg, map_neg]

/-! ### Nonnegative functionals on the closed cone -/

theorem zero_mem_closedCurveCone : (0 : V S) ∈ closedCurveCone S hreg :=
  subset_closure (Submodule.zero_mem _)

/-- A real linear functional nonnegative on every actual prime-curve class is nonnegative on
the closed cone of curves. -/
theorem nonneg_on_closedCurveCone (L : V S →ₗ[ℝ] ℝ)
    (hL : ∀ C : S.PrimeCurve, 0 ≤ L (curveClassReal S hreg C)) :
    ∀ z ∈ closedCurveCone S hreg, 0 ≤ L z := by
  have hcone : ∀ z ∈ effectiveCone S hreg, 0 ≤ L z := by
    intro z hz
    unfold effectiveCone at hz
    refine Submodule.span_induction (p := fun x _ => 0 ≤ L x) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨C, rfl⟩
      exact hL C
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_nonneg hx hy
    · intro a x _ hx
      rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  have hclosed : IsClosed {z : V S | 0 ≤ L z} :=
    isClosed_le continuous_const L.continuous_of_finiteDimensional
  intro z hz
  exact closure_minimal hcone hclosed hz

/-- The closed cone is stable under nonnegative scaling. -/
theorem smul_mem_closedCurveCone {t : ℝ} (ht : 0 ≤ t) {z : V S}
    (hz : z ∈ closedCurveCone S hreg) : t • z ∈ closedCurveCone S hreg := by
  have hmaps : Set.MapsTo (fun x : V S => t • x) (effectiveCone S hreg : Set (V S))
      (effectiveCone S hreg : Set (V S)) := by
    intro x hx
    have := (effectiveCone S hreg).smul_mem (⟨t, ht⟩ : {c : ℝ // 0 ≤ c}) hx
    rwa [Nonneg.mk_smul] at this
  exact hmaps.closure (continuous_const.smul continuous_id) hz

theorem convex_effectiveCone : Convex ℝ (effectiveCone S hreg : Set (V S)) :=
  (effectiveCone S hreg : ConvexCone ℝ (V S)).convex

theorem convex_closedCurveCone : Convex ℝ (closedCurveCone S hreg) :=
  (convex_effectiveCone S hreg).closure

/-! ### T0: negativity on a curve is negativity on the closed cone -/

/-- **(T0)** An actual Cartier divisor has negative degree on some actual prime curve iff its
real numerical class is negative somewhere on `NE(S)‾`. -/
theorem not_nef_iff_exists_neg (D : CartierDivisor S.toScheme) :
    (∃ C : S.PrimeCurve, C.intersectionNumber D < 0) ↔
      ∃ z ∈ closedCurveCone S hreg, pairReal S hreg (cartierClass S D) z < 0 := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨curveClassReal S hreg C, curveClassReal_mem_closedCurveCone S hreg C, ?_⟩
    rw [pairReal_cartierClass_curveClassReal]
    exact_mod_cast hC
  · rintro ⟨z, hz, hneg⟩
    by_contra h
    push_neg at h
    have h0 := nonneg_on_closedCurveCone S hreg (pairReal S hreg (cartierClass S D))
      (fun C => by
        rw [pairReal_cartierClass_curveClassReal]
        exact_mod_cast h C) z hz
    exact absurd hneg (not_lt.mpr h0)

/-- Nefness of the actual invertible sheaf `O(D)` is nonnegativity of the real class of `D` on
the closed cone of curves. -/
theorem isNef_iff_nonneg_on_closedCurveCone (D : CartierDivisor S.toScheme) :
    Positivity.IsNef S.structureMorphism (cartierDivisorInvertibleSheaf S.toScheme D) ↔
      ∀ z ∈ closedCurveCone S hreg, 0 ≤ pairReal S hreg (cartierClass S D) z := by
  rw [Positivity.isNef_iff_forall_primeCurve]
  constructor
  · intro h
    apply nonneg_on_closedCurveCone S hreg
    intro C
    rw [pairReal_cartierClass_curveClassReal, C.intersectionNumber_eq_restrictionDegree]
    exact_mod_cast h C
  · intro h C
    rw [← C.intersectionNumber_eq_restrictionDegree]
    have := h _ (curveClassReal_mem_closedCurveCone S hreg C)
    rw [pairReal_cartierClass_curveClassReal] at this
    exact_mod_cast this

/-! ### T1: the ample bound -/

omit [IsAlgClosed k] [FiniteDimensional ℚ S.NumericalClassGroup] in
/-- Ample divisors are positive on every actual prime curve. -/
theorem intersectionNumber_pos_of_isAmple (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H)) (C : S.PrimeCurve) :
    0 < C.intersectionNumber H := by
  rw [C.intersectionNumber_eq_restrictionDegree]
  exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple S _ hH C

theorem pairReal_cartierClass_nonneg (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H)) :
    ∀ z ∈ closedCurveCone S hreg, 0 ≤ pairReal S hreg (cartierClass S H) z := by
  apply nonneg_on_closedCurveCone S hreg
  intro C
  rw [pairReal_cartierClass_curveClassReal]
  exact_mod_cast (intersectionNumber_pos_of_isAmple S H hH C).le

omit [FiniteDimensional ℚ S.NumericalClassGroup] in
/-- Serre's global generation: `O(N H - D)` is nef for `N ≫ 0`, so `D · C ≤ N · (H · C)`
uniformly over all actual prime curves. -/
theorem exists_nat_bound_curves (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    (D : CartierDivisor S.toScheme) :
    ∃ N : ℕ, ∀ C : S.PrimeCurve, C.intersectionNumber D ≤ (N : ℤ) * C.intersectionNumber H := by
  obtain ⟨N, hN⟩ := CanonicalAmpleSpan.exists_nef_twist S H (-D) hH
  refine ⟨N, fun C => ?_⟩
  have h := (Positivity.isNef_iff_forall_primeCurve S _).mp hN C
  rw [← C.intersectionNumber_eq_restrictionDegree, ← C.intersectionNumberHom_apply, map_add,
    map_nsmul, map_neg, C.intersectionNumberHom_apply, C.intersectionNumberHom_apply,
    nsmul_eq_mul] at h
  linarith

/-- **(T1, Cartier form)** `D · z ≤ c · (H · z)` on `NE(S)‾` for a constant `c`. -/
theorem pairReal_cartierClass_le (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    (D : CartierDivisor S.toScheme) :
    ∃ c : ℝ, ∀ z ∈ closedCurveCone S hreg,
      pairReal S hreg (cartierClass S D) z ≤ c * pairReal S hreg (cartierClass S H) z := by
  obtain ⟨N, hN⟩ := exists_nat_bound_curves S H hH D
  refine ⟨(N : ℝ), fun z hz => ?_⟩
  have key := nonneg_on_closedCurveCone S hreg
    ((N : ℝ) • pairReal S hreg (cartierClass S H) - pairReal S hreg (cartierClass S D))
    (fun C => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        pairReal_cartierClass_curveClassReal]
      have h' : (C.intersectionNumber D : ℝ) ≤ (N : ℝ) * (C.intersectionNumber H : ℝ) := by
        exact_mod_cast hN C
      linarith) z hz
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at key
  linarith

theorem exists_abs_bound_cartierClass (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    (D : CartierDivisor S.toScheme) :
    ∃ c : ℝ, ∀ z ∈ closedCurveCone S hreg,
      |pairReal S hreg (cartierClass S D) z| ≤ c * pairReal S hreg (cartierClass S H) z := by
  obtain ⟨c₁, h₁⟩ := pairReal_cartierClass_le S hreg H hH D
  obtain ⟨c₂, h₂⟩ := pairReal_cartierClass_le S hreg H hH (-D)
  have hHnn := pairReal_cartierClass_nonneg S hreg H hH
  refine ⟨max c₁ c₂, fun z hz => ?_⟩
  have hz0 := hHnn z hz
  have hneg : pairReal S hreg (cartierClass S (-D)) z = -pairReal S hreg (cartierClass S D) z := by
    rw [cartierClass_neg, pairReal_neg_left]
  have e₁ := h₁ z hz
  have e₂ := h₂ z hz
  rw [hneg] at e₂
  have m₁ : c₁ * pairReal S hreg (cartierClass S H) z ≤
      max c₁ c₂ * pairReal S hreg (cartierClass S H) z :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hz0
  have m₂ : c₂ * pairReal S hreg (cartierClass S H) z ≤
      max c₁ c₂ * pairReal S hreg (cartierClass S H) z :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hz0
  rw [abs_le]
  constructor <;> linarith

omit [IsAlgClosed k] [FiniteDimensional ℚ S.NumericalClassGroup] in
/-- The classes of actual Cartier divisors span `N¹(S)_ℚ`. -/
theorem span_range_cartierClass :
    Submodule.span ℚ (Set.range (cartierClass S)) = ⊤ := by
  apply top_unique
  rintro c -
  obtain ⟨v, rfl⟩ := S.rationalPicardNumericalMap_surjective c
  induction v using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | tmul q p =>
      obtain ⟨D, hD⟩ := cartierPicardHom_surjective S.toScheme p
      have hq : (q ⊗ₜ[ℤ] p : S.RationalPicard) = q • ((1 : ℚ) ⊗ₜ[ℤ] p) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hq, map_smul]
      refine Submodule.smul_mem _ q (Submodule.subset_span ⟨D, ?_⟩)
      change S.picardNumericalMap (cartierPicardHom S.toScheme D) = _
      rw [hD]
      rfl
  | add v w hv hw =>
      rw [map_add]
      exact Submodule.add_mem _ hv hw

/-- **(T1)** For every numerical class `d` there is a constant `c` with
`|d · z| ≤ c · (H · z)` on `NE(S)‾`, `H` ample. -/
theorem exists_abs_bound (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    (d : S.NumericalClassGroup) :
    ∃ c : ℝ, ∀ z ∈ closedCurveCone S hreg,
      |pairReal S hreg d z| ≤ c * pairReal S hreg (cartierClass S H) z := by
  have hd : d ∈ Submodule.span ℚ (Set.range (cartierClass S)) := by
    rw [span_range_cartierClass]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun d _ => ∃ c : ℝ, ∀ z ∈ closedCurveCone S hreg,
      |pairReal S hreg d z| ≤ c * pairReal S hreg (cartierClass S H) z) ?_ ?_ ?_ ?_ hd
  · rintro _ ⟨D, rfl⟩
    exact exists_abs_bound_cartierClass S hreg H hH D
  · exact ⟨0, fun z _ => by simp [pairReal_zero_left]⟩
  · rintro x y _ _ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ + c₂, fun z hz => ?_⟩
    rw [pairReal_add_left]
    have e₁ := abs_le.mp (h₁ z hz)
    have e₂ := abs_le.mp (h₂ z hz)
    rw [abs_le]
    constructor <;> nlinarith [e₁.1, e₁.2, e₂.1, e₂.2]
  · rintro a x _ ⟨c, hc⟩
    refine ⟨|(a : ℝ)| * c, fun z hz => ?_⟩
    rw [pairReal_smul_left, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hc z hz) (abs_nonneg _)

/-! ### The Gram matrix of the intersection form -/

/-- The rational Gram matrix of the intersection form in the fixed basis. -/
def gram : Matrix (Fin (Module.finrank ℚ S.NumericalClassGroup))
    (Fin (Module.finrank ℚ S.NumericalClassGroup)) ℚ :=
  BilinForm.toMatrix (basis S) (S.numericalIntersectionBilinForm hreg)

theorem gram_apply (i j : Fin (Module.finrank ℚ S.NumericalClassGroup)) :
    gram S hreg i j = S.numericalIntersectionBilinForm hreg (basis S i) (basis S j) :=
  BilinForm.toMatrix_apply _ _ _ _

theorem gram_det_ne_zero : (gram S hreg).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (basis S)).mp
    (S.numericalIntersectionBilinForm_nondegenerate hreg)

/-- The real Gram matrix. -/
def gramReal : Matrix (Fin (Module.finrank ℚ S.NumericalClassGroup))
    (Fin (Module.finrank ℚ S.NumericalClassGroup)) ℝ :=
  (Rat.castHom ℝ).mapMatrix (gram S hreg)

theorem gramReal_apply (i j : Fin (Module.finrank ℚ S.NumericalClassGroup)) :
    gramReal S hreg i j = (gram S hreg i j : ℝ) := rfl

theorem gramReal_det_ne_zero : (gramReal S hreg).det ≠ 0 := by
  unfold gramReal
  rw [← RingHom.map_det, Rat.coe_castHom]
  exact_mod_cast gram_det_ne_zero S hreg

theorem pairReal_basis_eq_mulVec (z : V S) (i : Fin (Module.finrank ℚ S.NumericalClassGroup)) :
    pairReal S hreg (basis S i) z = (gramReal S hreg).mulVec z i := by
  change ∑ j, z j * (S.numericalIntersectionBilinForm hreg (basis S i) (basis S j) : ℝ) =
    ∑ j, gramReal S hreg i j * z j
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gramReal_apply, gram_apply, mul_comm]

/-- A real vector orthogonal to every basis class vanishes (nondegeneracy over `ℚ` transports
to `ℝ` through the invertible Gram matrix). -/
theorem eq_zero_of_forall_pairReal_basis (z : V S)
    (h : ∀ i, pairReal S hreg (basis S i) z = 0) : z = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero (gramReal_det_ne_zero S hreg)
  funext i
  rw [← pairReal_basis_eq_mulVec, h i]
  rfl

theorem eq_zero_of_forall_pairReal (z : V S) (h : ∀ d, pairReal S hreg d z = 0) : z = 0 :=
  eq_zero_of_forall_pairReal_basis S hreg z fun _ => h _

/-! ### T2, T3: Kleiman positivity and pointedness -/

/-- **(T2, Kleiman)** An ample Cartier divisor is strictly positive on every nonzero element of
the closed cone of curves. -/
theorem pairReal_ample_pos (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    (z : V S) (hz : z ∈ closedCurveCone S hreg) (hz0 : z ≠ 0) :
    0 < pairReal S hreg (cartierClass S H) z := by
  rcases (pairReal_cartierClass_nonneg S hreg H hH z hz).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hz0
    apply eq_zero_of_forall_pairReal S hreg z
    intro d
    obtain ⟨c, hc⟩ := exists_abs_bound S hreg H hH d
    have := hc z hz
    rw [← heq, mul_zero] at this
    exact abs_nonpos_iff.mp this

/-- **(T3)** `NE(S)‾ ∩ -NE(S)‾ = {0}`. -/
theorem eq_zero_of_mem_of_neg_mem (z : V S) (hz : z ∈ closedCurveCone S hreg)
    (hz' : -z ∈ closedCurveCone S hreg) : z = 0 := by
  obtain ⟨H, hH⟩ := S.exists_isAmple_cartier
  by_contra h0
  have h1 := pairReal_ample_pos S hreg H hH z hz h0
  have h2 := pairReal_ample_pos S hreg H hH (-z) hz' (neg_ne_zero.mpr h0)
  rw [map_neg] at h2
  linarith

theorem closedCurveCone_inter_neg :
    closedCurveCone S hreg ∩ (-closedCurveCone S hreg) = {0} := by
  ext z
  constructor
  · rintro ⟨hz, hz'⟩
    exact eq_zero_of_mem_of_neg_mem S hreg z hz (Set.mem_neg.mp hz')
  · rintro rfl
    exact ⟨zero_mem_closedCurveCone S hreg, by
      rw [Set.mem_neg, neg_zero]
      exact zero_mem_closedCurveCone S hreg⟩

/-! ### T4: the compact ample slice -/

/-- The ample slice `{z ∈ NE(S)‾ | H · z = 1}`. -/
def ampleSlice (H : CartierDivisor S.toScheme) : Set (V S) :=
  {z | z ∈ closedCurveCone S hreg ∧ pairReal S hreg (cartierClass S H) z = 1}

theorem mem_ampleSlice (H : CartierDivisor S.toScheme) (z : V S) :
    z ∈ ampleSlice S hreg H ↔
      z ∈ closedCurveCone S hreg ∧ pairReal S hreg (cartierClass S H) z = 1 := Iff.rfl

theorem ampleSlice_subset (H : CartierDivisor S.toScheme) :
    ampleSlice S hreg H ⊆ closedCurveCone S hreg := fun _ hz => hz.1

theorem isClosed_ampleSlice (H : CartierDivisor S.toScheme) : IsClosed (ampleSlice S hreg H) :=
  (isClosed_closedCurveCone S hreg).inter
    (isClosed_eq (pairReal S hreg (cartierClass S H)).continuous_of_finiteDimensional
      continuous_const)

theorem convex_ampleSlice (H : CartierDivisor S.toScheme) : Convex ℝ (ampleSlice S hreg H) :=
  (convex_closedCurveCone S hreg).inter
    ((convex_singleton (1 : ℝ)).linear_preimage (pairReal S hreg (cartierClass S H)))

/-- Normalizing a nonzero element of the closed cone by its ample degree lands in the slice. -/
theorem inv_smul_mem_ampleSlice (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    {z : V S} (hz : z ∈ closedCurveCone S hreg) (hz0 : z ≠ 0) :
    (pairReal S hreg (cartierClass S H) z)⁻¹ • z ∈ ampleSlice S hreg H := by
  have hpos := pairReal_ample_pos S hreg H hH z hz hz0
  refine ⟨smul_mem_closedCurveCone S hreg (inv_nonneg.mpr hpos.le) hz, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hpos.ne']

/-- The linear map `z ↦ (b_i · z)_i` (multiplication by the real Gram matrix). -/
def gramMap : V S →ₗ[ℝ] V S := LinearMap.pi fun i => pairReal S hreg (basis S i)

theorem gramMap_apply (z : V S) (i : Fin (Module.finrank ℚ S.NumericalClassGroup)) :
    gramMap S hreg z i = pairReal S hreg (basis S i) z :=
  LinearMap.pi_apply _ _ _

theorem gramMap_injective : Function.Injective (gramMap S hreg) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  apply eq_zero_of_forall_pairReal_basis S hreg z
  intro i
  rw [← gramMap_apply, hz]
  rfl

/-- The Gram map as a linear automorphism of `V S`. -/
def gramEquiv : V S ≃ₗ[ℝ] V S :=
  LinearEquiv.ofInjectiveEndo (gramMap S hreg) (gramMap_injective S hreg)

theorem gramEquiv_apply (z : V S) (i : Fin (Module.finrank ℚ S.NumericalClassGroup)) :
    gramEquiv S hreg z i = pairReal S hreg (basis S i) z :=
  gramMap_apply S hreg z i

theorem isBounded_ampleSlice (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H)) :
    Bornology.IsBounded (ampleSlice S hreg H) := by
  have hb : ∀ i, ∃ c : ℝ, ∀ z ∈ ampleSlice S hreg H, |pairReal S hreg (basis S i) z| ≤ c := by
    intro i
    obtain ⟨c, hc⟩ := exists_abs_bound S hreg H hH (basis S i)
    refine ⟨c, fun z hz => ?_⟩
    have := hc z hz.1
    rw [hz.2, mul_one] at this
    exact this
  choose c hc using hb
  let e := (gramEquiv S hreg).toContinuousLinearEquiv
  have hR : (0 : ℝ) ≤ ∑ j, |c j| := Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  have hbox : Bornology.IsBounded (Metric.closedBall (0 : V S) (∑ j, |c j|)) :=
    Metric.isBounded_closedBall
  have hsub : ampleSlice S hreg H ⊆ e.symm '' Metric.closedBall (0 : V S) (∑ j, |c j|) := by
    intro z hz
    refine ⟨e z, ?_, e.symm_apply_apply z⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro i
    rw [Real.norm_eq_abs]
    have hei : e z i = pairReal S hreg (basis S i) z := gramEquiv_apply S hreg z i
    rw [hei]
    calc |pairReal S hreg (basis S i) z| ≤ c i := hc i z hz
      _ ≤ |c i| := le_abs_self _
      _ ≤ ∑ j, |c j| := Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)
  exact (e.symm.lipschitz.isBounded_image hbox).subset hsub

/-- **(T4)** The ample slice of the closed cone of curves is compact. -/
theorem isCompact_ampleSlice (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H)) :
    IsCompact (ampleSlice S hreg H) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_ampleSlice S hreg H)
    (isBounded_ampleSlice S hreg H hH)

/-! ### T5: negative extremal rays -/

/-- An extreme point of the ample slice spans an extremal ray of the closed cone. -/
theorem isExtremalRay_of_mem_extremePoints (H : CartierDivisor S.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme H))
    (v : V S) (hv : v ∈ (ampleSlice S hreg H).extremePoints ℝ) :
    IsExtremalRay S (closedCurveCone S hreg) v := by
  have hvT : v ∈ ampleSlice S hreg H := hv.1
  have hvK : v ∈ closedCurveCone S hreg := hvT.1
  have hv1 : pairReal S hreg (cartierClass S H) v = 1 := hvT.2
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv1
    exact zero_ne_one hv1
  refine ⟨hv0, hvK, ?_⟩
  intro x y hx hy hxy
  obtain ⟨t, ht, hxy⟩ := hxy
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨⟨0, le_rfl, (zero_smul ℝ v).symm⟩, ⟨t, ht, ?_⟩⟩
    rwa [zero_add] at hxy
  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨⟨t, ht, ?_⟩, ⟨0, le_rfl, (zero_smul ℝ v).symm⟩⟩
    rwa [add_zero] at hxy
  have hxp := pairReal_ample_pos S hreg H hH x hx hx0
  have hyp := pairReal_ample_pos S hreg H hH y hy hy0
  have hab : pairReal S hreg (cartierClass S H) x + pairReal S hreg (cartierClass S H) y = t := by
    have := congrArg (pairReal S hreg (cartierClass S H)) hxy
    rw [map_add, map_smul, smul_eq_mul, hv1, mul_one] at this
    exact this
  have htpos : 0 < t := by
    rw [← hab]
    exact add_pos hxp hyp
  have hx'T := inv_smul_mem_ampleSlice S hreg H hH hx hx0
  have hy'T := inv_smul_mem_ampleSlice S hreg H hH hy hy0
  have hseg : v ∈ openSegment ℝ ((pairReal S hreg (cartierClass S H) x)⁻¹ • x)
      ((pairReal S hreg (cartierClass S H) y)⁻¹ • y) := by
    refine ⟨pairReal S hreg (cartierClass S H) x / t, pairReal S hreg (cartierClass S H) y / t,
      div_pos hxp htpos, div_pos hyp htpos, ?_, ?_⟩
    · rw [← add_div, hab, div_self htpos.ne']
    · have h1 : pairReal S hreg (cartierClass S H) x / t *
          (pairReal S hreg (cartierClass S H) x)⁻¹ = t⁻¹ := by
        rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hxp.ne', one_mul]
      have h2 : pairReal S hreg (cartierClass S H) y / t *
          (pairReal S hreg (cartierClass S H) y)⁻¹ = t⁻¹ := by
        rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hyp.ne', one_mul]
      rw [smul_smul, smul_smul, h1, h2, ← smul_add, hxy, smul_smul, inv_mul_cancel₀ htpos.ne',
        one_smul]
  obtain ⟨hx', hy'⟩ := (mem_extremePoints.mp hv).2 _ hx'T _ hy'T hseg
  refine ⟨⟨pairReal S hreg (cartierClass S H) x, hxp.le, ?_⟩,
    ⟨pairReal S hreg (cartierClass S H) y, hyp.le, ?_⟩⟩
  · rw [← hx', smul_smul, mul_inv_cancel₀ hxp.ne', one_smul]
  · rw [← hy', smul_smul, mul_inv_cancel₀ hyp.ne', one_smul]

/-- **(T5)** A numerical class that is negative somewhere on `NE(S)‾` is negative on an
extremal ray of `NE(S)‾`. -/
theorem exists_extremalRay_of_neg (d : S.NumericalClassGroup)
    (hd : ∃ z ∈ closedCurveCone S hreg, pairReal S hreg d z < 0) :
    ∃ v, IsExtremalRay S (closedCurveCone S hreg) v ∧ pairReal S hreg d v < 0 := by
  obtain ⟨H, hH⟩ := S.exists_isAmple_cartier
  obtain ⟨z, hz, hdz⟩ := hd
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hdz
    exact lt_irrefl _ hdz
  have hpos := pairReal_ample_pos S hreg H hH z hz hz0
  have hzT := inv_smul_mem_ampleSlice S hreg H hH hz hz0
  have hzneg : pairReal S hreg d ((pairReal S hreg (cartierClass S H) z)⁻¹ • z) < 0 := by
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hpos) hdz
  have hKM := closure_convexHull_extremePoints (isCompact_ampleSlice S hreg H hH)
    (convex_ampleSlice S hreg H)
  have hex : ∃ v ∈ (ampleSlice S hreg H).extremePoints ℝ, pairReal S hreg d v < 0 := by
    by_contra hcon
    push_neg at hcon
    have hconv : Convex ℝ {x : V S | 0 ≤ pairReal S hreg d x} :=
      (convex_Ici (0 : ℝ)).linear_preimage (pairReal S hreg d)
    have hcl : IsClosed {x : V S | 0 ≤ pairReal S hreg d x} :=
      isClosed_le continuous_const (pairReal S hreg d).continuous_of_finiteDimensional
    have hsub : closure (convexHull ℝ ((ampleSlice S hreg H).extremePoints ℝ)) ⊆
        {x : V S | 0 ≤ pairReal S hreg d x} :=
      closure_minimal (convexHull_min (fun v hv => hcon v hv) hconv) hcl
    rw [hKM] at hsub
    exact absurd hzneg (not_lt.mpr (hsub hzT))
  obtain ⟨v, hv, hvneg⟩ := hex
  exact ⟨v, isExtremalRay_of_mem_extremePoints S hreg H hH v hv, hvneg⟩

/-- **(T5, `NegativeOn` form)** -/
theorem exists_extremalRay_negativeOn (d : S.NumericalClassGroup)
    (hd : ∃ z ∈ closedCurveCone S hreg, NegativeOn S hreg d z) :
    ∃ v, IsExtremalRay S (closedCurveCone S hreg) v ∧ NegativeOn S hreg d v :=
  exists_extremalRay_of_neg S hreg d hd

/-- **(T5, Cartier form)** A Cartier divisor with a curve of negative degree is negative on an
extremal ray of `NE(S)‾`. -/
theorem exists_extremalRay_of_intersectionNumber_neg (D : CartierDivisor S.toScheme)
    (hD : ∃ C : S.PrimeCurve, C.intersectionNumber D < 0) :
    ∃ v, IsExtremalRay S (closedCurveCone S hreg) v ∧
      pairReal S hreg (cartierClass S D) v < 0 :=
  exists_extremalRay_of_neg S hreg (cartierClass S D)
    ((not_nef_iff_exists_neg S hreg D).mp hD)

end KltDP.Geometry.CurveCone

#print axioms KltDP.Geometry.CurveCone.not_nef_iff_exists_neg
#print axioms KltDP.Geometry.CurveCone.exists_abs_bound
#print axioms KltDP.Geometry.CurveCone.pairReal_ample_pos
#print axioms KltDP.Geometry.CurveCone.eq_zero_of_mem_of_neg_mem
#print axioms KltDP.Geometry.CurveCone.isCompact_ampleSlice
#print axioms KltDP.Geometry.CurveCone.exists_extremalRay_of_neg
