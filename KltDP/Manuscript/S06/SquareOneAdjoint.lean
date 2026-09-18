import KltDP.Manuscript.S02.ExteriorNullCurves
import KltDP.Manuscript.S05.ZeroAdjoint
import KltDP.Geometry.SurfaceRiemannRochProved
import KltDP.Geometry.NefIntersectionSectionVanishing
import KltDP.Geometry.KltResolutionPicardCohomologyInvariants
import KltDP.Geometry.NullCurveIntersectionMatrix
import KltDP.Geometry.NullCurveNumericalSpan

/-!
# Manuscript Lemma 6.1: the effective adjoint remainder of a square-one configuration

Source: `source/manuscript.tex`, lines 1569–1638, label `lem:square-one-adjoint`.

For the resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface and an exterior
`(-1)`-curve `P`, the three square-one configurations are

* (U1) `A = W + P` with `W ⊂ D` of weight two and `P · W = 2`;
* (U2) `A = U + V + P` with `U, V ⊂ D` adjacent of weight two and `P · U = P · V = 1`;
* (U3) `A = B + 2P` with `B ⊂ D` of weight three and `P · B = 2`.

In each case `A² = 1`, `K_S · A = -1`, `A` is nef, and Riemann–Roch (`χ(K_S + A) = 1`,
`h⁰(-A) = 0`) gives an effective `Z ∼ K_S + A`; solving the supported coefficients gives
`Z = ε P + N` with `ε = 0, 0, 1`, and `N` is the *effective adjoint remainder*:
`N ≥ 0`, `K_S + A ∼ ε P + N` in `Pic S`, `L · N = L · P - L²`, every component of `N` is
`A`-null and outside `Supp A`, every exterior `A`-null curve outside `Supp A` occurs in `N`
with positive coefficient, and `N = 0` iff there is no such curve (negative definiteness of
the exceptional lattice).

Weil divisors are `Finsupp`s on prime curves (`R.S.WeilDivisor`); their numerical classes are
computed through `numW`; linear equivalence is the actual relation `R.S.LinearlyEquivalent`,
and the Picard identities are stated in `Pic S` with `R.curvePic` and
`R.S.regularWeilPicardClass`. Everything is derived from the compiled union and the delivered
modules; the only characteristic hypothesis is `0 < p` (for `χ(𝒪_S) = 1`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S05

universe u

namespace KltDP.Manuscript.S06

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

local notation "𝒞" => DisjointNegativeCurvesRank.curveClass R.S R.hreg
local notation "𝔅" => R.S.numericalIntersectionBilinForm R.hreg

/-! ### Numerical classes of integral Weil divisors -/

/-- The numerical class in `N¹(S)_ℚ` of an integral Weil divisor. -/
def numW (Z : R.S.WeilDivisor) : R.S.NumericalClassGroup :=
  R.S.rationalWeilNumericalMap R.hreg (rationalizeWeilDivisor R.S Z)

theorem numW_add (Z Z' : R.S.WeilDivisor) : numW R (Z + Z') = numW R Z + numW R Z' := by
  simp only [numW, map_add]

theorem numW_sub (Z Z' : R.S.WeilDivisor) : numW R (Z - Z') = numW R Z - numW R Z' := by
  simp only [numW, map_sub]

theorem numW_zero : numW R 0 = 0 := by
  simp only [numW, map_zero]

theorem numW_single (C : R.S.PrimeCurve) (a : ℤ) :
    numW R (Finsupp.single C a) = (a : ℚ) • 𝒞 C := by
  unfold numW
  rw [rationalizeWeilDivisor_single, ← Finsupp.smul_single_one, map_smul,
    R.rationalWeilNumericalMap_single]

/-- The numerical class of the canonical Weil divisor `K_S` is `[K_S]`. -/
theorem numW_KS : numW R (R.S.cartierToWeilHom R.KS) = R.Knum :=
  R.rationalWeilNumericalMap_rationalCartier R.KS

/-- The Cartier class of the Cartier representative of a Weil divisor is its numerical class. -/
theorem cartierClass_symm (Z : R.S.WeilDivisor) :
    NefNullCurveNegativeSquare.cartierClass R.S ((R.S.regularCartierWeilEquiv R.hreg).symm Z) =
      numW R Z := by
  rw [← R.rationalWeilNumericalMap_rationalCartier]
  unfold numW
  congr 1
  change rationalizeWeilDivisor R.S (R.S.cartierToWeilHom _) = _
  have hmap : R.S.cartierToWeilHom ((R.S.regularCartierWeilEquiv R.hreg).symm Z) = Z :=
    (R.S.regularCartierWeilEquiv R.hreg).apply_symm_apply Z
  rw [hmap]

/-- The intersection pairing of the Cartier representatives is the numerical pairing. -/
theorem pairing_symm_symm (Z Z' : R.S.WeilDivisor) :
    (R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm Z)
      ((R.S.regularCartierWeilEquiv R.hreg).symm Z') : ℚ) = 𝔅 (numW R Z) (numW R Z') := by
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing, cartierClass_symm, cartierClass_symm]

/-- The Cartier representative of a prime curve is its prime Cartier divisor. -/
theorem symm_single (C : R.S.PrimeCurve) :
    (R.S.regularCartierWeilEquiv R.hreg).symm (Finsupp.single C 1) =
      R.S.primeCurveCartier R.hreg C := by
  rw [← R.S.cartierToWeilHom_primeCurveCartier R.hreg C]
  exact (R.S.regularCartierWeilEquiv R.hreg).symm_apply_apply _

theorem numW_eq_sum (Z : R.S.WeilDivisor) : numW R Z = Z.sum (fun C a => (a : ℚ) • 𝒞 C) := by
  induction Z using Finsupp.induction_linear with
  | zero => rw [numW_zero, Finsupp.sum_zero_index]
  | add f g hf hg =>
    rw [numW_add, hf, hg, Finsupp.sum_add_index' (fun _ => by rw [Int.cast_zero, zero_smul])
      (fun _ _ _ => by rw [Int.cast_add, add_smul])]
  | single C a => rw [numW_single, Finsupp.sum_single_index (by rw [Int.cast_zero, zero_smul])]

theorem pairing_numW_right (c : R.S.NumericalClassGroup) (Z : R.S.WeilDivisor) :
    𝔅 c (numW R Z) = Z.sum (fun C a => (a : ℚ) * 𝔅 c (𝒞 C)) := by
  rw [numW_eq_sum]
  unfold Finsupp.sum
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem pairing_numW_left (Z : R.S.WeilDivisor) (c : R.S.NumericalClassGroup) :
    𝔅 (numW R Z) c = Z.sum (fun C a => (a : ℚ) * 𝔅 (𝒞 C) c) := by
  rw [numW_eq_sum]
  unfold Finsupp.sum
  rw [LinearMap.BilinForm.sum_left]
  simp only [LinearMap.BilinForm.smul_left, smul_eq_mul]

/-! ### Pairings -/

theorem deg_eq_pairing (C : R.S.PrimeCurve) (c : R.S.NumericalClassGroup) :
    R.S.numericalRestrictionDegree C c = 𝔅 c (𝒞 C) :=
  (DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg c C).symm

theorem pairing_symm (x y : R.S.NumericalClassGroup) : 𝔅 x y = 𝔅 y x :=
  (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq x y

/-- Distinct prime curves pair nonnegatively. -/
theorem pairing_nonneg_of_ne (C E : R.S.PrimeCurve) (h : C ≠ E) : 0 ≤ 𝔅 (𝒞 C) (𝒞 E) := by
  rw [DisjointNegativeCurvesRank.curveClass_pairing]
  exact_mod_cast PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg C E h

theorem pairing_vertex_self (i : R.Vertices) : 𝔅 (𝒞 i.val) (𝒞 i.val) = -R.w i := by
  rw [curveClass_pairing_vertices R i i, M_diag R i]

theorem pairing_vertices (i j : R.Vertices) : 𝔅 (𝒞 i.val) (𝒞 j.val) = R.M i j :=
  curveClass_pairing_vertices R i j

theorem pairing_contact (P : R.S.PrimeCurve) (i : R.Vertices) :
    𝔅 (𝒞 P) (𝒞 i.val) = (R.contact P i : ℚ) :=
  curveClass_pairing_contact R P i

theorem pairing_minusOne_self (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    𝔅 (𝒞 P) (𝒞 P) = -1 := by
  rw [curveClass_self_pairing R P, hP.selfIntersection]
  norm_num

theorem Knum_pairing (C : R.S.PrimeCurve) : 𝔅 R.Knum (𝒞 C) = (R.Kdeg C : ℚ) :=
  NullCurveNumericalSpan.cartierClass_curveClass R.S R.hreg R.KS C

theorem Knum_pairing_vertex (i : R.Vertices) : 𝔅 R.Knum (𝒞 i.val) = R.w i - 2 :=
  R.Knum_pairing_curveClass i

theorem Knum_pairing_minusOne (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    𝔅 R.Knum (𝒞 P) = -1 := by
  rw [Knum_pairing, Kdeg_eq_neg_one_of_isMinusOne R P hP]
  norm_num

theorem Lnum_pairing (C : R.S.PrimeCurve) : 𝔅 R.Lnum (𝒞 C) = R.Ldeg C :=
  Lnum_pairing_curveClass R C

theorem Lnum_pairing_Knum : 𝔅 R.Lnum R.Knum = -R.Lsq := by
  rw [pairing_symm, R.Knum_pairing_Lnum]

/-- Adjacent exceptional curves meet with intersection number exactly one (klt forest). -/
theorem M_eq_one_of_adj {i j : R.Vertices} (h : R.graph.Adj i j) : R.M i j = 1 := by
  have hne : i ≠ j := R.graph.ne_of_adj h
  have hle := (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.2 i j hne
  have hM : R.M i j = (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) : ℚ) := rfl
  have hne0 : R.M i j ≠ 0 := fun h0 => not_adj_of_M_eq_zero R hne h0 h
  have hnn := R.M_offDiag_nonneg i j hne
  rw [hM] at hne0 hnn ⊢
  have h1 : (0 : ℤ) ≤ R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) := by exact_mod_cast hnn
  have h2 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) ≠ 0 := by exact_mod_cast hne0
  have h3 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) = 1 := by omega
  rw [h3]
  norm_num

/-! ### The Riemann–Roch input -/

/-- The canonical Weil divisor `K_S` satisfies the source's canonical condition. -/
theorem isCanonical_KS :
    SurfaceRiemannRochSource.IsCanonical R.S R.hreg (R.S.cartierToWeilHom R.KS) := by
  have hK : (R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS) = R.KS :=
    (R.S.regularCartierWeilEquiv R.hreg).symm_apply_apply R.KS
  change Nonempty (cartierDivisorModule R.S.toScheme
    ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS)) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior R.S.structureMorphism 2)
  rw [hK]
  exact ⟨R.eKS⟩

/-- `p_a(S) = χ(𝒪_S) - 1 = 0` (the resolution is rational). -/
theorem arithmeticGenus_eq_zero (p : ℕ) [CharP k p] (hp : 0 < p) :
    SurfaceRiemannRochSource.arithmeticGenus R.S = 0 := by
  have h := (R.hmin.picard_and_structure_invariants_of_kltDelPezzo R.hDP R.hrank p hp).2.2.1
  unfold SurfaceRiemannRochSource.arithmeticGenus
  rw [h]
  norm_num

/-- `χ(K_S + A) = 1 + ½ (K_S + A) · A = 1` for `A² = 1`, `K_S · A = -1`. -/
theorem rrNumber_adjoint (p : ℕ) [CharP k p] (hp : 0 < p) (A : R.S.WeilDivisor)
    (hA2 : 𝔅 (numW R A) (numW R A) = 1) (hKA : 𝔅 R.Knum (numW R A) = -1) :
    SurfaceRiemannRochSource.rrNumber R.S R.hreg (R.S.cartierToWeilHom R.KS + A)
      (R.S.cartierToWeilHom R.KS) = 1 := by
  unfold SurfaceRiemannRochSource.rrNumber
  rw [arithmeticGenus_eq_zero R p hp, add_sub_cancel_left]
  have h := pairing_symm_symm R (R.S.cartierToWeilHom R.KS + A) A
  rw [numW_add, numW_KS, LinearMap.BilinForm.add_left, hKA, hA2] at h
  rw [h]
  norm_num

/-- A Weil divisor of nonnegative numerical degree on every curve has a nef Cartier
representative. -/
theorem isNef_symm (A : R.S.WeilDivisor)
    (hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C (numW R A)) :
    Positivity.IsNef R.S.structureMorphism
      (cartierDivisorInvertibleSheaf R.S.toScheme ((R.S.regularCartierWeilEquiv R.hreg).symm A)) := by
  rw [R.S.isNef_iff_pairing R.hreg]
  intro C
  have h := pairing_symm_symm R A (Finsupp.single C 1)
  rw [numW_single, Int.cast_one, one_smul, ← deg_eq_pairing, symm_single] at h
  have := hnef C
  rw [← h] at this
  exact_mod_cast this

/-- **Riemann–Roch for the adjoint** (manuscript lines 1590–1598): for a nef `A` with `A² = 1`
and `K_S · A = -1` there is an effective `Z ∼ K_S + A`. -/
theorem exists_effective_adjoint (p : ℕ) [CharP k p] (hp : 0 < p) (A : R.S.WeilDivisor)
    (hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C (numW R A))
    (hA2 : 𝔅 (numW R A) (numW R A) = 1) (hKA : 𝔅 R.Knum (numW R A) = -1) :
    ∃ Z : R.S.WeilDivisor, EffectiveDivisor Z ∧
      R.S.LinearlyEquivalent Z (R.S.cartierToWeilHom R.KS + A) := by
  refine SurfaceRiemannRochProved.exists_effectiveWeil R.S R.hreg _ _ (isCanonical_KS R) ?_ ?_
  · set D : R.S.WeilDivisor :=
      R.S.cartierToWeilHom R.KS - (R.S.cartierToWeilHom R.KS + A) with hD
    have hnumD : numW R D = -numW R A := by
      rw [hD, numW_sub, numW_add, sub_add_cancel_left]
    have h := pairing_symm_symm R D A
    rw [hnumD, LinearMap.BilinForm.neg_left, hA2] at h
    have hneg : R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm D)
        ((R.S.regularCartierWeilEquiv R.hreg).symm A) < 0 := by
      have h' : (R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm D)
          ((R.S.regularCartierWeilEquiv R.hreg).symm A) : ℚ) < 0 := by
        rw [h]
        norm_num
      exact_mod_cast h'
    exact NefIntersectionSectionVanishing.sections_subsingleton R.S R.hreg D _
      (isNef_symm R A hnef) hneg
  · rw [rrNumber_adjoint R p hp A hA2 hKA]
    norm_num

/-! ### Linear equivalence, numerical classes and Picard classes -/

theorem numW_eq_of_linearlyEquivalent {Z Z' : R.S.WeilDivisor}
    (h : R.S.LinearlyEquivalent Z Z') : numW R Z = numW R Z' := by
  have hp := (R.S.regularWeilPicardClass_eq_iff R.hreg Z Z').mpr h
  have h2 := congrArg (fun c => R.S.picardNumericalMap (Additive.ofMul c)) hp
  simp only [R.S.picardNumericalMap_regularWeilPicardClass R.hreg] at h2
  exact h2

theorem picardClass_eq_of_linearlyEquivalent {Z Z' : R.S.WeilDivisor}
    (h : R.S.LinearlyEquivalent Z Z') :
    R.S.regularWeilPicardClass R.hreg Z = R.S.regularWeilPicardClass R.hreg Z' :=
  (R.S.regularWeilPicardClass_eq_iff R.hreg Z Z').mpr h

theorem picardClass_single (C : R.S.PrimeCurve) :
    R.S.regularWeilPicardClass R.hreg (Finsupp.single C 1) = R.curvePic C := by
  rw [← R.S.cartierToWeilHom_primeCurveCartier R.hreg C]
  exact R.S.regularWeilClassPicardEquiv_of_cartier R.hreg _

theorem picardClass_KS :
    R.S.regularWeilPicardClass R.hreg (R.S.cartierToWeilHom R.KS) =
      cartierPicardClass R.S.toScheme R.KS :=
  R.S.regularWeilClassPicardEquiv_of_cartier R.hreg R.KS

/-! ### Components of effective divisors -/

/-- Every component of an effective `Z` with `A · Z = 0` is `A`-null, for a nef class `A`. -/
theorem deg_eq_zero_of_mem_support (a : R.S.NumericalClassGroup) (Z : R.S.WeilDivisor)
    (hZ : EffectiveDivisor Z) (hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C a)
    (hAZ : 𝔅 a (numW R Z) = 0) (C : R.S.PrimeCurve) (hC : C ∈ Z.support) :
    R.S.numericalRestrictionDegree C a = 0 := by
  rw [pairing_numW_right] at hAZ
  unfold Finsupp.sum at hAZ
  have hnn : ∀ E ∈ Z.support, 0 ≤ (Z E : ℚ) * 𝔅 a (𝒞 E) := fun E _ =>
    mul_nonneg (by exact_mod_cast hZ E) (by rw [← deg_eq_pairing]; exact hnef E)
  have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hAZ C hC
  have hZC : (Z C : ℚ) ≠ 0 := by exact_mod_cast Finsupp.mem_support_iff.mp hC
  rw [deg_eq_pairing]
  exact (mul_eq_zero.mp h).resolve_left hZC

/-- A prime curve outside the support of an effective `A` which is `A`-null is disjoint from
every component of `A`. -/
theorem pairing_eq_zero_of_deg_eq_zero (A : R.S.WeilDivisor) (hA : EffectiveDivisor A)
    (C : R.S.PrimeCurve) (hC : C ∉ A.support)
    (hnull : R.S.numericalRestrictionDegree C (numW R A) = 0)
    (E : R.S.PrimeCurve) (hE : E ∈ A.support) : 𝔅 (𝒞 E) (𝒞 C) = 0 := by
  rw [deg_eq_pairing, pairing_numW_left] at hnull
  unfold Finsupp.sum at hnull
  have hnn : ∀ F ∈ A.support, 0 ≤ (A F : ℚ) * 𝔅 (𝒞 F) (𝒞 C) := fun F hF =>
    mul_nonneg (by exact_mod_cast hA F) (pairing_nonneg_of_ne R F C (fun h => hC (h ▸ hF)))
  have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnull E hE
  have hAE : (A E : ℚ) ≠ 0 := by exact_mod_cast Finsupp.mem_support_iff.mp hE
  exact (mul_eq_zero.mp h).resolve_left hAE

/-- For effective `N`, `N · Q ≥ N_Q · Q²`. -/
theorem sum_pairing_ge (N : R.S.WeilDivisor) (hN : EffectiveDivisor N) (Q : R.S.PrimeCurve) :
    (N Q : ℚ) * 𝔅 (𝒞 Q) (𝒞 Q) ≤ N.sum (fun C a => (a : ℚ) * 𝔅 (𝒞 C) (𝒞 Q)) := by
  classical
  unfold Finsupp.sum
  by_cases hQ : Q ∈ N.support
  · rw [← Finset.add_sum_erase _ _ hQ]
    dsimp only
    have : 0 ≤ ∑ C ∈ N.support.erase Q, (N C : ℚ) * 𝔅 (𝒞 C) (𝒞 Q) :=
      Finset.sum_nonneg (fun C hC => mul_nonneg (by exact_mod_cast hN C)
        (pairing_nonneg_of_ne R C Q (Finset.ne_of_mem_erase hC)))
    linarith
  · rw [Finsupp.not_mem_support_iff.mp hQ, Int.cast_zero, zero_mul]
    exact Finset.sum_nonneg (fun C hC => mul_nonneg (by exact_mod_cast hN C)
      (pairing_nonneg_of_ne R C Q (fun h => hQ (h ▸ hC))))

/-- **Negative definiteness of the exceptional lattice**: an effective divisor supported on
exceptional curves whose components all have nonnegative degree on it is zero. -/
theorem eq_zero_of_exceptional_support (N : R.S.WeilDivisor) (hN : EffectiveDivisor N)
    (hexc : ∀ C ∈ N.support, IsExceptionalCurve R.π C)
    (hdeg : ∀ C ∈ N.support, 0 ≤ 𝔅 (𝒞 C) (numW R N)) : N = 0 := by
  classical
  let n : R.Vertices → ℚ := fun i => (N i.val : ℚ)
  have hsum : numW R N = ∑ i : R.Vertices, n i • 𝒞 i.val := by
    rw [numW_eq_sum]
    unfold Finsupp.sum
    have hsub : N.support ⊆ Finset.univ.map
        (⟨Subtype.val, Subtype.val_injective⟩ : R.Vertices ↪ R.S.PrimeCurve) := by
      intro C hC
      exact Finset.mem_map.mpr ⟨⟨C, hexc C hC⟩, Finset.mem_univ _, rfl⟩
    rw [Finset.sum_subset hsub (fun C _ hC => by
      simp [Finsupp.not_mem_support_iff.mp hC]), Finset.sum_map]
    rfl
  have hsq : 𝔅 (numW R N) (numW R N) = -(n ⬝ᵥ (R.A *ᵥ n)) := by
    have hq := NullCurveIntersectionMatrix.quadraticForm_eq R.S R.hreg
      (fun i : R.Vertices => i.val) n
    have hq' : n ⬝ᵥ (R.M *ᵥ n) = 𝔅 (numW R N) (numW R N) := by
      rw [hsum]
      exact hq
    rw [← hq']
    show n ⬝ᵥ (R.M *ᵥ n) = -(n ⬝ᵥ ((-R.M) *ᵥ n))
    rw [Matrix.neg_mulVec, dotProduct_neg, neg_neg]
  have hnn : 0 ≤ 𝔅 (numW R N) (numW R N) := by
    rw [pairing_numW_left]
    exact Finset.sum_nonneg (fun C hC => mul_nonneg (by exact_mod_cast hN C) (hdeg C hC))
  have hn0 : n = 0 := by
    refine Classical.byContradiction fun h => ?_
    have hpos := R.A_posDef.2 n h
    simp only [star_trivial] at hpos
    linarith
  ext C
  rw [Finsupp.zero_apply]
  by_cases hC : IsExceptionalCurve R.π C
  · have h := congrFun hn0 ⟨C, hC⟩
    simp only [n, Pi.zero_apply, Int.cast_eq_zero] at h
    exact h
  · refine Classical.byContradiction fun hNC => ?_
    exact hC (hexc C (Finsupp.mem_support_iff.mpr hNC))

/-- **Exterior null curves occur in the remainder** (manuscript lines 1616–1620): if
`N ≡ K_S + A - ε P` with `N` effective, `A` nef and big, `P ∈ Supp A`, then every exterior
`A`-null curve `Q ∉ Supp A` has positive coefficient in `N`. -/
theorem pos_coeff_of_exteriorNull (A N : R.S.WeilDivisor) (hA : EffectiveDivisor A)
    (hN : EffectiveDivisor N) (P : R.S.PrimeCurve) (hPA : P ∈ A.support) (ε : ℚ)
    (hNnum : numW R N = R.Knum + numW R A - ε • 𝒞 P)
    (hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C (numW R A))
    (hbig : 0 < 𝔅 (numW R A) (numW R A))
    (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q)
    (hnull : R.S.numericalRestrictionDegree Q (numW R A) = 0) (hQA : Q ∉ A.support) :
    0 < N Q := by
  obtain ⟨hQm, hKQ⟩ := exteriorNullCurve_isMinusOne R (numW R A) hnef hbig Q hQ hnull
  have hPQ : 𝔅 (𝒞 P) (𝒞 Q) = 0 := pairing_eq_zero_of_deg_eq_zero R A hA Q hQA hnull P hPA
  have hQQ : 𝔅 (𝒞 Q) (𝒞 Q) = -1 := pairing_minusOne_self R Q hQm
  have hNQ : 𝔅 (numW R N) (𝒞 Q) = -1 := by
    rw [hNnum, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hPQ, Knum_pairing, hKQ, ← deg_eq_pairing, hnull]
    push_cast
    ring
  have hge := sum_pairing_ge R N hN Q
  rw [← pairing_numW_left, hNQ, hQQ] at hge
  have h1 : (1 : ℚ) ≤ N Q := by linarith
  exact_mod_cast (show (0 : ℚ) < N Q by linarith)

/-- A finite sum vanishing off two points. -/
theorem sum_eq_pair {α : Type*} [DecidableEq α] {s : Finset α} (f : α → ℚ) (a b : α)
    (hab : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a → c ≠ b → f c = 0)
    (ha : a ∉ s → f a = 0) (hb : b ∉ s → f b = 0) :
    ∑ c ∈ s, f c = f a + f b := by
  have h1 : ∑ c ∈ s, f c = ∑ c ∈ s ∪ {a, b}, f c := by
    apply Finset.sum_subset Finset.subset_union_left
    intro c hc hcs
    have hc' : c = a ∨ c = b := by
      rcases Finset.mem_union.mp hc with h | h
      · exact absurd h hcs
      · simpa using h
    rcases hc' with rfl | rfl
    · exact ha hcs
    · exact hb hcs
  have h2 : ∑ c ∈ s ∪ {a, b}, f c = ∑ c ∈ ({a, b} : Finset α), f c := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro c hc hcp
    have hcs : c ∈ s := by
      rcases Finset.mem_union.mp hc with h | h
      · exact h
      · exact absurd h hcp
    have hne : ¬ (c = a ∨ c = b) := by simpa using hcp
    exact h₀ c hcs (fun h => hne (Or.inl h)) (fun h => hne (Or.inr h))
  rw [h1, h2, Finset.sum_pair hab]

theorem mem_support_pair {W P : R.S.PrimeCurve} {a b : ℤ} (C : R.S.PrimeCurve)
    (hC : C ∈ (Finsupp.single W a + Finsupp.single P b).support) : C = W ∨ C = P := by
  by_contra hne
  push_neg at hne
  apply Finsupp.mem_support_iff.mp hC
  simp [Finsupp.single_apply, Ne.symm hne.1, Ne.symm hne.2]

theorem mem_support_triple {U V P : R.S.PrimeCurve} {a b c : ℤ} (C : R.S.PrimeCurve)
    (hC : C ∈ (Finsupp.single U a + Finsupp.single V b + Finsupp.single P c).support) :
    C = U ∨ C = V ∨ C = P := by
  refine Classical.byContradiction fun hne => ?_
  push_neg at hne
  apply Finsupp.mem_support_iff.mp hC
  simp [Finsupp.single_apply, Ne.symm hne.1, Ne.symm hne.2.1, Ne.symm hne.2.2]

/-- `K_S · C ≥ 0` for every exceptional curve (`K_S · D_i = b_i - 2`). -/
theorem Knum_pairing_nonneg_of_exceptional (C : R.S.PrimeCurve) (hC : IsExceptionalCurve R.π C) :
    0 ≤ 𝔅 (𝒞 C) R.Knum := by
  have h : 𝔅 R.Knum (𝒞 C) = R.w ⟨C, hC⟩ - 2 := Knum_pairing_vertex R ⟨C, hC⟩
  rw [pairing_symm, h]
  linarith [R.two_le_w ⟨C, hC⟩]

/-! ### Manuscript Lemma 6.1 -/

/-- **Lemma 6.1 (`lem:square-one-adjoint`), type (U1)** `A = W + P`: the effective adjoint
remainder `N` with `K_S + W + P ∼ N`. -/
theorem squareOneAdjoint_U1 (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (W : R.Vertices) (hW : R.w W = 2) (hPW : R.contact P W = 2)
    (hother : ∀ i : R.Vertices, i ≠ W → R.contact P i = 0) :
    ∃ N : R.S.WeilDivisor, EffectiveDivisor N ∧
      cartierPicardClass R.S.toScheme R.KS * R.curvePic W.val * R.curvePic P =
        R.S.regularWeilPicardClass R.hreg N ∧
      (N.sum fun C a => (a : ℚ) * R.Ldeg C) = R.Ldeg P - R.Lsq ∧
      (∀ C ∈ N.support, R.S.numericalRestrictionDegree C (𝒞 W.val + 𝒞 P) = 0) ∧
      Disjoint N.support (Finsupp.single W.val (1 : ℤ) + Finsupp.single P 1).support ∧
      (∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q →
        R.S.numericalRestrictionDegree Q (𝒞 W.val + 𝒞 P) = 0 →
        Q ∉ (Finsupp.single W.val (1 : ℤ) + Finsupp.single P 1).support → 0 < N Q) ∧
      (N = 0 ↔ ¬ ∃ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q ∧
        R.S.numericalRestrictionDegree Q (𝒞 W.val + 𝒞 P) = 0 ∧
        Q ∉ (Finsupp.single W.val (1 : ℤ) + Finsupp.single P 1).support) := by
  classical
  set A : R.S.WeilDivisor := Finsupp.single W.val 1 + Finsupp.single P 1 with hAdef
  have hPW' : P ≠ W.val := fun h => hP.2 (h ▸ W.property)
  have hWP' : W.val ≠ P := fun h => hPW' h.symm
  have hAnum : numW R A = 𝒞 W.val + 𝒞 P := by
    rw [hAdef, numW_add, numW_single, numW_single, Int.cast_one, one_smul, one_smul]
  have hAeff : EffectiveDivisor A := by
    intro C
    simp only [hAdef, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  have hAsupp : ∀ C, C ∈ A.support → C = W.val ∨ C = P := fun C hC => mem_support_pair R C hC
  have hWA : W.val ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hPW']
  have hPA : P ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hWP']
  -- the intersection table
  have hWW : 𝔅 (𝒞 W.val) (𝒞 W.val) = -2 := by rw [pairing_vertex_self, hW]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hPWp : 𝔅 (𝒞 P) (𝒞 W.val) = 2 := by rw [pairing_contact, hPW]; norm_num
  have hWPp : 𝔅 (𝒞 W.val) (𝒞 P) = 2 := by rw [pairing_symm, hPWp]
  have hKW : 𝔅 R.Knum (𝒞 W.val) = 0 := by rw [Knum_pairing_vertex, hW]; norm_num
  have hKP : 𝔅 R.Knum (𝒞 P) = -1 := Knum_pairing_minusOne R P hP.1
  -- degrees of `A`
  have hdegA : ∀ C, R.S.numericalRestrictionDegree C (numW R A) =
      𝔅 (𝒞 W.val) (𝒞 C) + 𝔅 (𝒞 P) (𝒞 C) := by
    intro C
    rw [hAnum, deg_eq_pairing, LinearMap.BilinForm.add_left]
  have hdegW : R.S.numericalRestrictionDegree W.val (numW R A) = 0 := by
    rw [hdegA, hWW, hPWp]; norm_num
  have hdegP : R.S.numericalRestrictionDegree P (numW R A) = 1 := by
    rw [hdegA, hWPp, hPP]; norm_num
  have hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C (numW R A) := by
    intro C
    by_cases hCW : C = W.val
    · rw [hCW, hdegW]
    by_cases hCP : C = P
    · rw [hCP, hdegP]; norm_num
    rw [hdegA]
    exact add_nonneg (pairing_nonneg_of_ne R _ _ (Ne.symm hCW))
      (pairing_nonneg_of_ne R _ _ (Ne.symm hCP))
  have hA2 : 𝔅 (numW R A) (numW R A) = 1 := by
    rw [hAnum]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hWW, hPP, hPWp, hWPp]
    norm_num
  have hKA : 𝔅 R.Knum (numW R A) = -1 := by
    rw [hAnum, LinearMap.BilinForm.add_right, hKW, hKP]; norm_num
  -- Riemann–Roch
  obtain ⟨Z, hZ, hZlin⟩ := exists_effective_adjoint R p hp A hnef hA2 hKA
  have hZnum : numW R Z = R.Knum + numW R A := by
    rw [numW_eq_of_linearlyEquivalent R hZlin, numW_add, numW_KS]
  have hAZ : 𝔅 (numW R A) (numW R Z) = 0 := by
    rw [hZnum, LinearMap.BilinForm.add_right, pairing_symm R (numW R A) R.Knum, hKA, hA2]
    norm_num
  have hnullZ : ∀ C ∈ Z.support, R.S.numericalRestrictionDegree C (numW R A) = 0 :=
    deg_eq_zero_of_mem_support R (numW R A) Z hZ hnef hAZ
  have hPZ : P ∉ Z.support := by
    intro h
    have := hnullZ P h
    rw [hdegP] at this
    exact one_ne_zero this
  have hoff : ∀ C ∈ Z.support, C ≠ W.val → 𝔅 (𝒞 W.val) (𝒞 C) = 0 := by
    intro C hC hCW
    have hCA : C ∉ A.support := by
      intro h
      rcases hAsupp C h with h | h
      · exact hCW h
      · exact hPZ (h ▸ hC)
    exact pairing_eq_zero_of_deg_eq_zero R A hAeff C hCA (hnullZ C hC) W.val hWA
  have hZW : Z W.val = 0 := by
    have h1 : 𝔅 (numW R Z) (𝒞 W.val) = 0 := by
      rw [hZnum, hAnum, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left, hKW, hWW, hPWp]
      norm_num
    rw [pairing_numW_left] at h1
    unfold Finsupp.sum at h1
    rw [Finset.sum_eq_single W.val
      (fun C hC hCW => by
        dsimp only
        rw [pairing_symm R (𝒞 C) (𝒞 W.val), hoff C hC hCW, mul_zero])
      (fun h => by simp [Finsupp.not_mem_support_iff.mp h])] at h1
    dsimp only at h1
    rw [hWW] at h1
    have : (Z W.val : ℚ) = 0 := by linarith
    exact_mod_cast this
  have hWZ : W.val ∉ Z.support := fun h => Finsupp.mem_support_iff.mp h hZW
  have hdisj : ∀ C ∈ Z.support, C ∉ A.support := by
    intro C hC hCA
    rcases hAsupp C hCA with h | h
    · exact hWZ (h ▸ hC)
    · exact hPZ (h ▸ hC)
  have hpos : ∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q →
      R.S.numericalRestrictionDegree Q (𝒞 W.val + 𝒞 P) = 0 → Q ∉ A.support → 0 < Z Q := by
    intro Q hQ hnull hQA
    rw [← hAnum] at hnull
    exact pos_coeff_of_exteriorNull R A Z hAeff hZ P hPA 0 (by rw [hZnum, zero_smul, sub_zero])
      hnef (by rw [hA2]; norm_num) Q hQ hnull hQA
  refine ⟨Z, hZ, ?_, ?_, ?_, Finset.disjoint_left.mpr hdisj, hpos, ?_⟩
  · -- the Picard identity `K_S + W + P ∼ N`
    rw [picardClass_eq_of_linearlyEquivalent R hZlin, hAdef, R.S.regularWeilPicardClass_add,
      R.S.regularWeilPicardClass_add, picardClass_KS, picardClass_single, picardClass_single,
      mul_assoc]
  · -- the `L`-degree `L · N = L · P - L²`
    have h := pairing_numW_right R R.Lnum Z
    rw [hZnum, hAnum, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
      Lnum_pairing_Knum, Lnum_pairing, Lnum_pairing, R.Ldeg_exceptional W] at h
    have h2 : (Z.sum fun C a => (a : ℚ) * R.Ldeg C) =
        Z.sum fun C a => (a : ℚ) * 𝔅 R.Lnum (𝒞 C) :=
      Finsupp.sum_congr (fun C _ => by rw [Lnum_pairing])
    rw [h2]
    linarith
  · intro C hC
    rw [← hAnum]
    exact hnullZ C hC
  · constructor
    · rintro hN0 ⟨Q, hQ, hnull, hQA⟩
      have := hpos Q hQ hnull hQA
      rw [hN0] at this
      simp at this
    · intro hno
      have hexc : ∀ C ∈ Z.support, IsExceptionalCurve R.π C := by
        intro C hC
        refine Classical.byContradiction fun hCex => ?_
        apply hno
        refine ⟨C, hCex, ?_, hdisj C hC⟩
        rw [← hAnum]
        exact hnullZ C hC
      refine eq_zero_of_exceptional_support R Z hZ hexc ?_
      intro C hC
      rw [hZnum, LinearMap.BilinForm.add_right, pairing_symm R (𝒞 C) (numW R A),
        ← deg_eq_pairing, hnullZ C hC, add_zero]
      exact Knum_pairing_nonneg_of_exceptional R C (hexc C hC)


/-- **Lemma 6.1 (`lem:square-one-adjoint`), type (U2)** `A = U + V + P`: the effective adjoint
remainder `N` with `K_S + U + V + P ∼ N`. The distinctness of the three intersection points is
recorded as in the manuscript but is not needed for the algebra. -/
theorem squareOneAdjoint_U2 (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (U V : R.Vertices) (hUV : U ≠ V) (hwU : R.w U = 2) (hwV : R.w V = 2)
    (hadj : R.graph.Adj U V) (hPU : R.contact P U = 1) (hPV : R.contact P V = 1)
    (hother : ∀ i : R.Vertices, i ≠ U → i ≠ V → R.contact P i = 0)
    (hdistinct :
      Disjoint ((U.val : Set R.S.toScheme) ∩ (V.val : Set R.S.toScheme))
        ((U.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme)) ∧
      Disjoint ((U.val : Set R.S.toScheme) ∩ (V.val : Set R.S.toScheme))
        ((V.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme)) ∧
      Disjoint ((U.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme))
        ((V.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme))) :
    ∃ N : R.S.WeilDivisor, EffectiveDivisor N ∧
      cartierPicardClass R.S.toScheme R.KS * R.curvePic U.val * R.curvePic V.val * R.curvePic P =
        R.S.regularWeilPicardClass R.hreg N ∧
      (N.sum fun C a => (a : ℚ) * R.Ldeg C) = R.Ldeg P - R.Lsq ∧
      (∀ C ∈ N.support, R.S.numericalRestrictionDegree C (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 0) ∧
      Disjoint N.support
        (Finsupp.single U.val (1 : ℤ) + Finsupp.single V.val 1 + Finsupp.single P 1).support ∧
      (∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q →
        R.S.numericalRestrictionDegree Q (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 0 →
        Q ∉ (Finsupp.single U.val (1 : ℤ) + Finsupp.single V.val 1 + Finsupp.single P 1).support →
        0 < N Q) ∧
      (N = 0 ↔ ¬ ∃ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q ∧
        R.S.numericalRestrictionDegree Q (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 0 ∧
        Q ∉ (Finsupp.single U.val (1 : ℤ) + Finsupp.single V.val 1 +
          Finsupp.single P 1).support) := by
  classical
  set A : R.S.WeilDivisor :=
    Finsupp.single U.val 1 + Finsupp.single V.val 1 + Finsupp.single P 1 with hAdef
  have hPU' : P ≠ U.val := fun h => hP.2 (h ▸ U.property)
  have hPV' : P ≠ V.val := fun h => hP.2 (h ▸ V.property)
  have hUV' : U.val ≠ V.val := fun h => hUV (Subtype.ext h)
  have hAnum : numW R A = 𝒞 U.val + 𝒞 V.val + 𝒞 P := by
    rw [hAdef, numW_add, numW_add, numW_single, numW_single, numW_single, Int.cast_one, one_smul,
      one_smul, one_smul]
  have hAeff : EffectiveDivisor A := by
    intro C
    simp only [hAdef, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  have hAsupp : ∀ C, C ∈ A.support → C = U.val ∨ C = V.val ∨ C = P :=
    fun C hC => mem_support_triple R C hC
  have hUA : U.val ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hPU', hUV'.symm]
  have hVA : V.val ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hPV', hUV']
  have hPA : P ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hPU'.symm, hPV'.symm]
  -- the intersection table
  have hUU : 𝔅 (𝒞 U.val) (𝒞 U.val) = -2 := by rw [pairing_vertex_self, hwU]
  have hVV : 𝔅 (𝒞 V.val) (𝒞 V.val) = -2 := by rw [pairing_vertex_self, hwV]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hUVp : 𝔅 (𝒞 U.val) (𝒞 V.val) = 1 := by rw [pairing_vertices, M_eq_one_of_adj R hadj]
  have hVUp : 𝔅 (𝒞 V.val) (𝒞 U.val) = 1 := by rw [pairing_symm, hUVp]
  have hPUp : 𝔅 (𝒞 P) (𝒞 U.val) = 1 := by rw [pairing_contact, hPU]; norm_num
  have hUPp : 𝔅 (𝒞 U.val) (𝒞 P) = 1 := by rw [pairing_symm, hPUp]
  have hPVp : 𝔅 (𝒞 P) (𝒞 V.val) = 1 := by rw [pairing_contact, hPV]; norm_num
  have hVPp : 𝔅 (𝒞 V.val) (𝒞 P) = 1 := by rw [pairing_symm, hPVp]
  have hKU : 𝔅 R.Knum (𝒞 U.val) = 0 := by rw [Knum_pairing_vertex, hwU]; norm_num
  have hKV : 𝔅 R.Knum (𝒞 V.val) = 0 := by rw [Knum_pairing_vertex, hwV]; norm_num
  have hKP : 𝔅 R.Knum (𝒞 P) = -1 := Knum_pairing_minusOne R P hP.1
  -- degrees of `A`
  have hdegA : ∀ C, R.S.numericalRestrictionDegree C (numW R A) =
      𝔅 (𝒞 U.val) (𝒞 C) + 𝔅 (𝒞 V.val) (𝒞 C) + 𝔅 (𝒞 P) (𝒞 C) := by
    intro C
    rw [hAnum, deg_eq_pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left]
  have hdegU : R.S.numericalRestrictionDegree U.val (numW R A) = 0 := by
    rw [hdegA, hUU, hVUp, hPUp]; norm_num
  have hdegV : R.S.numericalRestrictionDegree V.val (numW R A) = 0 := by
    rw [hdegA, hUVp, hVV, hPVp]; norm_num
  have hdegP : R.S.numericalRestrictionDegree P (numW R A) = 1 := by
    rw [hdegA, hUPp, hVPp, hPP]; norm_num
  have hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C (numW R A) := by
    intro C
    by_cases hCU : C = U.val
    · rw [hCU, hdegU]
    by_cases hCV : C = V.val
    · rw [hCV, hdegV]
    by_cases hCP : C = P
    · rw [hCP, hdegP]; norm_num
    rw [hdegA]
    exact add_nonneg (add_nonneg (pairing_nonneg_of_ne R _ _ (Ne.symm hCU))
      (pairing_nonneg_of_ne R _ _ (Ne.symm hCV))) (pairing_nonneg_of_ne R _ _ (Ne.symm hCP))
  have hA2 : 𝔅 (numW R A) (numW R A) = 1 := by
    rw [hAnum]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hUU, hVV, hPP, hUVp,
      hVUp, hPUp, hUPp, hPVp, hVPp]
    norm_num
  have hKA : 𝔅 R.Knum (numW R A) = -1 := by
    rw [hAnum, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, hKU, hKV, hKP]
    norm_num
  -- Riemann–Roch
  obtain ⟨Z, hZ, hZlin⟩ := exists_effective_adjoint R p hp A hnef hA2 hKA
  have hZnum : numW R Z = R.Knum + numW R A := by
    rw [numW_eq_of_linearlyEquivalent R hZlin, numW_add, numW_KS]
  have hAZ : 𝔅 (numW R A) (numW R Z) = 0 := by
    rw [hZnum, LinearMap.BilinForm.add_right, pairing_symm R (numW R A) R.Knum, hKA, hA2]
    norm_num
  have hnullZ : ∀ C ∈ Z.support, R.S.numericalRestrictionDegree C (numW R A) = 0 :=
    deg_eq_zero_of_mem_support R (numW R A) Z hZ hnef hAZ
  have hPZ : P ∉ Z.support := by
    intro h
    have := hnullZ P h
    rw [hdegP] at this
    exact one_ne_zero this
  have hoff : ∀ C ∈ Z.support, C ≠ U.val → C ≠ V.val →
      𝔅 (𝒞 U.val) (𝒞 C) = 0 ∧ 𝔅 (𝒞 V.val) (𝒞 C) = 0 := by
    intro C hC hCU hCV
    have hCA : C ∉ A.support := by
      intro h
      rcases hAsupp C h with h | h | h
      · exact hCU h
      · exact hCV h
      · exact hPZ (h ▸ hC)
    exact ⟨pairing_eq_zero_of_deg_eq_zero R A hAeff C hCA (hnullZ C hC) U.val hUA,
      pairing_eq_zero_of_deg_eq_zero R A hAeff C hCA (hnullZ C hC) V.val hVA⟩
  -- the supported coefficients solve `[[-2, 1], [1, -2]] z = 0`
  have hZU : 𝔅 (numW R Z) (𝒞 U.val) = (Z U.val : ℚ) * (-2) + (Z V.val : ℚ) * 1 := by
    rw [pairing_numW_left]
    unfold Finsupp.sum
    rw [sum_eq_pair _ U.val V.val hUV'
      (fun C hC hCU hCV => by
        dsimp only
        rw [pairing_symm R (𝒞 C) (𝒞 U.val), (hoff C hC hCU hCV).1, mul_zero])
      (fun h => by simp [Finsupp.not_mem_support_iff.mp h])
      (fun h => by simp [Finsupp.not_mem_support_iff.mp h])]
    dsimp only
    rw [hUU, hVUp]
  have hZV : 𝔅 (numW R Z) (𝒞 V.val) = (Z U.val : ℚ) * 1 + (Z V.val : ℚ) * (-2) := by
    rw [pairing_numW_left]
    unfold Finsupp.sum
    rw [sum_eq_pair _ U.val V.val hUV'
      (fun C hC hCU hCV => by
        dsimp only
        rw [pairing_symm R (𝒞 C) (𝒞 V.val), (hoff C hC hCU hCV).2, mul_zero])
      (fun h => by simp [Finsupp.not_mem_support_iff.mp h])
      (fun h => by simp [Finsupp.not_mem_support_iff.mp h])]
    dsimp only
    rw [hUVp, hVV]
  have hZU0 : 𝔅 (numW R Z) (𝒞 U.val) = 0 := by
    rw [hZnum, hAnum, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_left, hKU, hUU, hVUp, hPUp]
    norm_num
  have hZV0 : 𝔅 (numW R Z) (𝒞 V.val) = 0 := by
    rw [hZnum, hAnum, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_left, hKV, hUVp, hVV, hPVp]
    norm_num
  have hcoeffU : Z U.val = 0 := by
    have h1 := hZU
    rw [hZU0] at h1
    have h2 := hZV
    rw [hZV0] at h2
    have : (Z U.val : ℚ) = 0 := by linarith
    exact_mod_cast this
  have hcoeffV : Z V.val = 0 := by
    have h1 := hZU
    rw [hZU0] at h1
    have h2 := hZV
    rw [hZV0] at h2
    have : (Z V.val : ℚ) = 0 := by linarith
    exact_mod_cast this
  have hUZ : U.val ∉ Z.support := fun h => Finsupp.mem_support_iff.mp h hcoeffU
  have hVZ : V.val ∉ Z.support := fun h => Finsupp.mem_support_iff.mp h hcoeffV
  have hdisj : ∀ C ∈ Z.support, C ∉ A.support := by
    intro C hC hCA
    rcases hAsupp C hCA with h | h | h
    · exact hUZ (h ▸ hC)
    · exact hVZ (h ▸ hC)
    · exact hPZ (h ▸ hC)
  have hpos : ∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q →
      R.S.numericalRestrictionDegree Q (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 0 → Q ∉ A.support →
      0 < Z Q := by
    intro Q hQ hnull hQA
    rw [← hAnum] at hnull
    exact pos_coeff_of_exteriorNull R A Z hAeff hZ P hPA 0 (by rw [hZnum, zero_smul, sub_zero])
      hnef (by rw [hA2]; norm_num) Q hQ hnull hQA
  refine ⟨Z, hZ, ?_, ?_, ?_, Finset.disjoint_left.mpr hdisj, hpos, ?_⟩
  · -- the Picard identity `K_S + U + V + P ∼ N`
    rw [picardClass_eq_of_linearlyEquivalent R hZlin, hAdef, R.S.regularWeilPicardClass_add,
      R.S.regularWeilPicardClass_add, R.S.regularWeilPicardClass_add, picardClass_KS,
      picardClass_single, picardClass_single, picardClass_single]
    simp only [mul_assoc]
  · -- the `L`-degree
    have h := pairing_numW_right R R.Lnum Z
    rw [hZnum, hAnum, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, Lnum_pairing_Knum, Lnum_pairing, Lnum_pairing, Lnum_pairing,
      R.Ldeg_exceptional U, R.Ldeg_exceptional V] at h
    have h2 : (Z.sum fun C a => (a : ℚ) * R.Ldeg C) =
        Z.sum fun C a => (a : ℚ) * 𝔅 R.Lnum (𝒞 C) :=
      Finsupp.sum_congr (fun C _ => by rw [Lnum_pairing])
    rw [h2]
    linarith
  · intro C hC
    rw [← hAnum]
    exact hnullZ C hC
  · constructor
    · rintro hN0 ⟨Q, hQ, hnull, hQA⟩
      have := hpos Q hQ hnull hQA
      rw [hN0] at this
      simp at this
    · intro hno
      have hexc : ∀ C ∈ Z.support, IsExceptionalCurve R.π C := by
        intro C hC
        refine Classical.byContradiction fun hCex => ?_
        apply hno
        refine ⟨C, hCex, ?_, hdisj C hC⟩
        rw [← hAnum]
        exact hnullZ C hC
      refine eq_zero_of_exceptional_support R Z hZ hexc ?_
      intro C hC
      rw [hZnum, LinearMap.BilinForm.add_right, pairing_symm R (𝒞 C) (numW R A),
        ← deg_eq_pairing, hnullZ C hC, add_zero]
      exact Knum_pairing_nonneg_of_exceptional R C (hexc C hC)

/-- **Lemma 6.1 (`lem:square-one-adjoint`), type (U3)** `A = B + 2P`: the effective adjoint
remainder `N` with `K_S + B + 2P ∼ P + N`. -/
theorem squareOneAdjoint_U3 (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (B : R.Vertices) (hwB : R.w B = 3) (hPB : R.contact P B = 2)
    (hother : ∀ i : R.Vertices, i ≠ B → R.contact P i = 0) :
    ∃ N : R.S.WeilDivisor, EffectiveDivisor N ∧
      cartierPicardClass R.S.toScheme R.KS * R.curvePic B.val * R.curvePic P ^ 2 =
        R.curvePic P * R.S.regularWeilPicardClass R.hreg N ∧
      (N.sum fun C a => (a : ℚ) * R.Ldeg C) = R.Ldeg P - R.Lsq ∧
      (∀ C ∈ N.support, R.S.numericalRestrictionDegree C (𝒞 B.val + (2 : ℚ) • 𝒞 P) = 0) ∧
      Disjoint N.support (Finsupp.single B.val (1 : ℤ) + Finsupp.single P 2).support ∧
      (∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q →
        R.S.numericalRestrictionDegree Q (𝒞 B.val + (2 : ℚ) • 𝒞 P) = 0 →
        Q ∉ (Finsupp.single B.val (1 : ℤ) + Finsupp.single P 2).support → 0 < N Q) ∧
      (N = 0 ↔ ¬ ∃ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q ∧
        R.S.numericalRestrictionDegree Q (𝒞 B.val + (2 : ℚ) • 𝒞 P) = 0 ∧
        Q ∉ (Finsupp.single B.val (1 : ℤ) + Finsupp.single P 2).support) := by
  classical
  set A : R.S.WeilDivisor := Finsupp.single B.val 1 + Finsupp.single P 2 with hAdef
  have hPB' : P ≠ B.val := fun h => hP.2 (h ▸ B.property)
  have hBP' : B.val ≠ P := fun h => hPB' h.symm
  have hAnum : numW R A = 𝒞 B.val + (2 : ℚ) • 𝒞 P := by
    rw [hAdef, numW_add, numW_single, numW_single, Int.cast_one, one_smul, Int.cast_ofNat]
  have hAeff : EffectiveDivisor A := by
    intro C
    simp only [hAdef, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num
  have hAsupp : ∀ C, C ∈ A.support → C = B.val ∨ C = P := fun C hC => mem_support_pair R C hC
  have hBA : B.val ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hPB']
  have hPA : P ∈ A.support := by
    rw [Finsupp.mem_support_iff, hAdef]
    simp [Finsupp.single_apply, hBP']
  -- the intersection table
  have hBB : 𝔅 (𝒞 B.val) (𝒞 B.val) = -3 := by rw [pairing_vertex_self, hwB]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hPBp : 𝔅 (𝒞 P) (𝒞 B.val) = 2 := by rw [pairing_contact, hPB]; norm_num
  have hBPp : 𝔅 (𝒞 B.val) (𝒞 P) = 2 := by rw [pairing_symm, hPBp]
  have hKB : 𝔅 R.Knum (𝒞 B.val) = 1 := by rw [Knum_pairing_vertex, hwB]; norm_num
  have hKP : 𝔅 R.Knum (𝒞 P) = -1 := Knum_pairing_minusOne R P hP.1
  -- degrees of `A`
  have hdegA : ∀ C, R.S.numericalRestrictionDegree C (numW R A) =
      𝔅 (𝒞 B.val) (𝒞 C) + 2 * 𝔅 (𝒞 P) (𝒞 C) := by
    intro C
    rw [hAnum, deg_eq_pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  have hdegB : R.S.numericalRestrictionDegree B.val (numW R A) = 1 := by
    rw [hdegA, hBB, hPBp]; norm_num
  have hdegP : R.S.numericalRestrictionDegree P (numW R A) = 0 := by
    rw [hdegA, hBPp, hPP]; norm_num
  have hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C (numW R A) := by
    intro C
    by_cases hCB : C = B.val
    · rw [hCB, hdegB]; norm_num
    by_cases hCP : C = P
    · rw [hCP, hdegP]
    rw [hdegA]
    have h1 := pairing_nonneg_of_ne R B.val C (Ne.symm hCB)
    have h2 := pairing_nonneg_of_ne R P C (Ne.symm hCP)
    linarith
  have hA2 : 𝔅 (numW R A) (numW R A) = 1 := by
    rw [hAnum]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, smul_eq_mul, hBB, hPP, hPBp,
      hBPp]
    norm_num
  have hKA : 𝔅 R.Knum (numW R A) = -1 := by
    rw [hAnum, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hKB, hKP]
    norm_num
  -- Riemann–Roch
  obtain ⟨Z, hZ, hZlin⟩ := exists_effective_adjoint R p hp A hnef hA2 hKA
  have hZnum : numW R Z = R.Knum + numW R A := by
    rw [numW_eq_of_linearlyEquivalent R hZlin, numW_add, numW_KS]
  have hAZ : 𝔅 (numW R A) (numW R Z) = 0 := by
    rw [hZnum, LinearMap.BilinForm.add_right, pairing_symm R (numW R A) R.Knum, hKA, hA2]
    norm_num
  have hnullZ : ∀ C ∈ Z.support, R.S.numericalRestrictionDegree C (numW R A) = 0 :=
    deg_eq_zero_of_mem_support R (numW R A) Z hZ hnef hAZ
  have hBZ : B.val ∉ Z.support := by
    intro h
    have := hnullZ B.val h
    rw [hdegB] at this
    exact one_ne_zero this
  have hZB : Z B.val = 0 := Finsupp.not_mem_support_iff.mp hBZ
  have hoff : ∀ C ∈ Z.support, C ≠ P → 𝔅 (𝒞 P) (𝒞 C) = 0 := by
    intro C hC hCP
    have hCA : C ∉ A.support := by
      intro h
      rcases hAsupp C h with h | h
      · exact hBZ (h ▸ hC)
      · exact hCP h
    exact pairing_eq_zero_of_deg_eq_zero R A hAeff C hCA (hnullZ C hC) P hPA
  -- `Z · P = K_S · P = -1` forces `Z_P = 1`
  have hZP : Z P = 1 := by
    have h1 : 𝔅 (numW R Z) (𝒞 P) = -1 := by
      rw [hZnum, hAnum, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.smul_left, hKP, hBPp, hPP]
      norm_num
    rw [pairing_numW_left] at h1
    unfold Finsupp.sum at h1
    rw [Finset.sum_eq_single P
      (fun C hC hCP => by
        dsimp only
        rw [pairing_symm R (𝒞 C) (𝒞 P), hoff C hC hCP, mul_zero])
      (fun h => by simp [Finsupp.not_mem_support_iff.mp h])] at h1
    dsimp only at h1
    rw [hPP] at h1
    have : (Z P : ℚ) = 1 := by linarith
    exact_mod_cast this
  -- the remainder `N = Z - P`
  set N : R.S.WeilDivisor := Z - Finsupp.single P 1 with hNdef
  have hNP : N P = 0 := by simp [hNdef, hZP]
  have hNother : ∀ C, C ≠ P → N C = Z C := by
    intro C hC
    simp [hNdef, Finsupp.single_apply, Ne.symm hC]
  have hNeff : EffectiveDivisor N := by
    intro C
    by_cases hC : C = P
    · rw [hC, hNP]
    · rw [hNother C hC]
      exact hZ C
  have hNnum : numW R N = R.Knum + numW R A - (1 : ℚ) • 𝒞 P := by
    rw [hNdef, numW_sub, hZnum, numW_single, Int.cast_one]
  have hNsupp : ∀ C ∈ N.support, C ∈ Z.support ∧ C ≠ P ∧ C ≠ B.val := by
    intro C hC
    have hCP : C ≠ P := by
      intro h
      apply Finsupp.mem_support_iff.mp hC
      rw [h, hNP]
    refine ⟨?_, hCP, ?_⟩
    · rw [Finsupp.mem_support_iff, ← hNother C hCP]
      exact Finsupp.mem_support_iff.mp hC
    · intro h
      apply Finsupp.mem_support_iff.mp hC
      rw [hNother C hCP, h, hZB]
  have hZeq : Z = N + Finsupp.single P 1 := by rw [hNdef, sub_add_cancel]
  have hdisj : ∀ C ∈ N.support, C ∉ A.support := by
    intro C hC hCA
    obtain ⟨_, hCP, hCB⟩ := hNsupp C hC
    rcases hAsupp C hCA with h | h
    · exact hCB h
    · exact hCP h
  have hpos : ∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q →
      R.S.numericalRestrictionDegree Q (𝒞 B.val + (2 : ℚ) • 𝒞 P) = 0 → Q ∉ A.support →
      0 < N Q := by
    intro Q hQ hnull hQA
    rw [← hAnum] at hnull
    exact pos_coeff_of_exteriorNull R A N hAeff hNeff P hPA 1 hNnum hnef (by rw [hA2]; norm_num)
      Q hQ hnull hQA
  refine ⟨N, hNeff, ?_, ?_, ?_, Finset.disjoint_left.mpr hdisj, hpos, ?_⟩
  · -- the Picard identity `K_S + B + 2P ∼ P + N`
    have h2 : Finsupp.single P (2 : ℤ) = Finsupp.single P 1 + Finsupp.single P 1 := by
      rw [← Finsupp.single_add]
      norm_num
    have h := picardClass_eq_of_linearlyEquivalent R hZlin
    rw [hZeq, hAdef, h2, R.S.regularWeilPicardClass_add, R.S.regularWeilPicardClass_add,
      R.S.regularWeilPicardClass_add, R.S.regularWeilPicardClass_add, picardClass_KS,
      picardClass_single, picardClass_single] at h
    simp only [sq, mul_assoc]
    rw [← h, mul_comm]
  · -- the `L`-degree
    have h := pairing_numW_right R R.Lnum N
    rw [hNnum, hAnum, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.smul_right, Lnum_pairing_Knum, Lnum_pairing,
      Lnum_pairing, R.Ldeg_exceptional B] at h
    have h2 : (N.sum fun C a => (a : ℚ) * R.Ldeg C) =
        N.sum fun C a => (a : ℚ) * 𝔅 R.Lnum (𝒞 C) :=
      Finsupp.sum_congr (fun C _ => by rw [Lnum_pairing])
    rw [h2]
    linarith
  · intro C hC
    rw [← hAnum]
    exact hnullZ C (hNsupp C hC).1
  · constructor
    · rintro hN0 ⟨Q, hQ, hnull, hQA⟩
      have := hpos Q hQ hnull hQA
      rw [hN0] at this
      simp at this
    · intro hno
      have hexc : ∀ C ∈ N.support, IsExceptionalCurve R.π C := by
        intro C hC
        refine Classical.byContradiction fun hCex => ?_
        apply hno
        refine ⟨C, hCex, ?_, hdisj C hC⟩
        rw [← hAnum]
        exact hnullZ C (hNsupp C hC).1
      refine eq_zero_of_exceptional_support R N hNeff hexc ?_
      intro C hC
      obtain ⟨hCZ, hCP, hCB⟩ := hNsupp C hC
      have hCPp : 𝔅 (𝒞 C) (𝒞 P) = 0 := by
        rw [pairing_symm R (𝒞 C) (𝒞 P)]
        exact hoff C hCZ hCP
      rw [hNnum, LinearMap.BilinForm.sub_right, LinearMap.BilinForm.add_right,
        LinearMap.BilinForm.smul_right, hCPp, pairing_symm R (𝒞 C) (numW R A),
        ← deg_eq_pairing, hnullZ C hCZ]
      have := Knum_pairing_nonneg_of_exceptional R C (hexc C hC)
      linarith

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06.squareOneAdjoint_U1
#print axioms KltDP.Manuscript.S06.squareOneAdjoint_U2
#print axioms KltDP.Manuscript.S06.squareOneAdjoint_U3
