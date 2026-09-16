import KltDP.Examples.FrobeniusFiberZeroInvertible
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.CartierDivisorOfEquations

/-!
# `F_0 = b`: the class of the fibre `y = 0` is the class of the fibre `y = 1`

Lane A2's tower relation starts from `fiberPicardClass h 0 = −[I(F_0)]`, the class of the stage-`0`
strict fibre `y = 0` of `P¹ × P¹`, while the accepted `b` is `secondFiberClass = −[I(y = 1)]`
(`= cartierPicardHom (rulingInfinityDivisor 1)`, the class of the ruling `y = ∞`). This module proves
`fiberPicardClass h 0 = secondFiberClass`:

* `fiberZeroDivisor`: the effective Cartier divisor of `y = 0`, glued (BRIEF8 `cartierDivisorOfEquations`)
  from the equations `y` on the open `y ≠ ∞` and `1` on the open `y ≠ 0` — the same two ruling opens as
  the accepted `rulingInfinityDivisor 1` (equations `1` and `y⁻¹`); hence
  `fiberZeroDivisor = rulingInfinityDivisor 1 + div(y)` and the two Cartier classes agree
  (`fiberZeroDivisor_picard`).
* It has regular equations on the four product charts (`fiberZeroChartZero`, `fiberZeroChartOne`):
  on `(i, 0)` the coefficient is the chart coordinate `v` — whose germ is the ruling coordinate `y` by the
  accepted `productFunctionFieldMap_v` — and on `(i, 1)` it is `1`.
* Its ideal sheaf (accepted `effectiveCartierIdealDataOfRegularEquations`) is the ideal sheaf of the
  fibre: both are kernels of quasi-compact morphisms and agree on every affine open inside a product chart
  (BRIEF17 chart ideals transported by `IdealSheafData.map_ideal`), so a kernel-locality lemma proved
  here (`Scheme.Hom.ker_eq_of_cover`, sections vanish iff they vanish on an affine cover) gives
  `fiberZeroIdealData_eq`; the accepted `effectiveCartierKernelIso` then identifies `O(−E)` with the
  kernel module of the fibre, i.e. `[I(F_0)] = [O(−E)]`.

Bundles: `f29_fiber_zero_class : fiberPicardClass h 0 = secondFiberClass` and the manuscript's
normalisation `π^*b = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P` (`f29_tower_fiber_picard_relation_b`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

/-! ## Kernels are determined on an affine cover -/

/-- Restricting `f.app U s` to the preimage of a smaller open is `f.app` of the restricted section. -/
theorem Scheme.Hom.app_restrict_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {U W : Y.Opens} (h : W ≤ U)
    (s : Γ(Y, U)) :
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op (f.app U s) =
      f.app W (Y.presheaf.map (homOfLE h).op s) := by
  have hmor : f.app U ≫
      X.presheaf.map (homOfLE (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op =
        Y.presheaf.map (homOfLE h).op ≫ f.app W := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
      Scheme.Hom.map_appLE]
  exact ConcreteCategory.congr_hom hmor s

/-- A section is killed by `f.app U` iff its restrictions to the affine opens of `U` lying in a covering
family belong to the kernel ideal there. -/
theorem Scheme.Hom.app_eq_zero_iff_of_cover {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {ι : Type*} (V : ι → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i) (U : Y.affineOpens) (s : Γ(Y, U)) :
    f.app U s = 0 ↔
      ∀ (W : Y.affineOpens) (hWU : W.1 ≤ U.1), (∃ i, W.1 ≤ V i) →
        Y.presheaf.map (homOfLE hWU).op s ∈ f.ker.ideal W := by
  constructor
  · intro h W hWU _
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    change f.app W (Y.presheaf.map (homOfLE hWU).op s) = 0
    rw [← Scheme.Hom.app_restrict_eq f hWU s, h, map_zero]
  · intro h
    refine X.sheaf.eq_of_locally_eq'
      (U := fun W : {W : Y.affineOpens // W.1 ≤ U.1 ∧ ∃ i, W.1 ≤ V i} => f ⁻¹ᵁ W.1.1)
      (f ⁻¹ᵁ U.1) (fun W => homOfLE (fun _ hx => W.2.1 hx)) ?_ (f.app U s) 0 ?_
    · intro x hx
      obtain ⟨i, hi⟩ := hV (f.base x)
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ := (isBasis_affine_open Y).exists_subset_of_mem_open
        (show f.base x ∈ (U.1 ⊓ V i : Y.Opens) from ⟨hx, hi⟩) (U.1 ⊓ V i).2
      exact Opens.mem_iSup.mpr
        ⟨⟨⟨W, hW⟩, fun _ hy => (hWle hy).1, i, fun _ hy => (hWle hy).2⟩, hxW⟩
    · intro W
      have hW := h W.1 W.2.1 W.2.2
      rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hW
      change X.presheaf.map (homOfLE _).op (f.app U s) = X.presheaf.map (homOfLE _).op 0
      rw [map_zero, Scheme.Hom.app_restrict_eq f W.2.1 s]
      exact hW

/-- Two quasi-compact morphisms with the same target have the same kernel ideal sheaf as soon as their
kernel ideals agree on every affine open contained in a member of a covering family. -/
theorem Scheme.Hom.ker_eq_of_cover {X X' Y : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y) [QuasiCompact f]
    [QuasiCompact g] {ι : Type*} (V : ι → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (H : ∀ (i : ι) (W : Y.affineOpens), W.1 ≤ V i → f.ker.ideal W = g.ker.ideal W) :
    f.ker = g.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  ext s
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, RingHom.mem_ker, RingHom.mem_ker]
  change f.app U s = 0 ↔ g.app U s = 0
  rw [Scheme.Hom.app_eq_zero_iff_of_cover f V hV U s, Scheme.Hom.app_eq_zero_iff_of_cover g V hV U s]
  constructor
  · intro h W hWU hWV
    obtain ⟨i, hi⟩ := hWV
    rw [← H i W hi]
    exact h W hWU ⟨i, hi⟩
  · intro h W hWU hWV
    obtain ⟨i, hi⟩ := hWV
    rw [H i W hi]
    exact h W hWU ⟨i, hi⟩

end KltDP.Geometry

namespace KltDP.Examples.FrobeniusFiberZeroClass

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusGraphPicardClassCharts
  FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassZeroFiber
  FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassRulingDivisors
  FrobeniusGraphPicardClassCoordinateComparison FrobeniusGraphPicardClassMixedCoordinates
  FrobeniusGraphPicardClassFiberClasses FrobeniusGraphPicardClassFrames
  FrobeniusFiberClosure FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard
  FrobeniusFiberZeroInvertible

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-! ## The effective Cartier divisor of the fibre `y = 0` -/

/-- Local equations of the fibre `y = 0` on the two ruling opens of the second projection: the
coordinate `y` where `y` is finite, and `1` where `y ≠ 0`. -/
def fiberZeroEquation (i : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  if i = 0 then rulingCoordinateUnit 1 else 1

/-- The coordinate `y` is a regular unit on every common subopen of the two ruling opens. -/
theorem coordinate_cartier_class_zero (V : (projectiveProduct k).Opens) [Nonempty V]
    (h₀ : V ≤ rulingOpen 1 0) (h₁ : V ≤ rulingOpen 1 1) :
    cartierEquationClassHom (projectiveProduct k) V
      (Additive.ofMul (rulingCoordinateUnit (k := k) 1)) = 0 := by
  have h := reciprocal_cartier_class_zero (k := k) 1 V h₀ h₁
  rw [ofMul_inv, map_neg, neg_eq_zero] at h
  exact h

theorem fiberZeroEquation_compatible (i j : Fin 2) :
    cartierEquationClassHom (projectiveProduct k) (rulingOpen 1 i ⊓ rulingOpen 1 j)
        (Additive.ofMul (fiberZeroEquation i)) =
      cartierEquationClassHom (projectiveProduct k) (rulingOpen 1 i ⊓ rulingOpen 1 j)
        (Additive.ofMul (fiberZeroEquation j)) := by
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [fiberZeroEquation] using
      coordinate_cartier_class_zero (k := k) (rulingOpen 1 0 ⊓ rulingOpen 1 1) inf_le_left inf_le_right
  · simpa [fiberZeroEquation] using
      (coordinate_cartier_class_zero (k := k) (rulingOpen 1 1 ⊓ rulingOpen 1 0) inf_le_right
        inf_le_left).symm
  · rfl

/-- The two ruling opens cover the product (indexed in the lane's universe). -/
theorem fiberZero_cover :
    (⊤ : (projectiveProduct k).Opens) ≤ ⨆ i : ULift.{u} (Fin 2), rulingOpen 1 i.down := by
  intro x _
  have hx : x ∈ ⨆ i : Fin 2, rulingOpen (k := k) 1 i := by
    rw [rulingOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

/-- The effective Cartier divisor of the fibre `y = 0`. -/
def fiberZeroDivisor : CartierDivisor (projectiveProduct k) :=
  cartierDivisorOfEquations (projectiveProduct k) (fun i : ULift.{u} (Fin 2) => rulingOpen 1 i.down)
    fiberZero_cover (fun i => fiberZeroEquation i.down)
    (fun i j => fiberZeroEquation_compatible i.down j.down)

theorem fiberZeroDivisor_restrict_ruling (i : Fin 2) :
    cartierEquationClassHom (projectiveProduct k) (rulingOpen 1 i)
        (Additive.ofMul (fiberZeroEquation i)) =
      (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen (k := k) 1 i ≤ ⊤ from le_top)).op fiberZeroDivisor :=
  (cartierDivisorOfEquations_restrict (projectiveProduct k)
    (fun i : ULift.{u} (Fin 2) => rulingOpen 1 i.down) fiberZero_cover
    (fun i => fiberZeroEquation i.down) (fun i j => fiberZeroEquation_compatible i.down j.down)
    ⟨i⟩).symm

/-- `E_0 = R_∞ + div(y)`: the fibre `y = 0` differs from the ruling `y = ∞` by the principal divisor of
the coordinate `y`. -/
theorem fiberZeroDivisor_eq :
    fiberZeroDivisor (k := k) =
      rulingInfinityDivisor 1 +
        principalCartierDivisorHom (projectiveProduct k) (Additive.ofMul (rulingCoordinateUnit 1)) := by
  apply cartierDivisor_eq_of_restrict_eq (projectiveProduct k)
    (fun i : ULift.{u} (Fin 2) => rulingOpen 1 i.down) fiberZero_cover
  rintro ⟨i⟩
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen (k := k) 1 i ≤ ⊤ from le_top)).op fiberZeroDivisor =
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen (k := k) 1 i ≤ ⊤ from le_top)).op
      (rulingInfinityDivisor 1 +
        principalCartierDivisorHom (projectiveProduct k) (Additive.ofMul (rulingCoordinateUnit 1)))
  rw [← fiberZeroDivisor_restrict_ruling i, map_add, rulingInfinityDivisor_restrict,
    principalCartierDivisorHom, cartierEquationClassHom_restrict, ← map_add, ← ofMul_mul]
  fin_cases i
  · simp [fiberZeroEquation, rulingInfinityEquation]
  · simp [fiberZeroEquation, rulingInfinityEquation]

/-- The Cartier class of the fibre `y = 0` is the class of the ruling `y = ∞`, i.e. `b`. -/
theorem fiberZeroDivisor_picard :
    cartierPicardHom (projectiveProduct k) (fiberZeroDivisor (k := k)) =
      cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 1) := by
  rw [fiberZeroDivisor_eq, map_add, cartierPicardHom_principal, add_zero]

/-! ## Regular equations on the four product charts -/

theorem productOpen_le_rulingOpen (i j : Fin 2) : productOpen (k := k) i j ≤ rulingOpen 1 j :=
  productOpen_le_rulingChart 1 i j

/-- On the chart `(i, 0)` the divisor has equation `y` with regular coefficient the chart coordinate
`v` (BRIEF17's `fiberZeroChartEquation`). -/
def fiberZeroChartZero (i : Fin 2) :
    RegularCartierEquationChart (projectiveProduct k) (fiberZeroDivisor (k := k)) where
  chart :=
    { openSet := productOpen i 0
      nonempty := productOpen_nonempty i 0
      equation := rulingCoordinateUnit 1
      represents := cartierGlobalEquation_restrict (projectiveProduct k) fiberZeroDivisor
        (homOfLE (productOpen_le_rulingOpen i 0)) (rulingCoordinateUnit 1)
        (fiberZeroDivisor_restrict_ruling 0) }
  coefficient := fiberZeroChartEquation i
  germ_eq := by
    change productFunctionFieldMap (k := k) i 0 vCoord = rulingLeft 1
    rw [productFunctionFieldMap_v, rulingCoordinate_zero]

/-- On the chart `(i, 1)` the divisor has equation and coefficient `1`. -/
def fiberZeroChartOne (i : Fin 2) :
    RegularCartierEquationChart (projectiveProduct k) (fiberZeroDivisor (k := k)) where
  chart :=
    { openSet := productOpen i 1
      nonempty := productOpen_nonempty i 1
      equation := 1
      represents := cartierGlobalEquation_restrict (projectiveProduct k) fiberZeroDivisor
        (homOfLE (productOpen_le_rulingOpen i 1)) 1 (fiberZeroDivisor_restrict_ruling 1) }
  coefficient := 1
  germ_eq := by simp

theorem mem_productOpen_of_mem_range (i j : Fin 2) (x : projectiveProduct k)
    (hx : x ∈ Set.range (productChart (k := k) i j).base) : x ∈ productOpen (k := k) i j := by
  rw [productOpen, Scheme.Hom.image_top_eq_opensRange]
  exact hx

theorem fiberZeroDivisor_hasRegularEquations :
    HasRegularCartierEquations (projectiveProduct k) (fiberZeroDivisor (k := k)) := by
  intro x
  obtain ⟨i, j, hx⟩ := productCharts_cover x
  have hx' := mem_productOpen_of_mem_range i j x hx
  fin_cases j
  · exact ⟨fiberZeroChartZero i, hx'⟩
  · exact ⟨fiberZeroChartOne i, hx'⟩

/-! ## The ideal sheaf of the divisor is the ideal sheaf of the fibre -/

/-- The Cartier ideal and the fibre kernel agree on each of the four product charts. -/
theorem fiberZero_chart_ideal_eq (i j : Fin 2) :
    (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k) fiberZeroDivisor
        fiberZeroDivisor_hasRegularEquations).ideal (fiberChartAffineOpen (k := k) i j) =
      (horizontalFiberMorphism (0 : k)).ker.ideal (fiberChartAffineOpen i j) := by
  fin_cases j
  · exact (effectiveCartierIdealDataOfRegularEquations_ideal_chart (projectiveProduct k)
      fiberZeroDivisor fiberZeroDivisor_hasRegularEquations (fiberZeroChartZero i)
      (fiberChartAffineOpen (k := k) i 0).2).trans (horizontalFiber_ideal_chart_zero i).symm
  · exact (effectiveCartierIdealDataOfRegularEquations_ideal_chart (projectiveProduct k)
      fiberZeroDivisor fiberZeroDivisor_hasRegularEquations (fiberZeroChartOne i)
      (fiberChartAffineOpen (k := k) i 1).2).trans (horizontalFiber_ideal_chart_one i).symm

/-- The ideal sheaf of the effective Cartier divisor `y = 0` is the kernel of the fibre `y = 0`. -/
theorem fiberZeroIdealData_eq :
    effectiveCartierIdealDataOfRegularEquations (projectiveProduct k) fiberZeroDivisor
        fiberZeroDivisor_hasRegularEquations =
      (horizontalFiberMorphism (0 : k)).ker := by
  rw [← effectiveCartierIdealDataOfRegularEquations_ker (projectiveProduct k) fiberZeroDivisor
    fiberZeroDivisor_hasRegularEquations, horizontalFiber_ker_eq 0]
  apply Scheme.Hom.ker_eq_of_cover _ _
    (fun ij : Fin 2 × Fin 2 => (fiberChartAffineOpen (k := k) ij.1 ij.2).1)
  · intro y
    obtain ⟨i, j, hy⟩ := productCharts_cover y
    exact ⟨(i, j), mem_fiberChartAffineOpen_of_mem_range i j y hy⟩
  · rintro ⟨i, j⟩ W hW
    dsimp only at hW
    rw [effectiveCartierIdealDataOfRegularEquations_ker, ← horizontalFiber_ker_eq 0,
      ← Scheme.IdealSheafData.map_ideal _ hW, ← Scheme.IdealSheafData.map_ideal _ hW,
      fiberZero_chart_ideal_eq i j]

/-! ## Picard classes -/

/-- The kernel module of the stage-`0` strict fibre, as an invertible sheaf on `P¹ × P¹`. -/
def fiberZeroLine : InvertibleSheaf (projectiveProduct k) :=
  ⟨schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) 0),
    fiberKernel_zero_isInvertible⟩

/-- `O(−E_0)` is the kernel module of the stage-`0` strict fibre. -/
def fiberZeroKernelIso :
    cartierDivisorModule (projectiveProduct k) (-fiberZeroDivisor) ≅ (fiberZeroLine (k := k)).obj :=
  effectiveCartierKernelIso (projectiveProduct k) fiberZeroDivisor
      fiberZeroDivisor_hasRegularEquations ≪≫
    eqToIso (congrArg (fun I : (projectiveProduct k).IdealSheafData => schemeKernelIdeal I.gluedTo)
      (fiberZeroIdealData_eq.trans fiberStrictIdeal_zero.symm))

theorem fiberZeroLine_toPic :
    (fiberZeroLine (k := k)).toPic = cartierPicardClass (projectiveProduct k) (-fiberZeroDivisor) := by
  letI := Scheme.Modules.monoidalCategory (projectiveProduct k)
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, cartierPicardClass_val]
  exact Quotient.sound ⟨fiberZeroKernelIso.symm⟩

theorem fiberKernelLine_zero_toPic :
    @Eq (projectiveProduct k).Pic (fiberKernelLine (fiberKernel_zero_isInvertible (k := k)) 0).toPic
      (fiberZeroLine (k := k)).toPic :=
  rfl

/-- **`F_0 = b`**: the class of the stage-`0` strict fibre `y = 0` is the accepted second fibre class. -/
theorem fiberPicardClass_zero_eq_secondFiberClass :
    fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) 0 = secondFiberClass := by
  have hdef : cartierPicardHom (projectiveProduct k) (fiberZeroDivisor (k := k)) =
      Additive.ofMul (cartierPicardClass (projectiveProduct k) fiberZeroDivisor) := rfl
  unfold fiberPicardClass
  rw [fiberKernelLine_zero_toPic, fiberZeroLine_toPic, cartierPicardClass_neg, ofMul_inv, neg_neg,
    secondFiberClass_eq_ruling, ← fiberZeroDivisor_picard, hdef]
  rfl

/-- The total transform of `F_0` is the pull-back of `b`. -/
theorem fiberTotalClass_eq_pullback_secondFiberClass (N : ℕ) :
    fiberTotalClass (fiberKernel_zero_isInvertible (k := k)) N =
      (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) (Nat.zero_le N))).toAdditive
        secondFiberClass := by
  unfold fiberTotalClass
  rw [fiberPicardClass_zero_eq_secondFiberClass]

end KltDP.Examples.FrobeniusFiberZeroClass

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard
  FrobeniusGraphPicardClassFiberClasses FrobeniusGlobalBlowupStages
  FrobeniusExceptionalFinalConfiguration FrobeniusFiberZeroInvertible FrobeniusFiberZeroClass

/-- Bundle: `F_0 = b` in `Additive (P¹ × P¹).Pic`. -/
theorem f29_fiber_zero_class (k : Type u) [Field k] :
    fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) 0 = secondFiberClass :=
  fiberPicardClass_zero_eq_secondFiberClass

/-- Bundle (manuscript normalisation): on every stage `N + 1` of the origin contact tower,
`π^*b = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P` in `Additive Pic`. -/
theorem f29_tower_fiber_picard_relation_b (k : Type u) [Field k] :
    ∀ N : ℕ,
      (schemePicardPullbackHom (between (projectiveProductInitial (k := k))
          (Nat.zero_le (N + 1)))).toAdditive secondFiberClass =
        fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (N + 1) +
          ∑ j : Fin N, (j.val + 1) • oldExceptionalStrictClass (k := k) (N + 1) j.val (by omega) +
            (N + 1) • totalExceptionalClass (N + 1) (Fin.last N) := by
  intro N
  rw [← fiberTotalClass_eq_pullback_secondFiberClass]
  exact f29_tower_fiber_picard_relation' k N

/-- The bundles have exactly one universe parameter. -/
theorem f29_fiber_zero_class_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_fiber_zero_class.{u} k
  have _ := f29_tower_fiber_picard_relation_b.{u} k
  trivial

end KltDP.Examples
