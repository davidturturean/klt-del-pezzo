import KltDP.Geometry.Positivity
import KltDP.Geometry.CurveConeReal
import KltDP.Geometry.CartierPicardComparison
import KltDP.Compatibility.GrothendieckVanishing.TopologicalKrullDim
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Numerical one-cycles `N₁(Y)_ℝ` and the real Picard number `ρ(Y)`

This is the vocabulary of Tanaka, *Minimal model program for excellent surfaces*, Annales de
l'Institut Fourier 68 (2018), §2.3 (extracted text lines 540–556), specialised to the base
`B = S = Spec k` of a field `k` and to a scheme `Y` with a structure morphism
`g : Y ⟶ Spec k` (the intended use is `IsProjectiveOverField g`, Tanaka's "quasi-projective
`B`-scheme", but nothing below needs it):

* `Curves Y`: the integral closed subschemes of dimension one, i.e. the irreducible closed
  subsets `Z ⊆ Y` with `topologicalKrullDim Z = 1` (with their reduced induced structure).
  For `S = Spec k` every such subscheme is a projective `k`-curve when `Y` is projective over
  `k`, and the condition "`π(C)` is one point" is automatic. This is Tanaka's index set of
  `Z(X/S)_ℝ`. For an actual normal projective surface `S` this type is *definitionally*
  `S.PrimeCurve` (`curves_eq_primeCurve`).
* `OneCycles Y = Z(Y/Spec k)_ℝ := ⨁_C ℝ C` (a `Finsupp`).
* `degreeFunctional g L : Γ ↦ L · Γ = Σ_C Γ_C · (L · C)`, where `L · C` is
  `Positivity.subvarietyDegree g L C`. **Source check for the degree**: Tanaka, Definition 2.6
  (extracted text lines 446–460) defines `deg_k M` for an invertible sheaf `M` on a projective
  curve `C` over `k` as the coefficient of `m` in the polynomial `χ(C, mM) ∈ ℤ[m]` (of degree at
  most one), and `L · C := deg_k (L|_C)`. The accepted `Positivity.subvarietyDegree g L Z` is
  `χ(Z, L|_Z) − χ(Z, O_Z)` (Stacks 0AYR). Since `χ(C, mM)` is a polynomial of degree `≤ 1` in
  `m` with constant term `χ(C, O_C)` (its value at `m = 0`), its coefficient of `m` equals
  `χ(C, M) − χ(C, O_C)`, i.e. the two definitions agree on the nose. On a prime curve of a
  surface this is the accepted restriction degree `C.restrictionDegree L`
  (`Positivity.subvarietyDegree_eq_restrictionDegree`, a `rfl`).
* `numericallyTrivial g`: the cycles `Γ` with `L · Γ = 0` for every invertible sheaf `L` on `Y`
  (Tanaka: `Γ₁ ≡ Γ₂ ↔ L · Γ₁ = L · Γ₂` for any invertible sheaf `L` on `X`), a submodule.
* `N₁ℝ Y g := OneCycles Y ⧸ numericallyTrivial g` (Tanaka's `N(X/S)_ℝ := Z(X/S)_ℝ / ≡`), and
  `rhoReal Y g := dim_ℝ N₁ℝ Y g` (Tanaka's `ρ(X/S)`).

## Main results

* `rhoReal_eq_picardRank`: for an actual normal projective surface `S` over an algebraically
  closed field with `N¹(S)_ℚ = S.NumericalClassGroup` finite dimensional,
  `rhoReal S = S.picardRank`. The pairing `Γ ↦ (d ↦ Σ_C Γ_C (d · C))` identifies `N₁(S)_ℝ` with
  the space of real-valued `ℚ`-linear functionals on `N¹(S)_ℚ`: its kernel is exactly the
  numerically trivial cycles (`ker_pairingMap`, because every rational numerical class is a
  rational combination of classes of invertible sheaves), and it is surjective
  (`range_pairingMap`) because the curve tests separate `N¹(S)_ℚ`
  (`numericalClass_eq_zero_iff`, through the double dual of the finite dimensional
  `N¹(S)_ℚ`). The target has real dimension `dim_ℚ N¹(S)_ℚ = S.picardRank`
  (`Basis.constr`).
* `rhoReal_le_one_of_dim_le_one`: an irreducible (e.g. integral) scheme of topological Krull
  dimension `≤ 1` has `rhoReal ≤ 1`: its only possible curve is the whole space.
* `pairingMap_single`: the compatibility with the Euclidean model of `KltDP.Geometry.CurveCone`:
  the class of a prime curve `C` corresponds to the functional
  `d ↦ pairReal S hreg d (curveClassReal S hreg C)`. Hence the identification
  `N₁(S)_ℝ ≅ (N¹(S)_ℚ →ₗ[ℚ] ℝ) ≅ V S` (the last through the real extension of the perfect
  intersection pairing) sends `[C]` to `curveClassReal S hreg C`, `NE(S)` to `effectiveCone` and
  `NE(S)‾` to `closedCurveCone`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.NumericalOneCycles

section Definitions

variable (Y : Scheme.{u})

/-- The projective curves on `Y`: irreducible closed subsets of dimension one (Tanaka's
projective `S`-curves `C ⊆ X` for `S = Spec k`; the condition that the image in `S` is a point is
automatic). Definitionally `S.PrimeCurve` for a normal projective surface `S`. -/
def Curves := {Z : IrreducibleCloseds Y // topologicalKrullDim (Z : Set Y) = 1}

/-- Real one-cycles `Z(Y/Spec k)_ℝ = ⨁_C ℝ C`. -/
abbrev OneCycles := Curves Y →₀ ℝ

variable {k : Type u} [Field k] (g : Y ⟶ Spec (CommRingCat.of k))

/-- The degree `L · Γ = Σ_C Γ_C · deg(L|_C)` of an invertible sheaf on a one-cycle (Tanaka,
Definition 2.6 extended linearly; `deg` is `Positivity.subvarietyDegree`). -/
def degreeFunctional (L : InvertibleSheaf Y) : OneCycles Y →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun Z : Curves Y => (Positivity.subvarietyDegree g L Z.1 : ℝ)

theorem degreeFunctional_apply (L : InvertibleSheaf Y) (Γ : OneCycles Y) :
    degreeFunctional Y g L Γ =
      Γ.sum fun Z a => a * (Positivity.subvarietyDegree g L Z.1 : ℝ) := by
  simp only [degreeFunctional, Finsupp.linearCombination_apply, smul_eq_mul]

theorem degreeFunctional_single (L : InvertibleSheaf Y) (Z : Curves Y) (a : ℝ) :
    degreeFunctional Y g L (Finsupp.single Z a) =
      a * (Positivity.subvarietyDegree g L Z.1 : ℝ) := by
  simp only [degreeFunctional, Finsupp.linearCombination_single, smul_eq_mul]

/-- Numerically trivial one-cycles: `L · Γ = 0` for every invertible sheaf `L` on `Y`. -/
def numericallyTrivial : Submodule ℝ (OneCycles Y) :=
  ⨅ L : InvertibleSheaf Y, LinearMap.ker (degreeFunctional Y g L)

theorem mem_numericallyTrivial_iff (Γ : OneCycles Y) :
    Γ ∈ numericallyTrivial Y g ↔ ∀ L : InvertibleSheaf Y, degreeFunctional Y g L Γ = 0 := by
  simp only [numericallyTrivial, Submodule.mem_iInf, LinearMap.mem_ker]

/-- `N₁(Y/Spec k)_ℝ = Z(Y/Spec k)_ℝ / ≡`. -/
abbrev N₁ℝ := OneCycles Y ⧸ numericallyTrivial Y g

/-- `ρ(Y/Spec k) = dim_ℝ N₁(Y)_ℝ` (Tanaka's `ρ(X/S)`; `Module.finrank` returns `0` if the space is
infinite dimensional). -/
def rhoReal : ℕ := Module.finrank ℝ (N₁ℝ Y g)

end Definitions

/-! ### Schemes of dimension at most one -/

section LowDimension

variable (Y : Scheme.{u}) [IrreducibleSpace Y]

/-- On an irreducible space of dimension `≤ 1` the only curve is the whole space. -/
theorem curve_eq_univ_of_dim_le_one (hdim : topologicalKrullDim Y ≤ 1) (Z : Curves Y) :
    (Z.1 : Set Y) = Set.univ := by
  by_contra hne
  have hfin : topologicalKrullDim (Z.1 : Set Y) < ⊤ := by
    rw [Z.2]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top 1)
  have hlt := topologicalKrullDim_lt_of_isIrreducible_of_isClosed (X := Y) Z.1.isClosed hne hfin
  rw [Z.2] at hlt
  exact lt_irrefl _ (hlt.trans_le hdim)

theorem subsingleton_curves_of_dim_le_one (hdim : topologicalKrullDim Y ≤ 1) :
    Subsingleton (Curves Y) :=
  ⟨fun Z W => Subtype.ext (IrreducibleCloseds.ext
    ((curve_eq_univ_of_dim_le_one Y hdim Z).trans (curve_eq_univ_of_dim_le_one Y hdim W).symm))⟩

variable {k : Type u} [Field k] (g : Y ⟶ Spec (CommRingCat.of k))

/-- An irreducible scheme of dimension at most one (a point or an integral curve) has
`ρ ≤ 1`. -/
theorem rhoReal_le_one_of_dim_le_one (hdim : topologicalKrullDim Y ≤ 1) : rhoReal Y g ≤ 1 := by
  haveI := subsingleton_curves_of_dim_le_one Y hdim
  haveI : Finite (Curves Y) := Finite.of_subsingleton
  letI : Fintype (Curves Y) := Fintype.ofFinite _
  calc rhoReal Y g ≤ Module.finrank ℝ (OneCycles Y) := Submodule.finrank_quotient_le _
    _ = Fintype.card (Curves Y) := Module.finrank_finsupp_self ℝ
    _ ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance

end LowDimension

/-! ### Normal projective surfaces: `ρ(S) = dim N¹(S)_ℚ` -/

section Surface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

theorem curves_eq_primeCurve : Curves S.toScheme = S.PrimeCurve := rfl

/-- The degree along a prime curve as a real-valued `ℚ`-linear functional on `N¹(S)_ℚ`. -/
def realDegree (C : S.PrimeCurve) : S.NumericalClassGroup →ₗ[ℚ] ℝ :=
  (Algebra.linearMap ℚ ℝ).comp (S.numericalRestrictionDegree C)

theorem realDegree_apply (C : S.PrimeCurve) (d : S.NumericalClassGroup) :
    realDegree S C d = (S.numericalRestrictionDegree C d : ℝ) := by
  simp only [realDegree, LinearMap.comp_apply, Algebra.linearMap_apply]
  exact eq_ratCast _ _

/-- The pairing `Γ ↦ (d ↦ Σ_C Γ_C (d · C))` from one-cycles to real functionals on
`N¹(S)_ℚ`. -/
def pairingMap : OneCycles S.toScheme →ₗ[ℝ] (S.NumericalClassGroup →ₗ[ℚ] ℝ) :=
  Finsupp.linearCombination ℝ fun C : Curves S.toScheme => realDegree S C

theorem pairingMap_apply (Γ : OneCycles S.toScheme) (d : S.NumericalClassGroup) :
    pairingMap S Γ d = Γ.sum fun C a => a * (S.numericalRestrictionDegree C d : ℝ) := by
  simp only [pairingMap, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply,
    LinearMap.smul_apply, realDegree_apply, smul_eq_mul]

/-- The degree functional of an invertible sheaf is the pairing with its numerical class. -/
theorem degreeFunctional_eq_pairingMap (L : InvertibleSheaf S.toScheme) (Γ : OneCycles S.toScheme) :
    degreeFunctional S.toScheme S.structureMorphism L Γ =
      pairingMap S Γ (S.picardNumericalMap (Additive.ofMul L.toPic)) := by
  rw [degreeFunctional_apply, pairingMap_apply]
  refine Finsupp.sum_congr fun C _ => ?_
  rw [S.numericalRestrictionDegree_picardNumericalMap, toMul_ofMul,
    PrimeCurve.picardRestrictionDegree_toPic, Rat.cast_intCast]
  rfl

/-- The kernel of the pairing is exactly the numerically trivial cycles. -/
theorem ker_pairingMap :
    LinearMap.ker (pairingMap S) = numericallyTrivial S.toScheme S.structureMorphism := by
  ext Γ
  rw [LinearMap.mem_ker, mem_numericallyTrivial_iff]
  constructor
  · intro h L
    rw [degreeFunctional_eq_pairingMap, h, LinearMap.zero_apply]
  · intro h
    apply LinearMap.ext
    intro d
    rw [LinearMap.zero_apply]
    obtain ⟨v, rfl⟩ := S.rationalPicardNumericalMap_surjective d
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a p =>
        have hp : ((a ⊗ₜ[ℤ] p : S.RationalPicard)) = a • ((1 : ℚ) ⊗ₜ[ℤ] p) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hp, map_smul, map_smul]
        obtain ⟨D, hD⟩ := cartierPicardClass_surjective S.toScheme p.toMul
        have hL := h (cartierDivisorInvertibleSheaf S.toScheme D)
        rw [degreeFunctional_eq_pairingMap] at hL
        have hp' : Additive.ofMul (cartierDivisorInvertibleSheaf S.toScheme D).toPic = p := by
          change Additive.ofMul (cartierPicardClass S.toScheme D) = p
          rw [hD]
          exact ofMul_toMul p
        rw [hp', picardNumericalMap_apply] at hL
        rw [hL, smul_zero]
    | add v w hv hw => rw [map_add, map_add, hv, hw, add_zero]

/-- The curve tests span the `ℚ`-dual of `N¹(S)_ℚ` (they separate points and `N¹(S)_ℚ` is
finite dimensional). -/
theorem span_numericalRestrictionDegree_eq_top [FiniteDimensional ℚ S.NumericalClassGroup] :
    Submodule.span ℚ (Set.range S.numericalRestrictionDegree) = ⊤ := by
  by_contra hne
  obtain ⟨F, hF0, hF⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  obtain ⟨d, rfl⟩ := (Module.evalEquiv ℚ S.NumericalClassGroup).surjective F
  apply hF0
  rw [(Module.evalEquiv ℚ S.NumericalClassGroup).map_eq_zero_iff, S.numericalClass_eq_zero_iff]
  intro C
  have hmem : S.numericalRestrictionDegree C ∈
      Submodule.span ℚ (Set.range S.numericalRestrictionDegree) :=
    Submodule.subset_span ⟨C, rfl⟩
  have h0 : Module.evalEquiv ℚ S.NumericalClassGroup d (S.numericalRestrictionDegree C) = 0 := by
    rw [← Submodule.mem_bot ℚ, ← hF]
    exact Submodule.mem_map_of_mem hmem
  simpa using h0

/-- Every real functional on `N¹(S)_ℚ` is a real combination of curve tests. -/
theorem mem_span_realDegree [FiniteDimensional ℚ S.NumericalClassGroup]
    (φ : S.NumericalClassGroup →ₗ[ℚ] ℝ) :
    φ ∈ Submodule.span ℝ (Set.range (realDegree S)) := by
  classical
  set W := Submodule.span ℝ (Set.range (realDegree S)) with hW
  have hA : ∀ ψ : Module.Dual ℚ S.NumericalClassGroup, (Algebra.linearMap ℚ ℝ).comp ψ ∈ W := by
    intro ψ
    have hψ : ψ ∈ Submodule.span ℚ (Set.range S.numericalRestrictionDegree) := by
      rw [span_numericalRestrictionDegree_eq_top]
      exact Submodule.mem_top
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨C, rfl⟩ := hx
        exact Submodule.subset_span ⟨C, rfl⟩
    | zero =>
        rw [LinearMap.comp_zero]
        exact W.zero_mem
    | add x y _ _ hx hy =>
        rw [LinearMap.comp_add]
        exact W.add_mem hx hy
    | smul q x _ hx =>
        have hsmul : (Algebra.linearMap ℚ ℝ).comp (q • x) =
            (q : ℝ) • (Algebra.linearMap ℚ ℝ).comp x := by
          apply LinearMap.ext
          intro d
          simp only [LinearMap.comp_apply, LinearMap.smul_apply, Algebra.linearMap_apply,
            smul_eq_mul, map_mul]
          rw [eq_ratCast]
        rw [hsmul]
        exact W.smul_mem _ hx
  let b := Module.finBasis ℚ S.NumericalClassGroup
  have hφ : φ = ∑ i, φ (b i) • (Algebra.linearMap ℚ ℝ).comp (b.coord i) := by
    apply b.ext
    intro i
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Algebra.linearMap_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hφ]
  exact W.sum_mem fun i _ => W.smul_mem _ (hA _)

theorem range_pairingMap [FiniteDimensional ℚ S.NumericalClassGroup] :
    LinearMap.range (pairingMap S) = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  rw [pairingMap, Finsupp.range_linearCombination]
  exact mem_span_realDegree S φ

/-- The space of real-valued `ℚ`-linear functionals on `N¹(S)_ℚ` has real dimension
`ρ(S) = dim_ℚ N¹(S)_ℚ`. -/
theorem finrank_realDual [FiniteDimensional ℚ S.NumericalClassGroup] :
    Module.finrank ℝ (S.NumericalClassGroup →ₗ[ℚ] ℝ) = S.picardRank := by
  let b := Module.finBasis ℚ S.NumericalClassGroup
  rw [← (b.constr ℝ (M' := ℝ)).finrank_eq, Module.finrank_fin_fun]
  rfl

/-- **`ρ(S/Spec k) = ρ(S)`**: Tanaka's real Picard number of an actual normal projective surface
equals the dimension of the accepted numerical quotient `N¹(S)_ℚ`. -/
theorem rhoReal_eq_picardRank [FiniteDimensional ℚ S.NumericalClassGroup] :
    rhoReal S.toScheme S.structureMorphism = S.picardRank := by
  have e1 : N₁ℝ S.toScheme S.structureMorphism ≃ₗ[ℝ]
      (OneCycles S.toScheme ⧸ LinearMap.ker (pairingMap S)) :=
    Submodule.quotEquivOfEq _ _ (ker_pairingMap S).symm
  have e2 := (pairingMap S).quotKerEquivOfSurjective
    (LinearMap.range_eq_top.mp (range_pairingMap S))
  unfold rhoReal
  rw [e1.finrank_eq, e2.finrank_eq, finrank_realDual]

/-! ### Compatibility with the Euclidean model `V S` of `N¹(S)_ℝ` -/

variable (hreg : ∀ x : S.Point, RegularPoint S.toScheme x)
  [FiniteDimensional ℚ S.NumericalClassGroup]

/-- Pairing a numerical class with the real class of a prime curve is the degree along that
curve. -/
theorem pairReal_curveClassReal (d : S.NumericalClassGroup) (C : S.PrimeCurve) :
    CurveCone.pairReal S hreg d (CurveCone.curveClassReal S hreg C) =
      (S.numericalRestrictionDegree C d : ℝ) := by
  rw [CurveCone.curveClassReal, CurveCone.pairReal_toReal,
    DisjointNegativeCurvesRank.pairing_curveClass]

/-- The class of a prime curve in `N₁(S)_ℝ` is, under the pairing, the functional
`d ↦ pairReal d (curveClassReal C)`: the identification `N₁(S)_ℝ ≅ V S` sends `[C]` to
`curveClassReal S hreg C`. -/
theorem pairingMap_single (C : S.PrimeCurve) (d : S.NumericalClassGroup) :
    pairingMap S (Finsupp.single C 1) d =
      CurveCone.pairReal S hreg d (CurveCone.curveClassReal S hreg C) := by
  rw [pairReal_curveClassReal, pairingMap_apply, Finsupp.sum_single_index (by simp), one_mul]

end Surface

end KltDP.Geometry.NumericalOneCycles

#print axioms KltDP.Geometry.NumericalOneCycles.rhoReal_eq_picardRank
#print axioms KltDP.Geometry.NumericalOneCycles.rhoReal_le_one_of_dim_le_one
#print axioms KltDP.Geometry.NumericalOneCycles.pairingMap_single
