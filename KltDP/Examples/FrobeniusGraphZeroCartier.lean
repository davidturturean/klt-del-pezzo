import KltDP.Examples.FrobeniusGraphPicardClassFullCover
import KltDP.Examples.FrobeniusGraphPicardClassAffine
import KltDP.Geometry.GluedSubschemeStalkKernel
import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal

/-!
# The graph `Γ : v = u^p` as an effective Cartier divisor on `P¹ × P¹`

BRIEF37 asks for the Cartier identity `π^*Γ = B̃ + Σ_j E_j^tot` on the origin tower.  Its fibre
analogue `f29_tower_fiber_relation` begins from `fiberZeroDivisor`, an effective Cartier divisor of
the fibre `y = 0` on `P¹ × P¹` **with regular equations**, because that is exactly the input the
generic `pullbackDivisor` consumes.  The graph had no such divisor: `graphIdealCartierDivisor` is
produced by choice from a line bundle and `graphDivisorCandidate` is a *difference* of divisors,
whose equations are known only on the two diagonal opens — and those, as
`FrobeniusGraphPicardClassLocalEquations` records, do not cover the product.

This module supplies the missing base input, by the same route as the strict fibre
(`fiberStrictDivisor`): the accepted graph ideal sheaf `graphIdeal p = (projectiveGraphMorphism p).ker`
is shown **locally principal with regular generators**, and `cartierDivisorOfIdeal` then produces the
divisor together with its regular equations for free.

The cover is the accepted `comparisonOpen` of `FrobeniusGraphPicardClassFullCover` — the two diagonal
opens and the two companion basic opens `D(1 - u^p v)`:

* on `diagonalAffineOpen i` the generator is the accepted `diagonalSection p i`
  (`diagonalSection_ideal`), regular because the product is integral (transported from the accepted
  `diagonalEquation_regular` through the top-section isomorphism);
* each companion open is a basic open of an affine product chart, hence affine, and is **disjoint
  from the graph** (accepted `mixedEquation_basicOpen_disjoint_graph`), so the ideal there is the unit
  ideal by the accepted `ker_ideal_eq_top_of_disjoint` and the generator is `1`.

Nothing here asserts the tower identity; this is its base-level prerequisite.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusGraphZeroCartier

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusBlowupContact
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassFullCover FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassMixedSections
open FrobeniusGraphPicardClassMixedVanishing FrobeniusGraphPicardClassPowerCharts

variable {k : Type u} [Field k]

local instance graphProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- Nonzerodivisors are preserved by a ring isomorphism (the accepted helper of
`FrobeniusFiberStrictCartier`, restated to avoid importing the fibre tower). -/
private theorem regular_of_iso' {R S : CommRingCat.{u}} (i : R ≅ S) (g : R)
    (hg : g ∈ nonZeroDivisors R) : i.hom g ∈ nonZeroDivisors S := by
  let σ := i.commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := σ.symm) σ.symm.injective
  change σ.symm (σ g) ∈ nonZeroDivisors R
  simpa only [σ.symm_apply_apply] using hg

/-! ### The diagonal opens -/

/-- The accepted diagonal generator is a nonzerodivisor of the ambient section ring. -/
theorem diagonalSection_regular (p : ℕ) (i : Fin 2) :
    diagonalSection (k := k) p i ∈
      nonZeroDivisors Γ(projectiveProduct k, diagonalOpen (k := k) i) := by
  have h := regular_of_iso' ((diagonalOpen (k := k) i).topIso) (diagonalEquation p i)
    (diagonalEquation_regular p i)
  rwa [diagonalEquation, Iso.inv_hom_id_apply] at h

/-! ### The companion opens -/

/-- Every product chart is an affine open (as `diagonalAffineOpen` records for the diagonal ones). -/
theorem productOpen_isAffineOpen (i j : Fin 2) :
    IsAffineOpen (productOpen (k := k) i j) :=
  (isAffineOpen_top (Spec (CommRingCat.of (planeRing k)))).image_of_isOpenImmersion
    (productChart i j)

/-- The companion open is a basic open of an affine product chart, hence affine. -/
def companionAffineOpen (p : ℕ) (i : Fin 2) : (projectiveProduct k).affineOpens :=
  ⟨companionOpen p i, (productOpen_isAffineOpen i (otherIndex i)).basicOpen _⟩

/-- The graph misses the companion open, so the graph ideal is the unit ideal there. -/
theorem graphIdeal_companion (p : ℕ) (i : Fin 2) :
    (graphIdeal (k := k) p).ideal (companionAffineOpen p i) =
      Ideal.span {(1 : Γ(projectiveProduct k, (companionAffineOpen (k := k) p i).1))} := by
  rw [Ideal.span_singleton_one]
  exact ker_ideal_eq_top_of_disjoint (projectiveGraphMorphism p) (companionAffineOpen p i)
    (fun z hz => Set.disjoint_left.mp (mixedEquation_basicOpen_disjoint_graph p i) hz ⟨z, rfl⟩)

/-! ### The graph ideal is locally principal with regular generators -/

/-- **The graph ideal sheaf is locally principal with regular generators.** -/
theorem graphIdeal_locallyPrincipalRegular (p : ℕ) :
    IdealLocallyPrincipalRegular (graphIdeal (k := k) p) := by
  intro x
  obtain ⟨a, ha⟩ := comparisonOpens_cover p x
  cases a with
  | inl i =>
    exact ⟨diagonalAffineOpen i, ha, diagonalSection p i, diagonalSection_ideal p i,
      diagonalSection_regular p i⟩
  | inr i =>
    exact ⟨companionAffineOpen p i, ha, 1, graphIdeal_companion p i, Submonoid.one_mem _⟩

/-! ### The effective Cartier divisor of the graph -/

/-- **The graph `v = u^p` as an effective Cartier divisor on `P¹ × P¹`.** -/
def graphZeroDivisor (p : ℕ) : CartierDivisor (projectiveProduct k) :=
  cartierDivisorOfIdeal (projectiveProduct k) (graphIdeal p) (graphIdeal_locallyPrincipalRegular p)

/-- It has regular equations, which is what the generic Cartier pullback consumes. -/
theorem graphZeroDivisor_hasRegularEquations (p : ℕ) :
    HasRegularCartierEquations (projectiveProduct k) (graphZeroDivisor (k := k) p) :=
  cartierDivisorOfIdeal_hasRegularEquations _ _ _

/-- Its zero scheme is the graph: the ideal-sheaf data is the accepted `graphIdeal`. -/
theorem graphZeroDivisor_idealData (p : ℕ) :
    effectiveCartierIdealDataOfRegularEquations (projectiveProduct k) (graphZeroDivisor p)
        (graphZeroDivisor_hasRegularEquations p) =
      graphIdeal (k := k) p :=
  cartierDivisorOfIdeal_idealData _ _ _

end KltDP.Examples.FrobeniusGraphZeroCartier
