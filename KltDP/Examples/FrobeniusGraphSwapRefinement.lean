import KltDP.Geometry.ProjectiveLineComparison
import KltDP.Geometry.ProjectiveLineTransitionExtension
import KltDP.Examples.FrobeniusBlowupContact
import KltDP.Examples.FrobeniusBlowupSmooth
import KltDP.Examples.FrobeniusBlowupChartIteration
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusProductPlaneChart
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import KltDP.Examples.FrobeniusGraphPicardClassSwap
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents

/-!
# The swapped graph section refines the diagonal atlas

The `a`-row of the F29 table is, by `FrobeniusGraphFirstRulingSwap`, the exponent of the accepted
`graphIdealLine 0` pulled back along the **swapped section**
`projectiveGraphMorphism p ≫ (productSwapIso).inv` (the curve `t ↦ (t^p, t)`). To feed that into the
accepted exponent machinery — `ProjectiveLineCocycleRefinement.exponent_pullback_eq_of_monomial`,
which is generic in the section — one needs the refinement hypothesis: each standard open of `P¹`
lands in the preimage of the corresponding diagonal chart of `P¹ ×_k P¹`.

The accepted tree proves this for the *unswapped* section
(`FrobeniusStrictTransformFiberRowsExponents.chartOpen_le_preimage_diagonal`, through
`curveInPlane_diagonalChart`), but nothing there relates `productSwapIso` to `productChart` or
`diagonalOpen`: `FrobeniusGraphPicardClassSwap` relates it only to `rulingProjection` and
`chartOpen`. That bridge is supplied here, and it is the only new geometry involved.

The bridge is the accepted plane coordinate exchange **`FrobeniusBlowupSmooth.coordinateSwap`**
(`planeRing k ≃ₐ[k] planeRing k`, with `coordinateSwap_u`, `coordinateSwap_v`,
`coordinateSwap_constants`). No new swap is constructed:

* `coordinateSwap_comp_firstCoordinateMap`, `coordinateSwap_comp_secondCoordinateMap`: the accepted
  swap exchanges the two polynomial coordinate embeddings of `FrobeniusProductPlaneChart`;
* `planeSwapMorphism` is that algebra equivalence read as a morphism of the plane, and
  **`productChart_swap_inv`**: `productChart i i ≫ (productSwapIso).inv = planeSwapMorphism ≫
  productChart i i`. So the product swap carries each *diagonal* chart to itself, reparameterised by
  the plane swap — which is exactly why `diagonalOpen i` is swap-stable;
* **`swappedCurve_diagonalChart`**, the swapped analogue of the accepted `curveInPlane_diagonalChart`;
* **`chartOpen_le_preimage_diagonal_swap`** and its cover-indexed form
  **`standardOpens_le_preimage_atlas_swap`**, the hypothesis `hσ` that
  `exponent_pullback_eq_of_monomial` consumes.

**Deliberately not proved here.** No exponent and no Laurent form: this module supplies only the
refinement hypothesis. It says nothing about the value of either ruling exponent.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusGraphSwapRefinement

open KltDP.Geometry KltDP.Geometry.ProjectiveLineComparison
open KltDP.Geometry.ProjectiveLineTransitionExtension
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusProductPlaneChart
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassPowerCharts
open FrobeniusGraphPicardClassSwap FrobeniusStrictTransformFiberRowsExponents

variable {k : Type u} [Field k]

local instance swapRefinementProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-! ### The accepted plane swap exchanges the two coordinate embeddings -/

/-- The accepted coordinate exchange sends the first polynomial coordinate to the second. -/
theorem coordinateSwap_comp_firstCoordinateMap :
    (coordinateSwap (k := k)).toRingHom.comp firstCoordinateMap = secondCoordinateMap := by
  apply Polynomial.ringHom_ext
  · intro r
    change coordinateSwap (firstCoordinateMap (Polynomial.C r)) =
      secondCoordinateMap (Polynomial.C r)
    rw [firstCoordinateMap_C, secondCoordinateMap_C, coordinateSwap_constants]
  · change coordinateSwap (firstCoordinateMap (Polynomial.X : Polynomial k)) =
      secondCoordinateMap (Polynomial.X : Polynomial k)
    rw [firstCoordinateMap_X, secondCoordinateMap_X, coordinateSwap_u]

/-- The accepted coordinate exchange sends the second polynomial coordinate to the first. -/
theorem coordinateSwap_comp_secondCoordinateMap :
    (coordinateSwap (k := k)).toRingHom.comp secondCoordinateMap = firstCoordinateMap := by
  apply Polynomial.ringHom_ext
  · intro r
    change coordinateSwap (secondCoordinateMap (Polynomial.C r)) =
      firstCoordinateMap (Polynomial.C r)
    rw [secondCoordinateMap_C, firstCoordinateMap_C, coordinateSwap_constants]
  · change coordinateSwap (secondCoordinateMap (Polynomial.X : Polynomial k)) =
      firstCoordinateMap (Polynomial.X : Polynomial k)
    rw [secondCoordinateMap_X, firstCoordinateMap_X, coordinateSwap_v]

/-- The accepted coordinate exchange, as a morphism of the actual polynomial plane. -/
def planeSwapMorphism : plane k ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (coordinateSwap (k := k)).toRingHom)

@[reassoc] theorem planeSwapMorphism_firstCoordinate :
    planeSwapMorphism (k := k) ≫ Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) =
      Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) := by
  rw [planeSwapMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coordinateSwap_comp_firstCoordinateMap]

@[reassoc] theorem planeSwapMorphism_secondCoordinate :
    planeSwapMorphism (k := k) ≫ Spec.map (CommRingCat.ofHom (secondCoordinateMap (k := k))) =
      Spec.map (CommRingCat.ofHom (firstCoordinateMap (k := k))) := by
  rw [planeSwapMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coordinateSwap_comp_secondCoordinateMap]

/-! ### The product swap preserves each diagonal chart -/

/-- **The product swap carries the diagonal chart `i` to itself**, reparameterised by the accepted
plane coordinate exchange. -/
@[reassoc] theorem productChart_swap_inv (i : Fin 2) :
    productChart (k := k) i i ≫ (productSwapIso (k := k)).inv =
      planeSwapMorphism (k := k) ≫ productChart i i := by
  apply pullback.hom_ext
  · change (productChart (k := k) i i ≫ (pullbackSymmetry (projectiveSpaceToSpec k 1)
        (projectiveSpaceToSpec k 1)).inv) ≫ pullback.fst _ _ = _
    rw [Category.assoc, pullbackSymmetry_inv_comp_fst, productChart_snd, Category.assoc,
      productChart_fst, ← Category.assoc, planeSwapMorphism_firstCoordinate]
  · change (productChart (k := k) i i ≫ (pullbackSymmetry (projectiveSpaceToSpec k 1)
        (projectiveSpaceToSpec k 1)).inv) ≫ pullback.snd _ _ = _
    rw [Category.assoc, pullbackSymmetry_inv_comp_snd, productChart_fst, Category.assoc,
      productChart_snd, ← Category.assoc, planeSwapMorphism_secondCoordinate]

/-- The swapped analogue of the accepted `curveInPlane_diagonalChart`: the monomial curve, read
through the plane swap, gives the swapped graph section in the diagonal chart `i`. -/
theorem swappedCurve_diagonalChart (p : ℕ) (i : Fin 2) :
    (curveInPlane (k := k) p ≫ planeSwapMorphism (k := k)) ≫ productChart i i =
      polynomialChartMap k i ≫
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv) := by
  rw [Category.assoc, ← productChart_swap_inv, ← Category.assoc, curveInPlane_diagonalChart,
    Category.assoc]

/-! ### The refinement hypothesis for the swapped section -/

/-- **The swapped graph section maps the standard chart `i` of `P¹` into the diagonal chart `i`.**
This is the swapped analogue of the accepted `chartOpen_le_preimage_diagonal`. -/
theorem chartOpen_le_preimage_diagonal_swap (p : ℕ) (i : Fin 2) :
    chartOpen k i ≤
      (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv) ⁻¹ᵁ diagonalOpen i := by
  intro x hx
  rw [← polynomialChartMap_opensRange] at hx
  obtain ⟨z, rfl⟩ := hx
  show (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv).base
      ((polynomialChartMap k i).base z) ∈ diagonalOpen i
  rw [← Scheme.comp_base_apply, ← swappedCurve_diagonalChart, Scheme.comp_base_apply,
    diagonalOpen, Scheme.Hom.image_top_eq_opensRange]
  exact ⟨_, rfl⟩

/-- **The refinement hypothesis `hσ` for the swapped section**, in the cover-indexed form consumed
by `ProjectiveLineCocycleRefinement.exponent_pullback_eq_of_monomial`. -/
theorem standardOpens_le_preimage_atlas_swap (p q : ℕ) (i : ULift.{u} (Fin 2)) :
    standardOpens k i ≤
      (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv) ⁻¹ᵁ
        graphAtlasCover q (graphSectionRefinement i) :=
  chartOpen_le_preimage_diagonal_swap p i.down

end KltDP.Examples.FrobeniusGraphSwapRefinement

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassSwap
open FrobeniusGraphSwapRefinement

/-- **The swapped graph section refines the diagonal atlas.** Each standard chart of `P¹` lands in
the preimage of the corresponding diagonal chart of `P¹ ×_k P¹` under the swapped section, which is
the refinement hypothesis the accepted exponent machinery consumes for the `a`-row. -/
theorem f29_swapped_section_refines_diagonal (k : Type u) [Field k] (p : ℕ) (i : Fin 2) :
    chartOpen k i ≤
      (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv) ⁻¹ᵁ diagonalOpen i :=
  chartOpen_le_preimage_diagonal_swap p i

/-- The bundle has exactly one universe parameter. -/
theorem f29_swapped_section_refines_diagonal_universe_check (k : Type u) [Field k] (p : ℕ)
    (i : Fin 2) : True := by
  have _ := f29_swapped_section_refines_diagonal.{u} k p i
  trivial

end KltDP.Examples
