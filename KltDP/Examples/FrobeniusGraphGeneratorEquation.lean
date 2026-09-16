import KltDP.Geometry.SchemeConormal
import KltDP.Geometry.TransitionUnitSections
import KltDP.Geometry.TransitionUnitExtraction
import KltDP.Geometry.CartierPicardAssembly
import KltDP.Geometry.CartierPicardSurjectivity
import KltDP.Geometry.RationalTreePicardOpenChartTransition
import KltDP.Geometry.TransitionUnitGenerator
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassNormalization
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents
import KltDP.Examples.FrobeniusGraphAtlasGenerator

/-!
# The atlas chart generators ARE the diagonal graph equations

`FrobeniusGraphAtlasGenerator` proves step (a) abstractly: the transition unit of the accepted graph
atlas is the ratio of the chart generators `d_i := ι (chartEquiv_i⁻¹ 1)`. That is only useful once
`d_i` is identified with the actual equation of the graph in the diagonal chart. This module does
that, and it does it **entirely from accepted material** — no over-site argument is rebuilt.

The identification the accepted tree already contains, under a name no search for
"generator/frame/equation" surfaces:
**`FrobeniusGraphPicardClassNormalization.diagonalGraphGenerator_inclusion`**, which says the ideal
inclusion sends the over-site generator `diagonalGraphGenerator q j` to the diagonal section
`diagonalSection q j`. What remained was to see that *their* generator is *my* `chartEquiv_j⁻¹ 1`:

* `chartEquiv_symm_one_eq`: on any `W ≤ diagonalOpen j`, `(chartEquiv_j)⁻¹ 1` is the restriction of
  `diagonalGraphGenerator q j`. The two are the same section because
  `chartEquiv_ofOpenCharts` rewrites the atlas coordinate as `openChartCoordinate`, which is
  *definitionally* the evaluation `overTrivializationSectionEquiv` performs for the chart
  trivialisation `(openChartToOverUnitIso …).symm`; the subopen case is the accepted
  `lineBundleChartGenerator_restrict`.
* **`graphIdealGenerator_eq_diagonalSection`**: `d_j = res (diagonalSection q j)`.
* **`graphAtlasUnits_mul_diagonalSection`**: hence `g₀₁ · e₀ = e₁` with `e_i` the **actual graph
  equations** — step (a) in fully concrete form, which is the gate on (b) and (c).

**Deliberately not proved here.** No Laurent form, and no evaluation of the ratio: steps (b)
(`g₀₁ = −v` on the overlap) and (c) (pulling back along the two sections) are untouched, and the
prediction `c = −1` is not assumed anywhere.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphGeneratorEquation

open KltDP.Geometry KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction
open KltDP.Geometry.TransitionUnitGenerator KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassNormalization
open FrobeniusStrictTransformFiberRowsExponents FrobeniusGraphAtlasGenerator

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance generatorEquationProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The section whose atlas chart coordinate is `1` on a subopen of the diagonal chart is the
restriction of the accepted over-site generator. -/
theorem chartEquiv_symm_one_eq (q : ℕ) (j : Fin 2) {W : (projectiveProduct k).Opens}
    (hW : W ≤ diagonalOpen j) :
    (chartEquiv (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
        (originalGraphAtlas q) ⟨some j⟩ hW).symm 1 =
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) q)).val.map (homOfLE hW).op
        (diagonalGraphGenerator (k := k) q j) := by
  have harg :
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) q)).val.map (homOfLE hW).op
          (lineBundleChartGenerator (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
            (diagonalGraphChart (k := k) q j)) =
        (overTrivializationSectionEquiv (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q)) (diagonalOpen j)
          (diagonalGraphChart (k := k) q j).trivialization (homOfLE hW)).symm 1 :=
    lineBundleChartGenerator_restrict (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
      (diagonalGraphChart (k := k) q j) (homOfLE hW)
  have key : chartEquiv (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
      (localTrivializationsOfOpenCharts (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
        (fun i : ULift.{u} (Option (Fin 2)) => originalAtlasOpen q i.down)
        (originalAtlasOpens_cover q) (fun i => originalOpenFrame q i.down))
      ⟨some j⟩ hW
        ((schemeKernelIdeal (projectiveGraphMorphism (k := k) q)).val.map (homOfLE hW).op
          (diagonalGraphGenerator (k := k) q j)) = 1 := by
    rw [chartEquiv_ofOpenCharts (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
      (fun i : ULift.{u} (Option (Fin 2)) => originalAtlasOpen q i.down)
      (originalAtlasOpens_cover q) (fun i => originalOpenFrame q i.down) ⟨some j⟩ hW]
    show (overTrivializationSectionEquiv (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q)) (diagonalOpen j)
        (diagonalGraphChart (k := k) q j).trivialization (homOfLE hW))
        ((schemeKernelIdeal (projectiveGraphMorphism (k := k) q)).val.map (homOfLE hW).op
          (lineBundleChartGenerator (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
            (diagonalGraphChart (k := k) q j))) = 1
    rw [harg]
    exact (overTrivializationSectionEquiv (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q)) (diagonalOpen j)
      (diagonalGraphChart (k := k) q j).trivialization (homOfLE hW)).apply_symm_apply 1
  rw [LinearEquiv.symm_apply_eq]
  exact key.symm

/-- **The chart generator is the diagonal graph equation.** -/
theorem graphIdealGenerator_eq_diagonalSection (q : ℕ) (j : Fin 2)
    {W : (projectiveProduct k).Opens} (hW : W ≤ graphAtlasCover q ⟨some j⟩) :
    graphIdealGenerator (k := k) q ⟨some j⟩ hW =
      res (projectiveProduct k) hW (diagonalSection (k := k) q j) := by
  show (schemeKernelIdealι (projectiveGraphMorphism (k := k) q)).val.app (op W)
      ((chartEquiv (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
        (originalGraphAtlas q) ⟨some j⟩ hW).symm 1) = _
  rw [chartEquiv_symm_one_eq q j (show W ≤ diagonalOpen j from hW),
    PresheafOfModules.naturality_apply
      (schemeKernelIdealι (projectiveGraphMorphism (k := k) q)).val
      (homOfLE (show W ≤ diagonalOpen j from hW)).op
      (diagonalGraphGenerator (k := k) q j),
    diagonalGraphGenerator_inclusion]
  rfl

/-- **Step (a), concretely: `g₀₁ · e₀ = e₁` with the actual graph equations.** -/
theorem graphAtlasUnits_mul_diagonalSection (q : ℕ) (i j : Fin 2)
    {W : (projectiveProduct k).Opens} (hWi : W ≤ graphAtlasCover q ⟨some i⟩)
    (hWj : W ≤ graphAtlasCover q ⟨some j⟩) :
    res (projectiveProduct k) (le_inf hWi hWj)
          (graphAtlasUnits (k := k) q ⟨some i⟩ ⟨some j⟩) *
        res (projectiveProduct k) hWi (diagonalSection (k := k) q i) =
      res (projectiveProduct k) hWj (diagonalSection (k := k) q j) := by
  rw [← graphIdealGenerator_eq_diagonalSection q i hWi,
    ← graphIdealGenerator_eq_diagonalSection q j hWj]
  exact graphAtlasUnits_mul_graphIdealGenerator q ⟨some i⟩ ⟨some j⟩ hWi hWj

end KltDP.Examples.FrobeniusGraphGeneratorEquation

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusStrictTransformFiberRowsExponents
open FrobeniusGraphGeneratorEquation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- **Step (a) of the F29 ruling computation, in concrete form.** The transition unit of the
accepted graph atlas between two diagonal charts is the ratio of the two actual graph equations. -/
theorem f29_graph_generator_equation (k : Type u) [Field k] (q : ℕ) (i j : Fin 2)
    {W : (projectiveProduct k).Opens} (hWi : W ≤ graphAtlasCover q ⟨some i⟩)
    (hWj : W ≤ graphAtlasCover q ⟨some j⟩) :
    res (projectiveProduct k) (le_inf hWi hWj)
          (graphAtlasUnits (k := k) q ⟨some i⟩ ⟨some j⟩) *
        res (projectiveProduct k) hWi (diagonalSection (k := k) q i) =
      res (projectiveProduct k) hWj (diagonalSection (k := k) q j) :=
  graphAtlasUnits_mul_diagonalSection q i j hWi hWj

/-- The bundle has exactly one universe parameter. -/
theorem f29_graph_generator_equation_universe_check (k : Type u) [Field k] (q : ℕ) (i j : Fin 2)
    {W : (projectiveProduct k).Opens} (hWi : W ≤ graphAtlasCover q ⟨some i⟩)
    (hWj : W ≤ graphAtlasCover q ⟨some j⟩) : True := by
  have _ := f29_graph_generator_equation.{u} k q i j hWi hWj
  trivial

end KltDP.Examples
