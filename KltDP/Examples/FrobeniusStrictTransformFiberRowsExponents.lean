import KltDP.Geometry.ProjectiveLineCocycleRefinement
import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts

/-!
# The exponent of the graph section against the graph ideal line (BRIEF17, item 2, reduction)

The graph ideal line `graphIdealLine q` (ideal of `y = x^q`) carries the accepted atlas
`originalGraphAtlas q` (the two diagonal charts and the graph complement), so its class is the class
of the atlas transition cocycle (`graphIdealLine_toPic_eq`). The graph section
`projectiveGraphMorphism p : P¹ ⟶ P¹ × P¹` maps the standard chart `i` of `P¹` into the diagonal chart
`i` (`chartOpen_le_preimage_diagonal`, accepted `curveInPlane_diagonalChart`), so the standard cover
refines the pulled-back atlas and, given the pullback compatibility `PullbackGluedClass`,
`exponent ((projectiveGraphMorphism p)^* graphIdealLine q)` is the Laurent exponent of the pulled-back
transition unit between the two diagonal charts (`exponent_graphSection_graphIdealLine`); if that unit
reads `c · Tⁿ`, the exponent is `n` (`exponent_graphSection_graphIdealLine_of_monomial`), and for
`q = 0`, `n = −p` gives **`B · b = p`** on `stageSurface (n+1) hproj`
(`graphStrictPairing_secondFiber_of_monomial`).

**Not proved here**: `PullbackGluedClass` (lane A1's accepted `pullbackGluedClass`, not importable on
the dev711-07 tree, see the record) and the explicit Laurent form `−T^{−p}` of the pulled-back unit
`(y − 1)/(y' − 1) ∘ (t, t^p)`; the vertical ideal line (`B · a`, `F̃ · a`) needs a swap-compatible atlas.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction
open KltDP.Geometry.ProjectiveLineSheafExponent KltDP.Geometry.ProjectiveLineTransitionExtension
open KltDP.Geometry.ProjectiveLineTransitionExponent KltDP.Geometry.ProjectiveLineCocycleRefinement
open KltDP.Geometry.ProjectiveLineIdealLineDegree KltDP.Geometry.ProjectiveLineComparison
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing FrobeniusStrictTransformFiberRows
open FrobeniusGraphClosed FrobeniusProjectiveMorphism FrobeniusProjectivePoints
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassDiagonal FrobeniusGraphPicardClassCharts
open FrobeniusGraphPicardClassPowerCharts FrobeniusGraphPicardClassTotalTransform
open FrobeniusBlowupChartIteration

variable {k : Type u} [Field k]

/-- The opens of the accepted atlas of the graph ideal line (the two diagonal charts and the graph
complement), as an opaque cover. -/
def graphAtlasCover (q : ℕ) : ULift.{u} (Option (Fin 2)) → (projectiveProduct k).Opens :=
  (originalGraphAtlas (k := k) q).X

theorem graphAtlasCover_some (q : ℕ) (i : Fin 2) :
    graphAtlasCover (k := k) q (ULift.up (some i)) = diagonalOpen i := rfl

/-- The transition cocycle of the accepted atlas of the graph ideal line. -/
def graphAtlasUnits (q : ℕ) :
    ∀ i j : ULift.{u} (Option (Fin 2)),
      Γ(projectiveProduct k, graphAtlasCover (k := k) q i ⊓ graphAtlasCover q j)ˣ :=
  transitionUnits (projectiveProduct k) (schemeKernelIdeal (projectiveGraphMorphism (k := k) q))
    (originalGraphAtlas q)

theorem graphAtlasUnits_isCocycle (q : ℕ) :
    IsCocycle (projectiveProduct k) (graphAtlasCover (k := k) q) (graphAtlasUnits q) :=
  transitionUnits_isCocycle _ _ _

theorem graphAtlasCover_top (q : ℕ) : (⨆ i, graphAtlasCover (k := k) q i) = ⊤ :=
  chartOpens_cover _ _ (originalGraphAtlas q)

/-- **The class of the graph ideal line is the class of its atlas cocycle.** -/
theorem graphIdealLine_toPic_eq (q : ℕ) :
    (graphIdealLine (k := k) q).toPic =
      picardClass (projectiveProduct k) (graphAtlasCover q) (graphAtlasUnits q)
        (graphAtlasUnits_isCocycle q) (graphAtlasCover_top q) :=
  toPic_eq_picardClass_atlas (graphIdealLine q) (originalGraphAtlas q) (chartOpens_cover _ _ _)

/-- The graph section maps the standard chart `i` into the diagonal chart `i`. -/
theorem chartOpen_le_preimage_diagonal (p : ℕ) (i : Fin 2) :
    chartOpen k i ≤ projectiveGraphMorphism (k := k) p ⁻¹ᵁ diagonalOpen i := by
  intro x hx
  rw [← polynomialChartMap_opensRange] at hx
  obtain ⟨z, rfl⟩ := hx
  show (projectiveGraphMorphism (k := k) p).base ((polynomialChartMap k i).base z) ∈ diagonalOpen i
  rw [← Scheme.comp_base_apply, ← curveInPlane_diagonalChart, Scheme.comp_base_apply, diagonalOpen,
    Scheme.Hom.image_top_eq_opensRange]
  exact ⟨_, rfl⟩

/-- The refinement of the pulled-back atlas by the standard opens: chart `i` into diagonal chart `i`. -/
def graphSectionRefinement : ULift.{u} (Fin 2) → ULift.{u} (Option (Fin 2)) :=
  fun i => ULift.up (some i.down)

theorem standardOpens_le_preimage_atlas (p q : ℕ) (i : ULift.{u} (Fin 2)) :
    standardOpens k i ≤
      projectiveGraphMorphism (k := k) p ⁻¹ᵁ graphAtlasCover q (graphSectionRefinement i) :=
  chartOpen_le_preimage_diagonal p i.down

/-- The refined pulled-back transition unit between the two standard charts. -/
def graphSectionUnit (p q : ℕ) : Γ(projectiveSpace k 1, standardOpens k ⟨0⟩ ⊓ standardOpens k ⟨1⟩)ˣ :=
  refinedUnits (projectiveSpace k 1)
    (fun j => projectiveGraphMorphism (k := k) p ⁻¹ᵁ graphAtlasCover q j)
    (pullbackUnits (projectiveGraphMorphism p) (graphAtlasCover q) (graphAtlasUnits q))
    (standardOpens k) graphSectionRefinement (standardOpens_le_preimage_atlas p q) ⟨0⟩ ⟨1⟩

/-- **The exponent of the graph section against the graph ideal line is the Laurent exponent of the
pulled-back diagonal transition unit** (given the pullback compatibility). -/
theorem exponent_graphSection_graphIdealLine (hP : PullbackGluedClass.{u}) (p q : ℕ) :
    exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p) (graphIdealLine q)) =
      overlapExponent k (overlapRestriction k (graphSectionUnit p q)) :=
  exponent_pullback_eq_overlapExponent k hP (graphIdealLine q) (graphAtlasCover q)
    (graphAtlasUnits q) (graphAtlasUnits_isCocycle q) (graphAtlasCover_top q)
    (graphIdealLine_toPic_eq q) (projectiveGraphMorphism p) graphSectionRefinement
    (standardOpens_le_preimage_atlas p q)

/-- If the pulled-back diagonal transition unit reads `c · Tⁿ`, the exponent is `n`. -/
theorem exponent_graphSection_graphIdealLine_of_monomial (hP : PullbackGluedClass.{u}) (p q : ℕ)
    (c : kˣ) (n : ℤ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (graphSectionUnit (k := k) p q)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) :
    exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p) (graphIdealLine q)) =
      n := by
  rw [exponent_graphSection_graphIdealLine hP p q]
  exact unitExponent_eq_of_monomial k _ c n h

section Rows

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · b = p`** on `stageSurface (n+1) hproj`, given the pullback compatibility and the Laurent
form `c · T^{−p}` of the pulled-back diagonal transition unit of the ideal line of `y = 1`. -/
theorem graphStrictPairing_secondFiber_of_monomial (hP : PullbackGluedClass.{u}) (m : ℕ) (c : kˣ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (graphSectionUnit (k := k) (m + (n + 1)) 0)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T (-(m + (n + 1) : ℤ))) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) = (m + (n + 1) : ℤ) :=
  graphStrictPairing_secondFiber_of_exponent n hproj m
    (exponent_graphSection_graphIdealLine_of_monomial hP (m + (n + 1)) 0 c _ h)

end Rows

end KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents
