import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusOldExceptionalSelfRow

/-!
# The rows `B · a`, `B · b`, `F̃ · a`, `F̃ · b` reduced to degrees on `P¹` (BRIEF15, item 2)

With `B_{n+1} ≅ P¹` and `F̃_{n+1} ≅ P¹` over the blowdown (`FrobeniusStrictTransformIsoProjectiveLine`)
and the degree transport `picardDegree_pullback_iso`, the pairing of `B` (resp. `F̃`) on
`stageSurface (n+1) hproj` with every class pulled back from stage `0` is the Euler degree on `P¹`
of the class pulled back along the graph section `projectiveGraphMorphism (m + (n+1))` (resp. the
horizontal fibre `horizontalFiberMorphism 0`):
`graphStrictPairing_pullback`, `fiberStrictPairing_pullback`. Specialised to the fibre classes
`a = −[π^* verticalFiberIdealLine]`, `b = −[π^* graphIdealLine 0]` (accepted definitions):
`graphStrictPairing_firstFiber`, `graphStrictPairing_secondFiber`, `fiberStrictPairing_firstFiber`,
`fiberStrictPairing_secondFiber`, each equal to minus a `P¹` Euler degree, and the conditional rows
`B · a = 1`, `B · b = p`, `F̃ · a = 1`, `F̃ · b = 0` given those four degrees (`−1`, `−p`, `−1`, `0`).

**Not proved here**: the four `P¹` degrees themselves (the Euler degree of the pullback of the
ideal line of a ruling along a section of `P¹ × P¹`): they need the base change of the ideal line
along the section (the ideal line of a point, resp. of `p` points, resp. trivial) and the Euler
characteristics `χ(P¹, O(−d)) = 1 − d`; neither is in the accepted tree.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFiberRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.PrimeCurveInclusionLift
open KltDP.Geometry.PrimeCurveDegreeTransport
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusExceptionalFinalConfiguration FrobeniusGlobalStrictTransform FrobeniusFiberClosure
open FrobeniusStrictTransformPrimeCurves FrobeniusStrictTransformPairing
open FrobeniusStrictTransformIsoProjectiveLine FrobeniusOldExceptionalSelfRow
open FrobeniusGraphClosed FrobeniusProjectiveMorphism FrobeniusProjectivePoints
open FrobeniusGraphPicardClassZeroFiber FrobeniusGraphPicardClassTotalTransform
open FrobeniusGraphPicardClassFiberClasses FrobeniusGraphPicardClassFrames

variable {k : Type u} [Field k]

/-- The structure morphism of stage `N` factors through the blowdown to stage `0`. -/
theorem projectiveContactProjection_structureMap (N : ℕ) :
    projectiveContactProjection (k := k) N ≫ (projectiveProductInitial (k := k)).structureMap =
      ((projectiveProductInitial (k := k)).stage N).structureMap := by
  have h := between_structureMap (projectiveProductInitial (k := k)) (Nat.zero_le N)
  rw [between_zero] at h
  exact h

section Rows

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The base of the graph section `P¹ ⟶ P¹ × P¹ ⟶ Spec k`. -/
abbrev graphSectionBase (p : ℕ) : projectiveSpace k 1 ⟶ Spec (CommRingCat.of k) :=
  projectiveGraphMorphism (k := k) p ≫ (projectiveProductInitial (k := k)).structureMap

/-- The base of the horizontal fibre `P¹ ⟶ P¹ × P¹ ⟶ Spec k`. -/
abbrev fiberSectionBase : projectiveSpace k 1 ⟶ Spec (CommRingCat.of k) :=
  horizontalFiberMorphism (0 : k) ≫ (projectiveProductInitial (k := k)).structureMap

/-- `B_{n+1} ≅ P¹` as a morphism from the prime-curve scheme. -/
abbrev graphCurveToLine (m : ℕ) :
    (graphStrictPrimeCurve n hproj m).toScheme ⟶ projectiveSpace k 1 :=
  inv (lift (graphStrictPrimeCurve n hproj m) (strictTransformι (n + 1) (m + (n + 1))) rfl) ≫
    (graphStrictIsoProjectiveLine (n + 1) m).hom

/-- `F̃_{n+1} ≅ P¹` as a morphism from the prime-curve scheme. -/
abbrev fiberCurveToLine : (fiberStrictPrimeCurve n hproj).toScheme ⟶ projectiveSpace k 1 :=
  inv (lift (fiberStrictPrimeCurve n hproj)
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) rfl) ≫
    (fiberStrictIsoProjectiveLine (n + 1)).hom

theorem graphCurveToLine_base (m : ℕ) :
    graphCurveToLine n hproj m ≫ graphSectionBase (m + (n + 1)) =
      (graphStrictPrimeCurve n hproj m).toSpec := by
  change _ = (graphStrictPrimeCurve n hproj m).inclusion ≫
    ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap
  rw [inclusion_eq_inv_lift (graphStrictPrimeCurve n hproj m)
      (strictTransformι (n + 1) (m + (n + 1))) rfl,
    ← projectiveContactProjection_structureMap, graphCurveToLine, graphSectionBase,
    Category.assoc, Category.assoc, ← Category.assoc (graphStrictIsoProjectiveLine (n + 1) m).hom,
    graphStrictIsoProjectiveLine_hom_comp, Category.assoc]

theorem fiberCurveToLine_base :
    fiberCurveToLine n hproj ≫ fiberSectionBase = (fiberStrictPrimeCurve n hproj).toSpec := by
  change _ = (fiberStrictPrimeCurve n hproj).inclusion ≫
    ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap
  rw [inclusion_eq_inv_lift (fiberStrictPrimeCurve n hproj)
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) rfl,
    ← projectiveContactProjection_structureMap, fiberCurveToLine, fiberSectionBase,
    Category.assoc, Category.assoc, ← Category.assoc (fiberStrictIsoProjectiveLine (n + 1)).hom,
    fiberStrictIsoProjectiveLine_hom_comp, Category.assoc]

/-- **Degree transport for `B`**: the pairing with a class pulled back from stage `0` is the Euler
degree on `P¹` of its pullback along the graph section. -/
theorem graphStrictPairing_pullback (m : ℕ) (q : (projectiveProduct k).Pic) :
    graphStrictPairing n hproj m
      ((schemePicardPullbackHom (projectiveContactProjection (n + 1))).toAdditive
        (Additive.ofMul q)) =
      eulerDegree (graphSectionBase (m + (n + 1)))
        (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1))) q) := by
  change (graphStrictPrimeCurve n hproj m).picardRestrictionDegree
    (schemePicardPullbackHom (projectiveContactProjection (n + 1)) q) = _
  erw [PrimeCurve.picardRestrictionDegree_pullback]
  rw [inclusion_eq_inv_lift (graphStrictPrimeCurve n hproj m)
      (strictTransformι (n + 1) (m + (n + 1))) rfl,
    Category.assoc, ← graphStrictIsoProjectiveLine_hom_comp (n + 1) m, ← Category.assoc,
    schemePicardPullbackHom_comp (projectiveGraphMorphism (m + (n + 1))) (graphCurveToLine n hproj m)]
  exact picardDegree_pullback_iso (graphStrictPrimeCurve n hproj m) (graphCurveToLine n hproj m)
    (graphSectionBase (m + (n + 1))) (graphCurveToLine_base n hproj m) _

/-- **Degree transport for `F̃`.** -/
theorem fiberStrictPairing_pullback (q : (projectiveProduct k).Pic) :
    fiberStrictPairing n hproj
      ((schemePicardPullbackHom (projectiveContactProjection (n + 1))).toAdditive
        (Additive.ofMul q)) =
      eulerDegree fiberSectionBase (schemePicardPullbackHom (horizontalFiberMorphism (0 : k)) q) := by
  change (fiberStrictPrimeCurve n hproj).picardRestrictionDegree
    (schemePicardPullbackHom (projectiveContactProjection (n + 1)) q) = _
  erw [PrimeCurve.picardRestrictionDegree_pullback]
  rw [inclusion_eq_inv_lift (fiberStrictPrimeCurve n hproj)
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) rfl,
    Category.assoc, ← fiberStrictIsoProjectiveLine_hom_comp (n + 1), ← Category.assoc,
    schemePicardPullbackHom_comp (horizontalFiberMorphism (0 : k)) (fiberCurveToLine n hproj)]
  exact picardDegree_pullback_iso (fiberStrictPrimeCurve n hproj) (fiberCurveToLine n hproj)
    fiberSectionBase (fiberCurveToLine_base n hproj) _

/-- `B · a` is minus the `P¹` degree of the vertical ideal line pulled back along the section. -/
theorem graphStrictPairing_firstFiber (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) =
      -eulerDegree (graphSectionBase (m + (n + 1)))
        (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
          (verticalFiberIdealLine (k := k)).toPic) := by
  rw [firstFiberTotalClass, map_neg, ← schemePicardPullbackHom_toPic]
  exact congrArg Neg.neg (graphStrictPairing_pullback n hproj m _)

/-- `B · b` is minus the `P¹` degree of the horizontal ideal line pulled back along the section. -/
theorem graphStrictPairing_secondFiber (m : ℕ) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) =
      -eulerDegree (graphSectionBase (m + (n + 1)))
        (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
          (graphIdealLine (k := k) 0).toPic) := by
  rw [secondFiberTotalClass, graphTotalIdealLine, map_neg, ← schemePicardPullbackHom_toPic]
  exact congrArg Neg.neg (graphStrictPairing_pullback n hproj m _)

theorem fiberStrictPairing_firstFiber :
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) =
      -eulerDegree fiberSectionBase
        (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
          (verticalFiberIdealLine (k := k)).toPic) := by
  rw [firstFiberTotalClass, map_neg, ← schemePicardPullbackHom_toPic]
  exact congrArg Neg.neg (fiberStrictPairing_pullback n hproj _)

theorem fiberStrictPairing_secondFiber :
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) =
      -eulerDegree fiberSectionBase
        (schemePicardPullbackHom (horizontalFiberMorphism (0 : k)) (graphIdealLine (k := k) 0).toPic) := by
  rw [secondFiberTotalClass, graphTotalIdealLine, map_neg, ← schemePicardPullbackHom_toPic]
  exact congrArg Neg.neg (fiberStrictPairing_pullback n hproj _)

/-! ### The rows, conditional on the four `P¹` degrees -/

theorem graphStrictPairing_firstFiber_eq_one (m : ℕ)
    (h : eulerDegree (graphSectionBase (m + (n + 1)))
      (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
        (verticalFiberIdealLine (k := k)).toPic) = -1) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) = 1 := by
  rw [graphStrictPairing_firstFiber, h, neg_neg]

theorem graphStrictPairing_secondFiber_eq (m : ℕ)
    (h : eulerDegree (graphSectionBase (m + (n + 1)))
      (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
        (graphIdealLine (k := k) 0).toPic) = -(m + (n + 1) : ℤ)) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) = (m + (n + 1) : ℤ) := by
  rw [graphStrictPairing_secondFiber, h, neg_neg]

theorem fiberStrictPairing_firstFiber_eq_one
    (h : eulerDegree fiberSectionBase
      (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
        (verticalFiberIdealLine (k := k)).toPic) = -1) :
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) = 1 := by
  rw [fiberStrictPairing_firstFiber, h, neg_neg]

theorem fiberStrictPairing_secondFiber_eq_zero
    (h : eulerDegree fiberSectionBase
      (schemePicardPullbackHom (horizontalFiberMorphism (0 : k)) (graphIdealLine (k := k) 0).toPic) =
        0) :
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0 := by
  rw [fiberStrictPairing_secondFiber, h, neg_zero]

end Rows

end KltDP.Examples.FrobeniusStrictTransformFiberRows

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.PrimeCurveDegreeTransport FrobeniusGlobalBlowupStages
  FrobeniusStrictTransformPairing FrobeniusStrictTransformFiberRows
  FrobeniusGraphPicardClassTotalTransform FrobeniusGraphPicardClassFiberClasses
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassZeroFiber FrobeniusProjectiveMorphism

/-- **The fibre-class rows of `B` and `F̃` reduce to Euler degrees on `P¹`**: on
`stageSurface (n+1) hproj`, `B · a`, `B · b`, `F̃ · a`, `F̃ · b` are minus the Euler degrees on `P¹`
of the ruling ideal lines pulled back along the graph section, resp. the horizontal fibre. -/
theorem f29_strict_transform_fiber_rows_reduction (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) =
      -eulerDegree (graphSectionBase (m + (n + 1)))
        (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
          (verticalFiberIdealLine (k := k)).toPic) ∧
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) =
      -eulerDegree (graphSectionBase (m + (n + 1)))
        (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
          (graphIdealLine (k := k) 0).toPic) ∧
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) =
      -eulerDegree fiberSectionBase
        (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
          (verticalFiberIdealLine (k := k)).toPic) ∧
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) =
      -eulerDegree fiberSectionBase
        (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
          (graphIdealLine (k := k) 0).toPic) :=
  ⟨graphStrictPairing_firstFiber n hproj m, graphStrictPairing_secondFiber n hproj m,
    fiberStrictPairing_firstFiber n hproj, fiberStrictPairing_secondFiber n hproj⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_strict_transform_fiber_rows_reduction_universe_check (k : Type u) [Field k]
    [IsAlgClosed k] (n : ℕ) (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) (m : ℕ) : True := by
  have _ := f29_strict_transform_fiber_rows_reduction.{u} k n hproj m
  trivial

end KltDP.Examples
