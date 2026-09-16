import KltDP.Geometry.ProjectiveLineDegreeExponent
import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Examples.FrobeniusStrictTransformFiberRows

/-!
# The fibre-class rows as transition exponents on `P¹` (BRIEF16, item 1, reduction)

Lane D's `degree_eq_exponent` (`χ(L) − χ(O) = exponent L` on `P¹`) identifies the Euler degree
`eulerDegree (projectiveSpaceToSpec k 1) L.toPic` of `PrimeCurveDegreeTransport` with the transition
exponent of `L` (`eulerDegree_toPic_eq_exponent`). The bases of the graph section and of the
horizontal fibre are the structure morphism of `P¹` (`graphSectionBase_eq`, `fiberSectionBase_eq`),
so the rows of `FrobeniusStrictTransformFiberRows` become:

* `B · a = −exponent ((projectiveGraphMorphism p)^* verticalFiberIdealLine)`,
* `B · b = −exponent ((projectiveGraphMorphism p)^* graphIdealLine 0)`,
* `F̃ · a = −exponent ((horizontalFiberMorphism 0)^* verticalFiberIdealLine)`,
* `F̃ · b = −exponent ((horizontalFiberMorphism 0)^* graphIdealLine 0)`,

with `p = m + (n + 1)`; and the rows `B · a = 1`, `B · b = p`, `F̃ · a = 1`, `F̃ · b = 0` follow from the
exponents `−1`, `−p`, `−1`, `0` (`graphStrictPairing_firstFiber_of_exponent`, …).

**Not proved here**: the four exponents (the transition exponents of the pulled-back ruling ideal lines
on the standard cover of `P¹`); see the record.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveLineIdealLineDegree

open KltDP.Geometry KltDP.Geometry.PrimeCurveDegreeTransport KltDP.Geometry.ProjectiveLineDegree
open KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Examples.FrobeniusStrictTransformFiberRows KltDP.Examples.FrobeniusStrictTransformPairing
open KltDP.Examples.FrobeniusGlobalBlowupStages KltDP.Examples.FrobeniusGraphClosed
open KltDP.Examples.FrobeniusProjectiveMorphism KltDP.Examples.FrobeniusProjectivePoints
open KltDP.Examples.FrobeniusGraphPicardClassZeroFiber KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
open KltDP.Examples.FrobeniusGraphPicardClassFiberClasses KltDP.Examples.FrobeniusGraphPicardClassFrames

variable {k : Type u} [Field k]

/-- The Euler degree relative to the unit is lane D's `degree`, hence the transition exponent. -/
theorem eulerDegree_toPic_eq_exponent (L : InvertibleSheaf (projectiveSpace k 1)) :
    eulerDegree (projectiveSpaceToSpec k 1) L.toPic = exponent k L := by
  rw [← degree_eq_exponent, degree_eq_picardEulerValue]
  rfl

/-- The base of the graph section is the structure morphism of `P¹`. -/
theorem graphSectionBase_eq (p : ℕ) : graphSectionBase (k := k) p = projectiveSpaceToSpec k 1 := by
  show projectiveGraphMorphism (k := k) p ≫ projectiveProductToSpec = _
  rw [projectiveProductToSpec, ← Category.assoc, projectiveGraphMorphism_fst, Category.id_comp]

/-- The base of the horizontal fibre is the structure morphism of `P¹`. -/
theorem fiberSectionBase_eq : fiberSectionBase (k := k) = projectiveSpaceToSpec k 1 := by
  show horizontalFiberMorphism (0 : k) ≫ projectiveProductToSpec = _
  rw [projectiveProductToSpec, ← Category.assoc, horizontalFiberMorphism_fst, Category.id_comp]

section Rows

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · a = −exponent ((projectiveGraphMorphism p)^* verticalFiberIdealLine)`.** -/
theorem graphStrictPairing_firstFiber_exponent (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) =
      -exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) (m + (n + 1)))
        (verticalFiberIdealLine (k := k))) := by
  rw [graphStrictPairing_firstFiber, graphSectionBase_eq, schemePicardPullbackHom_toPic,
    eulerDegree_toPic_eq_exponent]

/-- **`B · b = −exponent ((projectiveGraphMorphism p)^* graphIdealLine 0)`.** -/
theorem graphStrictPairing_secondFiber_exponent (m : ℕ) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) =
      -exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) (m + (n + 1)))
        (graphIdealLine (k := k) 0)) := by
  rw [graphStrictPairing_secondFiber, graphSectionBase_eq, schemePicardPullbackHom_toPic,
    eulerDegree_toPic_eq_exponent]

/-- **`F̃ · a = −exponent ((horizontalFiberMorphism 0)^* verticalFiberIdealLine)`.** -/
theorem fiberStrictPairing_firstFiber_exponent :
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) =
      -exponent k (pullbackInvertibleSheaf (horizontalFiberMorphism (0 : k))
        (verticalFiberIdealLine (k := k))) := by
  rw [fiberStrictPairing_firstFiber, fiberSectionBase_eq, schemePicardPullbackHom_toPic,
    eulerDegree_toPic_eq_exponent]

/-- **`F̃ · b = −exponent ((horizontalFiberMorphism 0)^* graphIdealLine 0)`.** -/
theorem fiberStrictPairing_secondFiber_exponent :
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) =
      -exponent k (pullbackInvertibleSheaf (horizontalFiberMorphism (0 : k))
        (graphIdealLine (k := k) 0)) := by
  rw [fiberStrictPairing_secondFiber, fiberSectionBase_eq, schemePicardPullbackHom_toPic,
    eulerDegree_toPic_eq_exponent]

/-! ### The rows from the exponents -/

theorem graphStrictPairing_firstFiber_of_exponent (m : ℕ)
    (h : exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) (m + (n + 1)))
      (verticalFiberIdealLine (k := k))) = -1) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) = 1 := by
  rw [graphStrictPairing_firstFiber_exponent, h, neg_neg]

theorem graphStrictPairing_secondFiber_of_exponent (m : ℕ)
    (h : exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) (m + (n + 1)))
      (graphIdealLine (k := k) 0)) = -(m + (n + 1) : ℤ)) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) = (m + (n + 1) : ℤ) := by
  rw [graphStrictPairing_secondFiber_exponent, h, neg_neg]

theorem fiberStrictPairing_firstFiber_of_exponent
    (h : exponent k (pullbackInvertibleSheaf (horizontalFiberMorphism (0 : k))
      (verticalFiberIdealLine (k := k))) = -1) :
    fiberStrictPairing n hproj (firstFiberTotalClass (n + 1)) = 1 := by
  rw [fiberStrictPairing_firstFiber_exponent, h, neg_neg]

theorem fiberStrictPairing_secondFiber_of_exponent
    (h : exponent k (pullbackInvertibleSheaf (horizontalFiberMorphism (0 : k))
      (graphIdealLine (k := k) 0)) = 0) :
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0 := by
  rw [fiberStrictPairing_secondFiber_exponent, h, neg_zero]

/-- The trivial-pullback form of the last row: if the horizontal fibre `y = 0` pulls the ideal line of
`y = 1` back to a trivial bundle, then `F̃ · b = 0`. -/
theorem fiberStrictPairing_secondFiber_of_iso_unit
    (e : (pullbackInvertibleSheaf (horizontalFiberMorphism (0 : k)) (graphIdealLine (k := k) 0)).obj ≅
      _root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0 :=
  fiberStrictPairing_secondFiber_of_exponent n hproj (exponent_eq_zero_of_iso_unit k _ e)

end Rows

end KltDP.Geometry.ProjectiveLineIdealLineDegree
