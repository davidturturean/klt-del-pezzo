import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.ProjectiveLineSheafExponent
import KltDP.Geometry.ProjectiveLineTransitionExtension
import KltDP.Geometry.ProjectiveLineTransitionExponent
import KltDP.Geometry.TransitionUnitRefinementCocycle
import KltDP.Geometry.ProjectiveLineCocycleRefinement
import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
import KltDP.Examples.FrobeniusGraphPicardClassSwap
import KltDP.Examples.FrobeniusStrictTransformFiberRowsExponents
import KltDP.Examples.FrobeniusStrictTransformFiberRowsClosure
import KltDP.Examples.FrobeniusGraphSwapRefinement
import KltDP.Examples.FrobeniusGraphFirstRulingSwap
import KltDP.Examples.FrobeniusGraphBaseRows

/-!
# The `a`-row as a Laurent form on the accepted atlas

`FrobeniusGraphFirstRulingSwap` showed the `a`-row exponent is the exponent of the accepted
`graphIdealLine 0` pulled back along the swapped section
`projectiveGraphMorphism p ≫ (productSwapIso).inv`, and `FrobeniusGraphSwapRefinement` supplied the
refinement hypothesis for that section. Those are exactly the two inputs the accepted
`FrobeniusStrictTransformFiberRowsClosure.exponent_pullback_eq_of_monomial_unconditional` still
wanted, so the `a`-row now has the same shape the `b`-row already had:

* `swappedSectionUnit p q`, the refined pulled-back transition unit of the swapped section against
  the accepted atlas `originalGraphAtlas q` — the swapped analogue of the accepted
  `FrobeniusStrictTransformFiberRowsExponents.graphSectionUnit`;
* **`exponent_swappedSection_of_monomial`**: if that unit reads `c · Tⁿ` in the Laurent ring of the
  overlap, the pulled-back exponent is `n`. Unconditional — the pullback compatibility is the
  accepted `pullbackGluedClass'`;
* **`graphBasePairing_firstFiberClass_of_monomial` : `Γ·a = 1`** and
  **`graphStrictPairing_firstFiber_of_monomial` : `B·a = 1`** (with `p = m + (n+1)`), each given only
  the Laurent form `c · T⁻¹` of `swappedSectionUnit p 0`.

Both ruling rows of the F29 table are now single Laurent-form computations on one accepted atlas:
`c · T^{−p}` of `graphSectionUnit p 0` gives `b`, and `c · T⁻¹` of `swappedSectionUnit p 0` gives `a`.

**Deliberately not proved here.** Neither Laurent form. No numerical value for either ruling row is
claimed unconditionally; this module only reduces the `a`-row to the same one-line computation the
accepted tree already reduced the `b`-row to.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphSwapExponent

open KltDP.Geometry KltDP.Geometry.TransitionUnitGluing
open KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension
open KltDP.Geometry.ProjectiveLineTransitionExponent
open KltDP.Geometry.ProjectiveLineCocycleRefinement
open KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassTotalTransform
open FrobeniusGraphPicardClassFiberClasses FrobeniusGraphPicardClassSwap
open FrobeniusStrictTransformFiberRowsExponents FrobeniusStrictTransformFiberRowsClosure
open FrobeniusGraphSwapRefinement FrobeniusGraphFirstRulingSwap FrobeniusGraphBaseRows

variable {k : Type u} [Field k]

/-- The refined pulled-back transition unit of the **swapped** section against the accepted atlas of
the graph ideal line: the swapped analogue of the accepted `graphSectionUnit`. -/
def swappedSectionUnit (p q : ℕ) :
    Γ(projectiveSpace k 1, standardOpens k ⟨0⟩ ⊓ standardOpens k ⟨1⟩)ˣ :=
  refinedUnits (projectiveSpace k 1)
    (fun j => (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv) ⁻¹ᵁ
      graphAtlasCover q j)
    (pullbackUnits (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
      (graphAtlasCover q) (graphAtlasUnits q))
    (standardOpens k) graphSectionRefinement (standardOpens_le_preimage_atlas_swap p q) ⟨0⟩ ⟨1⟩

/-- **If the swapped section's transition unit reads `c · Tⁿ`, the `a`-row exponent is `n`.**
Unconditional: the pullback compatibility is the accepted `pullbackGluedClass'`. -/
theorem exponent_swappedSection_of_monomial (p q : ℕ) (c : kˣ) (n : ℤ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (swappedSectionUnit (k := k) p q)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) :
    exponent k (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) q)) = n :=
  exponent_pullback_eq_of_monomial_unconditional k (graphIdealLine q) (graphAtlasCover q)
    (graphAtlasUnits q) (graphAtlasUnits_isCocycle q) (graphAtlasCover_top q)
    (graphIdealLine_toPic_eq q) _ graphSectionRefinement
    (standardOpens_le_preimage_atlas_swap p q) c n h

section Rows

variable [IsAlgClosed k]

/-- **`Γ · a = 1`**, given only the Laurent form `c · T⁻¹` of the swapped section's unit. -/
theorem graphBasePairing_firstFiberClass_of_monomial (p : ℕ) (c : kˣ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (swappedSectionUnit (k := k) p 0)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T (-1)) :
    graphBasePairing (k := k) p firstFiberClass = 1 := by
  rw [graphBasePairing_firstFiberClass_swap, exponent_swappedSection_of_monomial p 0 c (-1) h,
    neg_neg]

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · a = 1`** on `stageSurface (n+1) hproj`, given only the Laurent form `c · T⁻¹` of the
swapped section's unit at `p = m + (n + 1)`. -/
theorem graphStrictPairing_firstFiber_of_monomial (m : ℕ) (c : kˣ)
    (h : ((overlapLaurentUnit k
        (overlapRestriction k (swappedSectionUnit (k := k) (m + (n + 1)) 0)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T (-1)) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) = 1 := by
  rw [graphStrictPairing_firstFiber_swap,
    exponent_swappedSection_of_monomial (m + (n + 1)) 0 c (-1) h, neg_neg]

end Rows

end KltDP.Examples.FrobeniusGraphSwapExponent

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLineTransitionExtension
open KltDP.Geometry.ProjectiveLineTransitionExponent
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassSwap
open FrobeniusGraphSwapExponent

/-- **The `a`-row is one Laurent form on the accepted atlas.** If the swapped section's refined
transition unit against `originalGraphAtlas q` reads `c · Tⁿ`, then the exponent of the graph ideal
line pulled back along that section is `n`. -/
theorem f29_swapped_section_exponent (k : Type u) [Field k] (p q : ℕ) (c : kˣ) (n : ℤ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (swappedSectionUnit (k := k) p q)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) :
    exponent k (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) q)) = n :=
  exponent_swappedSection_of_monomial p q c n h

/-- The bundle has exactly one universe parameter. -/
theorem f29_swapped_section_exponent_universe_check (k : Type u) [Field k] (p q : ℕ) (c : kˣ)
    (n : ℤ)
    (h : ((overlapLaurentUnit k (overlapRestriction k (swappedSectionUnit (k := k) p q)) :
        (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      LaurentPolynomial.C (c : k) * LaurentPolynomial.T n) : True := by
  have _ := f29_swapped_section_exponent.{u} k p q c n h
  trivial

end KltDP.Examples
