import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.InvertibleSheafPicard
import KltDP.Geometry.SchemePicardPullback
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.ProjectiveLineSheafExponent
import KltDP.Geometry.ProjectiveLinePicardExponent
import KltDP.Geometry.ProjectiveLineIdealLineDegree
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
import KltDP.Examples.FrobeniusGraphPicardClassSwap
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses
import KltDP.Examples.FrobeniusGraphBaseRows

/-!
# The `a`-row is the `b`-row of the swapped section

The two open exponents behind the F29 ruling rows are

* `exponent ((projectiveGraphMorphism p)^* graphIdealLine 0)`   (the `b`-row), and
* `exponent ((projectiveGraphMorphism p)^* verticalFiberIdealLine)`   (the `a`-row).

The accepted record describes the second as needing "a swap-compatible atlas", because
`verticalFiberIdealLine` is defined by transporting `graphIdealLine 0` across `productSwapIso` and
therefore carries no atlas of its own. **No such atlas is needed.** The accepted
`FrobeniusGraphPicardClassFiberClasses.verticalFiberIdealLine_toPic` already identifies the two in
the *Picard group*, and on `P¹` the transition exponent is a function of the Picard class alone
(accepted `ProjectiveLinePicardExponent.value_toPic`). Composing the two pullbacks with the accepted
`schemePicardPullbackHom_comp` therefore gives

**`exponent_verticalFiberIdealLine_eq_swap :`**
  `exponent ((projectiveGraphMorphism p)^* verticalFiberIdealLine)`
  `= exponent ((projectiveGraphMorphism p ≫ (productSwapIso).inv)^* graphIdealLine 0)`,

i.e. the `a`-row is the *same* quantity as the `b`-row, read along the swapped section
`projectiveGraphMorphism p ≫ (productSwapIso).inv` instead of along `projectiveGraphMorphism p`.

Consequently both ruling rows — for the base graph `Γ` (`graphBasePairing_firstFiberClass_swap`)
and for the strict transform `B` on `stageSurface (n+1) hproj`
(`graphStrictPairing_firstFiber_swap`) — are exponents of the **one** accepted atlas
`originalGraphAtlas 0` of `graphIdealLine 0`, differing only in which section of `P¹ ⟶ P¹ ×_k P¹`
they are pulled back along. The accepted machinery that consumes them
(`ProjectiveLineCocycleRefinement.exponent_pullback_eq_of_monomial`, and its unconditional form
`FrobeniusStrictTransformFiberRowsClosure.exponent_pullback_eq_of_monomial_unconditional`) is
generic in that section, so it applies verbatim to the swapped one.

**Deliberately not proved here.** No value for either exponent. In particular the chart-refinement
hypothesis for the swapped section (`standardOpens i ≤ (projectiveGraphMorphism p ≫
(productSwapIso).inv) ⁻¹ᵁ diagonalOpen i`, the analogue of the accepted
`FrobeniusStrictTransformFiberRowsExponents.chartOpen_le_preimage_diagonal`) is neither stated nor
assumed, and neither Laurent form is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphFirstRulingSwap

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ProjectiveLineSheafExponent
open KltDP.Geometry.ProjectiveLinePicardExponent
open KltDP.Geometry.ProjectiveLineIdealLineDegree
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassTotalTransform
open FrobeniusGraphPicardClassSwap FrobeniusGraphPicardClassFiberClasses
open FrobeniusGraphBaseRows

variable {k : Type u} [Field k]

/-- On `P¹` the transition exponent depends only on the Picard class of the line bundle: it is the
accepted class-level `value`. -/
theorem exponent_eq_of_toPic_eq (L M : InvertibleSheaf (projectiveSpace k 1))
    (h : L.toPic = M.toPic) : exponent k L = exponent k M := by
  rw [← value_toPic k L, h, value_toPic]

/-- **The pullback of the vertical ruling ideal along the graph section has the Picard class of the
pullback of the accepted graph ideal line along the swapped section.** -/
theorem pullback_verticalFiberIdealLine_toPic (p : ℕ) :
    (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
        (verticalFiberIdealLine (k := k))).toPic =
      (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) 0)).toPic := by
  rw [← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic,
    schemePicardPullbackHom_comp, MonoidHom.comp_apply, verticalFiberIdealLine_toPic]

/-- **The `a`-exponent is the `b`-exponent of the swapped section.** No atlas for
`verticalFiberIdealLine` is constructed or assumed. -/
theorem exponent_verticalFiberIdealLine_eq_swap (p : ℕ) :
    exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
        (verticalFiberIdealLine (k := k))) =
      exponent k (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) 0)) :=
  exponent_eq_of_toPic_eq _ _ (pullback_verticalFiberIdealLine_toPic p)

section Rows

variable [IsAlgClosed k]

/-- **`Γ · a = −exponent ((projectiveGraphMorphism p ≫ swap⁻¹)^* graphIdealLine 0)`**: the base
graph's `a`-row, on the accepted atlas of `graphIdealLine 0`. -/
theorem graphBasePairing_firstFiberClass_swap (p : ℕ) :
    graphBasePairing (k := k) p firstFiberClass =
      -exponent k (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) 0)) := by
  rw [graphBasePairing_firstFiberClass, exponent_verticalFiberIdealLine_eq_swap]

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B · a = −exponent ((projectiveGraphMorphism p ≫ swap⁻¹)^* graphIdealLine 0)`** on
`stageSurface (n+1) hproj`, with `p = m + (n + 1)`: the strict transform's `a`-row, on the same
accepted atlas as its `b`-row. -/
theorem graphStrictPairing_firstFiber_swap (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) =
      -exponent k (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) (m + (n + 1)) ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) 0)) := by
  rw [graphStrictPairing_firstFiber_exponent, exponent_verticalFiberIdealLine_eq_swap]

end Rows

end KltDP.Examples.FrobeniusGraphFirstRulingSwap

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.ProjectiveLineSheafExponent
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassSwap
open FrobeniusGraphPicardClassFiberClasses FrobeniusGraphFirstRulingSwap

/-- **Both F29 ruling exponents live on the single accepted atlas of `graphIdealLine 0`.** The
`a`-row exponent, defined with the transported `verticalFiberIdealLine`, equals the `b`-row
exponent of the graph ideal line pulled back along the swapped section. -/
theorem f29_graph_first_ruling_swap (k : Type u) [Field k] (p : ℕ) :
    exponent k (pullbackInvertibleSheaf (projectiveGraphMorphism (k := k) p)
        (verticalFiberIdealLine (k := k))) =
      exponent k (pullbackInvertibleSheaf
        (projectiveGraphMorphism (k := k) p ≫ (productSwapIso (k := k)).inv)
        (graphIdealLine (k := k) 0)) :=
  exponent_verticalFiberIdealLine_eq_swap p

/-- The bundle has exactly one universe parameter. -/
theorem f29_graph_first_ruling_swap_universe_check (k : Type u) [Field k] (p : ℕ) : True := by
  have _ := f29_graph_first_ruling_swap.{u} k p
  trivial

end KltDP.Examples
