import KltDP.Examples.FrobeniusVerticalGermTransport
import KltDP.Examples.FrobeniusVerticalContactStalk

/-!
# The vertical equation's germ on the curve `B` (BRIEF52)

**This module supplies a step the lane's own rotation specification omitted, and the omission was an
ill-typed target.** That spec said to identify the *product* germ with `localParameter c`. Those are
elements of different rings: `openImmersionStalkLocalizationEquiv` at `productChart 0 0` lands in a
localisation of `planeRing k = Polynomial (Polynomial k)`, while `parameterLocalRing c` is a localisation
of `Polynomial k` (`parameterPointIdeal : Ideal (Polynomial k)`).

Geometrically the gap is clear once stated: the product germ lives in the **two-dimensional** local ring of
the surface, where the vertical equation cuts a *curve*, not a point. It is not a uniformizer there. It
becomes the local parameter only **after restriction to `B`**, in the one-dimensional local ring — and
`crossing_contact_length_pow` confirms this is what the rows need, since it demands a germ on
`strictTransform`, not on the stage and not on the product.

So the chain needs one more transport than the spec listed, and this module is it:

* **`curveVerticalGerm`** — the germ on `B` of the divisor's chart coefficient restricted along
  `strictTransformι`;
* **`stalkMap_stageVerticalChartZero`** — it is the image of the stage germ under
  `strictTransformι.stalkMap`, by `Scheme.stalkMap_germ_apply`. Composed with the previous round's
  `towerStalkEquiv_stageVerticalChartZero`, the divisor's coefficient now reaches `B`'s stalk.

Indexing is definitional, not transported: `FrobeniusVerticalContactStalk.crossingPoint` and
`FrobeniusVerticalContactLength.verticalCrossingPoint` unfold to the same term (`lineParamPoint` is an
`abbrev`), so the germ here and `crossingStalkEquiv` share one index and no stalk is moved along an
equality of points. Both bare names are ambiguous with `FrobeniusSecondChartCrossing`, so every reference
is qualified.

**Not proved here**: `crossingStalkEquiv n m c (curveVerticalGerm …) = localParameter c`. That is now the
single remaining statement, and it is the research-shaped one: it needs the `P¹`-side identification
through `graphStrictIsoProjectiveLine_hom_comp`, i.e. the pullback of the translated section along the
graph morphism. No row is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusVerticalCurveGerm

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusVerticalGermTransport

variable {k : Type u} [Field k]

-- Rule 8: an instance the *type* needs is not optional. `(stageVerticalChartZero …).chart.openSet`
-- mentions `RegularCartierEquationChart X D`, which carries `[IsIntegral X]`, and
-- `FrobeniusStageVerticalDivisor` supplies these only as `local instance`s that do not reach an
-- importing module. The `.carrier` form is separate: search does not reduce the projection.
local instance curveGermProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance curveGermInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance curveGermStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

variable (n m : ℕ)

/-- **The germ on `B` of the divisor's chart coefficient**, restricted along `strictTransformι`.
This is the germ `crossing_contact_length_pow` consumes — a germ on `strictTransform`, which is what the
rows require and what the stage-level transport alone does not provide. -/
def curveVerticalGerm (c : k) :
    (strictTransform (k := k) (n + 1) (m + (n + 1))).presheaf.stalk
      (FrobeniusVerticalContactStalk.crossingPoint (n + 1) m c) :=
  (strictTransform (k := k) (n + 1) (m + (n + 1))).presheaf.germ
    (strictTransformι (k := k) (n + 1) (m + (n + 1)) ⁻¹ᵁ
      (stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
    (FrobeniusVerticalContactLength.verticalCrossingPoint (n + 1) m c)
    (stageCrossingPoint_mem_translatedOpen n m c)
    ((strictTransformι (k := k) (n + 1) (m + (n + 1))).app
      ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
      ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient))

/-- **The stage germ maps to it under `strictTransformι.stalkMap`.** Direct instantiation of
`Scheme.stalkMap_germ_apply`; composed with `towerStalkEquiv_stageVerticalChartZero` it carries the
divisor's coefficient all the way from `P¹ × P¹` to the stalk of `B`. -/
theorem stalkMap_stageVerticalChartZero (c : k) :
    (strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap
        (FrobeniusVerticalContactLength.verticalCrossingPoint (n + 1) m c)
        ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
          ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
          (stageCrossingPoint n m c)
          (stageCrossingPoint_mem_translatedOpen n m c)
          ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient)) =
      curveVerticalGerm n m c :=
  Scheme.stalkMap_germ_apply (strictTransformι (k := k) (n + 1) (m + (n + 1)))
    ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
    (FrobeniusVerticalContactLength.verticalCrossingPoint (n + 1) m c)
    (stageCrossingPoint_mem_translatedOpen n m c)
    ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient)

end KltDP.Examples.FrobeniusVerticalCurveGerm

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusVerticalFiberTranslated FrobeniusStageVerticalDivisor
open FrobeniusVerticalGermTransport FrobeniusVerticalCurveGerm

local instance curveGermProductIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance curveGermInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance curveGermStageIntegral' {k : Type u} [Field k] (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- **F29: the vertical divisor's coefficient reaches the stalk of `B`.** The step the lane's rotation
spec omitted — the product germ lives in the surface's two-dimensional local ring and is not the local
parameter there; only after restriction to the curve can it be. -/
theorem f29_vertical_curve_germ (k : Type u) [Field k] (n m : ℕ) (c : k) :
    (strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap
        (FrobeniusVerticalContactLength.verticalCrossingPoint (n + 1) m c)
        ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
          ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
          (stageCrossingPoint n m c)
          (stageCrossingPoint_mem_translatedOpen n m c)
          ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient)) =
      curveVerticalGerm n m c :=
  stalkMap_stageVerticalChartZero n m c

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_curve_germ_universe_check (k : Type u) [Field k] (n m : ℕ) (c : k) :
    True := by
  have _ := f29_vertical_curve_germ.{u} k n m c
  trivial

end KltDP.Examples
