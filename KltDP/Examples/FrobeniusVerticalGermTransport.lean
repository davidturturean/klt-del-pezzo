import KltDP.Examples.FrobeniusVerticalChartBookkeeping
import KltDP.Examples.FrobeniusStageVerticalDivisor
import KltDP.Examples.FrobeniusStagePunctureStalk
import KltDP.Examples.FrobeniusVerticalContactLength
import KltDP.Examples.FrobeniusTowerFunctionField

/-!
# The vertical equation's germ on a contact stage at the crossing point (BRIEF50)

The rows need the germ of the **actual divisor's** chart coefficient at the crossing point. This module
supplies the stage-level half of that transport, at the **translated** equation — the one
`stageVerticalDivisor c` actually carries.

The distinction matters and is why the queued `FrobeniusStageVerticalGerm` does not already do this: that
module transports the germ of `verticalZeroChartEquation j`, the equation of `x = 0`. The divisor the rows
are computed against is `x = c`, whose stage chart coefficient is
`π.app _ ((verticalTranslation c).inv.app _ (verticalZeroChartEquation j))` — one `.app` further out, by
`stageVerticalDivisor_chart_coefficient`, which is `rfl`.

Two inputs come together here, and **this is where `c ≠ 0` finally enters**, exactly where it was predicted
to three briefs ago:

* the point lies in the chart open — `translatedCrossingPoint_mem_productOpen` of the previous round,
  after `verticalCrossingPoint_toInitial`, `polynomialLineChart_point` and `graphMorphism_base_point`
  identify the blowdown image of the crossing point as the graph point `(c, c^p)`;
* the point lies in the **stage puncture** — `verticalCrossingPoint_mem_stagePuncture`, which needs
  `c ≠ 0` because the centre of the tower sits over `x = 0`. Without it the tower stalk map is not an
  isomorphism there and no transport exists.

* `stageCrossingPoint` — the crossing point pushed into the stage;
* **`stageCrossingPoint_toInitial`** — its blowdown image is the graph point `(c, c^p)`;
* **`stageCrossingPoint_mem_translatedOpen`** — it lies in the divisor's chart open;
* **`towerStalkEquiv_stageVerticalChartZero`** — the tower transport carries the germ of the translated
  equation downstairs to the germ of the divisor's chart coefficient upstairs.

**Not proved here, and the remaining distance is exactly this**: identifying that product germ with
`localParameter c`. Leg 2 established the two presentations agree as elements of `planeRing k`
(`coordinateTranslation_uCoord_eq_pulledVertical`), but that is a **ring-level** identity; turning it into a
statement about the *section* `verticalZeroChartEquation j` requires transferring it across the chart's
`appIso`/`ΓSpecIso`, which is a separate module. Until that lands no row follows, so none is claimed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusVerticalGermTransport

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor StagePunctureStalkTransport
open FrobeniusVerticalChartBookkeeping

variable {k : Type u} [Field k]

-- `FrobeniusStageVerticalDivisor` supplies these only as `local instance`s, which reach neither an
-- importing module nor a later namespace block, and `RegularCartierEquationChart X D` needs
-- `[IsIntegral X]` to elaborate `stageVerticalChartZero`'s type at all. The `.carrier` form is a
-- separate instance: search does not reduce `projectiveProductInitial.carrier` to `projectiveProduct k`.
local instance germTransportProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance germTransportInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance germTransportStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

variable (n m : ℕ)

/-- The crossing point of `B` with the vertical fibre, pushed into the contact stage.
`FrobeniusVerticalContactStalk.crossingPoint` and `FrobeniusSecondChartCrossing.crossingPoint` are two
distinct accepted/queued constants of the same bare name, so every reference here is qualified. -/
def stageCrossingPoint (c : k) : projectiveContactStage (k := k) (n + 1) :=
  (strictTransformι (k := k) (n + 1) (m + (n + 1))).base
    (FrobeniusVerticalContactLength.verticalCrossingPoint (n + 1) m c)

/-- **Its blowdown image is the graph point `(c, c^p)`.** -/
theorem stageCrossingPoint_toInitial (c : k) :
    (projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c) =
      graphPoint (m + (n + 1)) c := by
  change ((projectiveProductInitial (k := k)).toInitial (n + 1)).base
    ((strictTransformι (k := k) (n + 1) (m + (n + 1))).base
      (FrobeniusVerticalContactLength.verticalCrossingPoint (n + 1) m c)) = _
  rw [FrobeniusVerticalContactLength.verticalCrossingPoint_toInitial,
    FrobeniusVerticalContactLength.polynomialLineChart_point, graphMorphism_base_point]

/-- **It lies in the divisor's chart open**, the translated product chart. -/
theorem stageCrossingPoint_mem_translatedOpen (c : k) :
    (projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c) ∈
      (verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0 := by
  show (verticalTranslation (k := k) c).inv.base
    ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c)) ∈
      productOpen (k := k) 0 0
  rw [stageCrossingPoint_toInitial]
  exact translatedCrossingPoint_mem_productOpen (m + (n + 1)) c

variable [IsAlgClosed k]

/-- **The tower transport carries the germ of the translated vertical equation to the germ of the
divisor's chart coefficient.** `c ≠ 0` is required: the centre of the tower lies over `x = 0`, so only
off it is the tower stalk map an isomorphism. -/
theorem towerStalkEquiv_stageVerticalChartZero (c : k) (hc : c ≠ 0) :
    towerStalkEquiv (n + 1) (stageCrossingPoint n m c)
        (FrobeniusVerticalContactLength.verticalCrossingPoint_mem_stagePuncture (n + 1) m c hc)
        ((projectiveProduct k).presheaf.germ
          ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
          ((projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c))
          (stageCrossingPoint_mem_translatedOpen n m c)
          ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
            (verticalZeroChartEquation 0))) =
      (projectiveContactStage (k := k) (n + 1)).presheaf.germ
        ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
        (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
        ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient) :=
  towerStalkEquiv_germ (n + 1) (stageCrossingPoint n m c)
    (FrobeniusVerticalContactLength.verticalCrossingPoint_mem_stagePuncture (n + 1) m c hc)
    ((verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0)
    (stageCrossingPoint_mem_translatedOpen n m c)
    ((verticalTranslation (k := k) c).inv.app (productOpen (k := k) 0 0)
      (verticalZeroChartEquation 0))

end KltDP.Examples.FrobeniusVerticalGermTransport

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusVerticalFiberTranslated
open FrobeniusVerticalGermTransport

/-- **F29: the crossing point on the contact stage, its blowdown image, and its membership in the
divisor's chart open** — the stage-level half of the germ transport for the vertical fibre `x = c`. -/
theorem f29_vertical_germ_transport (k : Type u) [Field k] (n m : ℕ) (c : k) :
    (projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c) =
        graphPoint (m + (n + 1)) c ∧
      (projectiveContactProjection (k := k) (n + 1)).base (stageCrossingPoint n m c) ∈
        (verticalTranslation (k := k) c).inv ⁻¹ᵁ productOpen (k := k) 0 0 :=
  ⟨stageCrossingPoint_toInitial n m c, stageCrossingPoint_mem_translatedOpen n m c⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_germ_transport_universe_check (k : Type u) [Field k] (n m : ℕ) (c : k) :
    True := by
  have _ := f29_vertical_germ_transport.{u} k n m c
  trivial

end KltDP.Examples
