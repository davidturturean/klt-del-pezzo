import KltDP.Examples.FrobeniusVerticalFiberTranslated
import KltDP.Examples.CartierDivisorPullbackBlowdown
import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusTowerFunctionField

/-!
# The vertical fibre on a contact stage, and its restricted coefficient (BRIEF34, leg 3)

Legs 1 and 2 identified the germ on the curve `B_n` and transported the vertical equation down the
blowdown tower. This module supplies the remaining leg: the divisor the intersection rows are actually
computed against, on the **stage surface**, together with the two coefficient steps that stand between
it and `C.restrictedCoefficient`.

The divisor `x = c` on `P¹ × P¹` is already a pullback along the translation `(τ_c × τ_0).inv`
(`verticalFiberDivisorAt`, whose chart coefficient is `rfl` to `(τ_c × τ_0).inv.app _ u`). Pulling it
back once more along the blowdown gives the stage divisor, mirroring the accepted

    totalFiberDivisor N = pullbackDivisor (between …) fiberZeroDivisor fiberZeroDivisor_hasRegularEquations

for the horizontal fibre. The instances this needs are accepted: `instStageIsIntegral` and
`projectiveContactProjection_genericPointPreserving`.

* `stageVerticalDivisor N c` — the vertical fibre `x = c` pulled back to stage `N`, with
  `stageVerticalDivisor_hasRegularEquations` free from `pullbackDivisor_hasRegularEquations`;
* `stageVerticalDivisor_chart N c d` — its regular chart, and **`stageVerticalDivisor_chart_coefficient`**,
  the **second** `pullbackDivisor_regularChart_coefficient` step: the coefficient is
  `π.app _ ((τ_c × τ_0).inv.app _ d.coefficient)`, both steps `rfl`;
* **`restrictedCoefficient_stageVerticalDivisor`** — the **third** step: restricting to a prime curve
  applies `C.inclusion.app`, so the restricted coefficient is
  `C.inclusion.app _ (π.app _ ((τ_c × τ_0).inv.app _ u))`;
* `stageVerticalChartZero N c j` — the concrete chart, from the `u`-chart of `x = 0`.

`NotInSupport` is taken as a **hypothesis** throughout: `restrictCartier` is defined by choice on an
existence statement and `NotInSupport` is a real side condition on the generic point of the curve, so
it is not discharged here. What this module delivers is the coefficient chain, which is what the rows
consume once that side condition is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageVerticalDivisor

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open CartierDivisorPullbackBlowdown FrobeniusStageSurface
open FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

/-- Integrality of the product: supplied by the accepted modules only as a `local instance`, which
reaches neither importing modules nor a later namespace block. -/
local instance stageProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The same integrality in the `.carrier` form that `instStageIsIntegral`'s section hypothesis
`[IsIntegral A.carrier]` actually asks for at `A = projectiveProductInitial`. Instance search does not
reduce `projectiveProductInitial.carrier` to `projectiveProduct k`, which is why four accepted modules
(`FrobeniusExceptionalCartier`, `FrobeniusTowerCartierIdentity`, `FrobeniusStageOneCharts`,
`FrobeniusTowerFiberPullback`) each declare exactly this instance instead of relying on the product one. -/
local instance stageInitialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Integrality of each contact stage, from the accepted `instStageIsIntegral`. The accepted module
that builds `totalFiberDivisor` likewise declares its integrality instances locally rather than
relying on propagation. -/
local instance contactStageIntegral (n : ℕ) : IsIntegral (projectiveContactStage (k := k) n) :=
  instStageIsIntegral (projectiveProductInitial (k := k)) n

section Stage

variable (N : ℕ)

/-- **The vertical fibre `x = c`, pulled back to the contact stage `N`.** The mirror of the accepted
`totalFiberDivisor` for the horizontal fibre, along the same blowdown. -/
def stageVerticalDivisor (c : k) : CartierDivisor (projectiveContactStage (k := k) N) :=
  pullbackDivisor (projectiveContactProjection (k := k) N) (verticalFiberDivisorAt c)
    (verticalFiberDivisorAt_hasRegularEquations c)

/-- **It has regular equations**, so it restricts to prime curves. -/
theorem stageVerticalDivisor_hasRegularEquations (c : k) :
    HasRegularCartierEquations (projectiveContactStage (k := k) N)
      (stageVerticalDivisor (k := k) N c) :=
  pullbackDivisor_hasRegularEquations _ _ _

/-- A regular chart of the stage divisor for each chart of `x = c`. -/
def stageVerticalDivisor_chart (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalFiberDivisorAt (k := k) c)) :
    RegularCartierEquationChart (projectiveContactStage (k := k) N)
      (stageVerticalDivisor (k := k) N c) :=
  pullbackDivisor_regularChart (projectiveContactProjection (k := k) N)
    (verticalFiberDivisorAt c) (verticalFiberDivisorAt_hasRegularEquations c) d

/-- Its chart open is the blowdown preimage of the chart open downstairs. -/
theorem stageVerticalDivisor_chart_openSet (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalFiberDivisorAt (k := k) c)) :
    (stageVerticalDivisor_chart N c d).chart.openSet =
      (projectiveContactProjection (k := k) N) ⁻¹ᵁ d.chart.openSet := rfl

/-- **The second coefficient step.** The chart coefficient upstairs is the blowdown pullback of the
coefficient downstairs. -/
theorem stageVerticalDivisor_chart_coefficient (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalFiberDivisorAt (k := k) c)) :
    (stageVerticalDivisor_chart N c d).coefficient =
      (projectiveContactProjection (k := k) N).app d.chart.openSet d.coefficient := rfl

/-- **Both pullback steps at once**, on the concrete `u`-chart of `x = 0`: the stage coefficient is
the blowdown pullback of the translate of the vertical coordinate. -/
theorem stageVerticalDivisor_chart_coefficient_translated (c : k) (j : Fin 2) :
    (stageVerticalDivisor_chart N c (verticalFiberDivisorAt_chart c (verticalZeroChartZero j))).coefficient =
      (projectiveContactProjection (k := k) N).app
        ((verticalTranslation c).inv ⁻¹ᵁ productOpen 0 j)
        ((verticalTranslation c).inv.app (productOpen 0 j) (verticalZeroChartEquation j)) := rfl

/-- The concrete regular chart of the stage divisor coming from the `u`-chart of `x = 0`. -/
def stageVerticalChartZero (c : k) (j : Fin 2) :
    RegularCartierEquationChart (projectiveContactStage (k := k) N)
      (stageVerticalDivisor (k := k) N c) :=
  stageVerticalDivisor_chart N c (verticalFiberDivisorAt_chart c (verticalZeroChartZero j))

end Stage

section Restriction

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **The third step.** Restricting the stage divisor to a prime curve applies `C.inclusion.app`, so
the restricted coefficient is the curve pullback of the stage coefficient — which, by the two steps
above, is the blowdown pullback of the translate of `u`. -/
theorem restrictedCoefficient_stageVerticalDivisor (C : (stageSurface (n + 1) hproj).PrimeCurve)
    (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalFiberDivisorAt (k := k) c)) :
    C.restrictedCoefficient (stageVerticalDivisor (n + 1) c)
        (stageVerticalDivisor_chart (n + 1) c d) =
      C.inclusion.app ((projectiveContactProjection (k := k) (n + 1)) ⁻¹ᵁ d.chart.openSet)
        ((projectiveContactProjection (k := k) (n + 1)).app d.chart.openSet d.coefficient) := rfl

/-- The same on the concrete `u`-chart: the full three-step chain, all by `rfl`. -/
theorem restrictedCoefficient_stageVerticalChartZero
    (C : (stageSurface (n + 1) hproj).PrimeCurve) (c : k) (j : Fin 2) :
    C.restrictedCoefficient (stageVerticalDivisor (n + 1) c) (stageVerticalChartZero (n + 1) c j) =
      C.inclusion.app
        ((projectiveContactProjection (k := k) (n + 1)) ⁻¹ᵁ
          ((verticalTranslation c).inv ⁻¹ᵁ productOpen 0 j))
        ((projectiveContactProjection (k := k) (n + 1)).app
          ((verticalTranslation c).inv ⁻¹ᵁ productOpen 0 j)
          ((verticalTranslation c).inv.app (productOpen 0 j) (verticalZeroChartEquation j))) := rfl

end Restriction

end KltDP.Examples.FrobeniusStageVerticalDivisor

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusStageSurface
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusTowerFunctionField
open FrobeniusTowerFunctionField.PlaneChartedScheme

local instance stageProductIntegral' {k : Type u} [Field k] : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance stageInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance contactStageIntegral' {k : Type u} [Field k] (n : ℕ) :
    IsIntegral (projectiveContactStage (k := k) n) :=
  instStageIsIntegral (projectiveProductInitial (k := k)) n

/-- **F29: the vertical fibre `x = c` as a Cartier divisor on a contact stage, with its restricted
coefficient on a prime curve** — the third leg of the germ chain the intersection rows consume. -/
theorem f29_stage_vertical_divisor (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (C : (stageSurface (n + 1) hproj).PrimeCurve) (c : k) (j : Fin 2) :
    HasRegularCartierEquations (projectiveContactStage (k := k) (n + 1))
        (stageVerticalDivisor (k := k) (n + 1) c) ∧
    C.restrictedCoefficient (stageVerticalDivisor (n + 1) c) (stageVerticalChartZero (n + 1) c j) =
      C.inclusion.app
        ((projectiveContactProjection (k := k) (n + 1)) ⁻¹ᵁ
          ((verticalTranslation c).inv ⁻¹ᵁ productOpen 0 j))
        ((projectiveContactProjection (k := k) (n + 1)).app
          ((verticalTranslation c).inv ⁻¹ᵁ productOpen 0 j)
          ((verticalTranslation c).inv.app (productOpen 0 j) (verticalZeroChartEquation j))) :=
  ⟨stageVerticalDivisor_hasRegularEquations (n + 1) c,
    restrictedCoefficient_stageVerticalChartZero n hproj C c j⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_stage_vertical_divisor_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (C : (stageSurface (n + 1) hproj).PrimeCurve) (c : k) (j : Fin 2) : True := by
  have _ := f29_stage_vertical_divisor.{u} k n hproj C c j
  trivial

end KltDP.Examples
