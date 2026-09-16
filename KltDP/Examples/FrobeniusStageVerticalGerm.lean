import KltDP.Examples.FrobeniusStagePunctureStalk
import KltDP.Examples.FrobeniusVerticalFiberClass

/-!
# The vertical equation germ upstairs on a contact stage (BRIEF32, task 2)

`FrobeniusCrossingGermParameter` discharges `crossingStalkEquiv f = localParameter c` on the curve
`B_n` itself. The rows need the same kind of statement one level up: the local equation of the
vertical fibre, pulled back from `P¹ × P¹` to a **contact stage**, with its germ identified at a
point of the stage puncture. That is the leg lane A2's `towerStalkEquiv_germ` was built for, and this
module instantiates it at the vertical chart data.

`stagePuncture A n` is by definition `A.toInitial n ⁻¹ᵁ initialPuncture A`, and
`projectiveContactProjection n` is by definition `(projectiveProductInitial).toInitial n`, so the
transport is indexed at the point itself and **no stalk is moved along an equality of points**.

* `stageVerticalEquation N j` — the local equation `u` of `x = 0` pulled back to stage `N`, i.e.
  `(projectiveContactProjection N).app (productOpen 0 j) (verticalZeroChartEquation j)`;
* **`towerStalkEquiv_stageVerticalEquation`** — the tower transport carries the germ of the vertical
  coordinate `u` downstairs to the germ of `stageVerticalEquation` upstairs. This is the chart join
  down the tower, with the puncture membership as a hypothesis so the statement stays reusable and
  free of any algebraic-closedness assumption.
* `stageVerticalGerm`, `stageVerticalGerm_eq` — the germ itself and its defining identity.

**Not proved here**, and named so the remaining distance is explicit: the divisor the rows are
computed against is `verticalFiberDivisorAt c`, a pullback of `x = 0` along the *translation*
`(τ_c × τ_0).inv`, so its stage chart coefficient is `π.app _ ((τ_c × τ_0).inv.app _ u)` — a second
`pullbackDivisor_regularChart_coefficient`; and `C.restrictedCoefficient` applies a third
`C.inclusion.app`, restricting from the stage to `B`. This module is one of those three legs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageVerticalGerm

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusGlobalBlowupStages FrobeniusStageComplement
open FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusFiberZeroInvertible FrobeniusVerticalFiberClass
open StagePunctureStalkTransport

variable {k : Type u} [Field k]

section Stage

variable (N : ℕ)

/-- The vertical local equation `u`, pulled back from `P¹ × P¹` to the contact stage `N`. -/
def stageVerticalEquation (j : Fin 2) :
    Γ(projectiveContactStage (k := k) N,
      (projectiveContactProjection (k := k) N) ⁻¹ᵁ productOpen 0 j) :=
  (projectiveContactProjection (k := k) N).app (productOpen 0 j) (verticalZeroChartEquation j)

/-- **The tower transport carries the germ of `u` to the germ of its pullback.** This is the chart
join down the blowdown tower; the puncture membership is a hypothesis, so the statement is reusable
at every stage and assumes nothing about `k`. -/
theorem towerStalkEquiv_stageVerticalEquation (j : Fin 2)
    (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N)
    (hU : (projectiveContactProjection (k := k) N).base x ∈ productOpen (k := k) 0 j) :
    towerStalkEquiv N x hx
        ((projectiveProduct k).presheaf.germ (productOpen 0 j)
          ((projectiveContactProjection (k := k) N).base x) hU
          (verticalZeroChartEquation j)) =
      (projectiveContactStage (k := k) N).presheaf.germ
        ((projectiveContactProjection (k := k) N) ⁻¹ᵁ productOpen 0 j) x hU
        (stageVerticalEquation N j) :=
  towerStalkEquiv_germ N x hx (productOpen 0 j) hU (verticalZeroChartEquation j)

/-- The germ of the pulled-back vertical equation at a punctured point of the stage. -/
def stageVerticalGerm (j : Fin 2) (x : projectiveContactStage (k := k) N)
    (hU : (projectiveContactProjection (k := k) N).base x ∈ productOpen (k := k) 0 j) :
    (projectiveContactStage (k := k) N).presheaf.stalk x :=
  (projectiveContactStage (k := k) N).presheaf.germ
    ((projectiveContactProjection (k := k) N) ⁻¹ᵁ productOpen 0 j) x hU
    (stageVerticalEquation N j)

/-- It is the image of the germ downstairs under the tower transport. -/
theorem stageVerticalGerm_eq (j : Fin 2) (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N)
    (hU : (projectiveContactProjection (k := k) N).base x ∈ productOpen (k := k) 0 j) :
    stageVerticalGerm N j x hU =
      towerStalkEquiv N x hx
        ((projectiveProduct k).presheaf.germ (productOpen 0 j)
          ((projectiveContactProjection (k := k) N).base x) hU
          (verticalZeroChartEquation j)) :=
  (towerStalkEquiv_stageVerticalEquation N j x hx hU).symm

end Stage

end KltDP.Examples.FrobeniusStageVerticalGerm

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusVerticalFiberClass
open StagePunctureStalkTransport FrobeniusStageVerticalGerm

/-- **F29: the vertical local equation pulled back to a contact stage, with its germ identified**
through lane A2's tower transport — the chart-join leg the intersection rows consume. -/
theorem f29_stage_vertical_germ (k : Type u) [Field k] (N : ℕ) (j : Fin 2)
    (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N)
    (hU : (projectiveContactProjection (k := k) N).base x ∈ productOpen (k := k) 0 j) :
    stageVerticalGerm N j x hU =
      towerStalkEquiv N x hx
        ((projectiveProduct k).presheaf.germ (productOpen 0 j)
          ((projectiveContactProjection (k := k) N).base x) hU
          (verticalZeroChartEquation j)) :=
  stageVerticalGerm_eq N j x hx hU

/-- The statement has exactly one universe parameter. -/
theorem f29_stage_vertical_germ_universe_check (k : Type u) [Field k] (N : ℕ) (j : Fin 2)
    (x : projectiveContactStage (k := k) N)
    (hx : x ∈ stagePuncture (projectiveProductInitial (k := k)) N)
    (hU : (projectiveContactProjection (k := k) N).base x ∈ productOpen (k := k) 0 j) : True := by
  have _ := f29_stage_vertical_germ.{u} k N j x hx hU
  trivial

end KltDP.Examples
