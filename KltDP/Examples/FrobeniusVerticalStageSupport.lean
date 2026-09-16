import KltDP.Examples.FrobeniusVerticalSupportCrossing
import KltDP.Examples.FrobeniusVerticalGermTransport
import KltDP.Examples.CartierDivisorPullbackBlowdown
import KltDP.Geometry.CartierDivisorPullbackSupport

/-!
# The crossing point lies in the support of the STAGE vertical divisor (BRIEF55)

BRIEF54 pinned the support of `x = c` from both sides on `P¹ × P¹`. This module lifts the
**nonempty** half up the tower, which BRIEF54's record flagged as the short remaining step: the
crossing point of `B` on the contact stage lies in `Supp(stageVerticalDivisor (n+1) c)`.

It is short for the reason the record predicted. `stageVerticalDivisor N c` is **by definition**
`pullbackDivisor (projectiveContactProjection N) (verticalFiberDivisorAt c) _`, and this lane's
`mem_support_pullbackDivisor_iff` is an **iff**, so the direction that was never used — `.mpr`,
membership upstairs from membership downstairs — costs nothing once a stage point over the crossing
point is in hand. `stageCrossingPoint` (BRIEF52) is exactly such a point, and
`stageCrossingPoint_toInitial` says its blowdown image is the graph point `(c, c^p)`.

The `GenericPointPreserving` instance the criterion needs is the accepted
`projectiveContactProjection_genericPointPreserving`; no new hypothesis is introduced.

* **`graphPoint_mem_support_verticalFiberAt`** — the graph point `(c, c^p)` lies in `Supp(x = c)`,
  BRIEF54's statement with the point rewritten from the chart form to `graphPoint` (point-level, inside
  a `Prop`, so no cast);
* **`stageCrossingPoint_mem_support_stageVerticalDivisor`** — hence the stage crossing point lies in
  `Supp(stageVerticalDivisor (n+1) c)`.

## What this does NOT give — the count is still not closed

This is the **nonempty** half only, and even that is a statement about a *point of the stage*, not yet
about the intersection scheme. What remains for `B ∩ Supp D` to be a singleton:

* turning this into `Nonempty ((graphStrictPrimeCurve …).intersectionScheme …)` — the accepted
  `range_intersectionToSurface` says that range is `(C : Set X) ∩ Supp D`, and the stage crossing point
  is in both (it is `strictTransformι.base` of a point of `B`, and `coe_graphStrictPrimeCurve` is
  `rfl`), so this looks like the same kind of short step — **not done here**;
* the **subsingleton** half, which still needs the range of `verticalLift` characterised. Nothing
  characterises it; that is research-shaped and is deliberately not started.

`c ≠ 0` is not needed: this statement lives below the tower stalk transport, where `c ≠ 0` enters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalStageSupport

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor
open FrobeniusVerticalChartBookkeeping
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk
open FrobeniusVerticalGermTransport
open FrobeniusVerticalSupportCrossing

variable {k : Type u} [Field k]

-- `mem_support_pullbackDivisor_iff` carries `[IsIntegral X] [IsIntegral Y]` in its statement, and the
-- `.carrier` form is a separate instance: search does not reduce `projectiveProductInitial.carrier`.
local instance stageSupportProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance stageSupportInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance stageSupportStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- **The graph point `(c, c^p)` lies in the support of the vertical fibre `x = c`.** BRIEF54's
statement, with the point rewritten from the chart form `projectiveGraphMorphism.base (lineParamPoint c)`
into `graphPoint`. Both rewrites are point-level inside a `Prop`, so nothing is transported. -/
theorem graphPoint_mem_support_verticalFiberAt (p : ℕ) (c : k) :
    graphPoint p c ∈
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  -- Rewrite the GOAL backwards, not the hypothesis forwards: `lineParamPoint` is an `abbrev`, so it
  -- is defeq but not syntactically equal and `rw` matches syntactically, whereas the goal's
  -- `graphPoint p c` is exactly the RHS of `graphMorphism_base_point`. `exact` then absorbs the
  -- abbrev's defeq, which `rw` would not.
  rw [← graphMorphism_base_point p c, ← polynomialLineChart_point c]
  exact crossingPoint_mem_support_verticalFiberAt p c

variable (n m : ℕ)

/-- **The stage crossing point lies in the support of the stage vertical divisor.** The nonempty half
of the count, lifted up the tower: `stageVerticalDivisor` is a `pullbackDivisor` by definition, so the
`.mpr` direction of `mem_support_pullbackDivisor_iff` applies as a term through the folded `def`, and
`stageCrossingPoint_toInitial` identifies the blowdown image as the graph point. -/
theorem stageCrossingPoint_mem_support_stageVerticalDivisor (c : k) :
    stageCrossingPoint n m c ∈
      (effectiveCartierIdealDataOfRegularEquations (projectiveContactStage (k := k) (n + 1))
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)).support := by
  refine (mem_support_pullbackDivisor_iff (projectiveContactProjection (k := k) (n + 1))
    (verticalFiberDivisorAt (k := k) c) (verticalFiberDivisorAt_hasRegularEquations c)
    (stageCrossingPoint n m c)).mpr ?_
  rw [stageCrossingPoint_toInitial]
  exact graphPoint_mem_support_verticalFiberAt (m + (n + 1)) c

end KltDP.Examples.FrobeniusVerticalStageSupport

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusVerticalGermTransport
open FrobeniusVerticalStageSupport

local instance stageSupportProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance stageSupportInitialIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance stageSupportStageIntegralTop {k : Type u} [Field k] (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- **F29: the crossing point of `B` lies in the support of the stage vertical divisor `x = c`.**
The nonempty half of the intersection count, lifted from `P¹ × P¹` to the contact stage. Derived from
BRIEF54 and BRIEF52; no new geometry and no new hypothesis. -/
theorem f29_vertical_stage_support_crossing (k : Type u) [Field k] (n m : ℕ) (c : k) :
    stageCrossingPoint n m c ∈
      (effectiveCartierIdealDataOfRegularEquations (projectiveContactStage (k := k) (n + 1))
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)).support :=
  stageCrossingPoint_mem_support_stageVerticalDivisor n m c

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_stage_support_crossing_universe_check (k : Type u) [Field k] (n m : ℕ) (c : k) :
    True := by
  have _ := f29_vertical_stage_support_crossing.{u} k n m c
  trivial

end KltDP.Examples
