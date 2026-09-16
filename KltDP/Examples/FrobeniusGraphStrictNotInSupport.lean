import KltDP.Examples.FrobeniusStageVerticalDivisor
import KltDP.Examples.FrobeniusGraphStrictGenericPoint
import KltDP.Examples.FrobeniusGraphGenericPointOffFiber
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.CartierDivisorPullbackBlowdown
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Geometry.CartierDivisorPullbackSupport
import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Geometry.ProjectiveSpaceIntegral

/-!
# `B ⊄ Supp(x = c)`: the first `NotInSupport` derived from geometry (BRIEF45)

`NotInSupport C D hD` — the generic point of the prime curve `C` lies off the support of `D` — is the
side condition that gates `restrictCartier`, `intersectionScheme` and `intersectionDegree`, and hence
every intersection row. Across the accepted tree **it is only ever assumed**: it is threaded as a
hypothesis binder through `PrimeCurveIntersectionSymm`, `IntersectionLaws` and `IntersectionAdditive`,
and the single place it is ever built (`PrimeCurveIntersectionAdditive:92`) constructs it for a *sum*
from two given ones. Nothing discharges it from geometry for any curve and any divisor.

This module discharges it, for the strict transform `B` of the graph against the vertical fibre `x = c`
on the contact stage. `docs/GAPS.md` records the accepted `intersectionDegree_eq_sum_cartierOrderAt` as
vacuous; a `NotInSupport` produced rather than assumed is a direct step against that class of defect.

The proof is three steps and no computation, because the two hard parts are already done:

1. `stageVerticalDivisor N c` is **by definition** `pullbackDivisor (projectiveContactProjection N)
   (verticalFiberDivisorAt c) …`, so `not_mem_support_pullbackDivisor` applies — as a **term**: the
   `def` stays folded in the goal, and a term-level application sees through it where `rw`/`unfold`
   cannot. It reduces the statement to one about the image point downstairs on `P¹ × P¹`;
2. `f29_graph_strict_generic_point` identifies that image as the graph's generic point
   `(projectiveGraphMorphism (m + (n+1))).base (genericPoint (projectiveSpace k 1))`;
3. `graphGenericPoint_not_mem_support_verticalFiberAt` puts that point off the fibre.

* **`toInitial_graphStrictGenericPoint_not_mem_support`** — step 2 composed with step 3;
* **`graphStrict_notInSupport`** — the `NotInSupport` itself.

Holds for **every** `c` (including `c = 0`) and every residual exponent `m`: the graph meets each
vertical fibre in one point, so its generic point is never on one. `c ≠ 0` is needed downstream, to
keep the crossing off the centre of the tower, not here.

**Not proved here**: the same statement for the fibre strict transform `F̃`. The off-support half is
already available — `not_mem_support_verticalZero_of_fst_generic` is stated for an *arbitrary* point
whose first coordinate is generic — but the analogue of `f29_graph_strict_generic_point` for
`fiberClosureInclusion` does not exist in the accepted tree or any lane, and that identification, not
the off-support fact, is what the `F̃` row still needs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphStrictNotInSupport

-- `KltDP.Geometry.NormalProjectiveSurface.PrimeCurve` is deliberately NOT opened: `NotInSupport` and
-- `genericPoint` are both reached by dot notation on the prime curve, and opening that namespace
-- would shadow the topological `_root_.genericPoint` appearing in `f29_graph_strict_generic_point`.
open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStrictTransformPrimeCurves
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusGraphGenericPointOffFiber
open CartierDivisorPullbackBlowdown
open FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

-- The four integrality instances, in dependency order. A `local instance` reaches neither an
-- importing module nor a later namespace block, so both blocks of this file declare all four.
local instance notInSupportProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

-- The `.carrier` form is a *separate* instance: search does not reduce the projection
-- `projectiveProductInitial.carrier` to `projectiveProduct k`, which is why four accepted modules
-- each declare exactly this.
local instance notInSupportInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance notInSupportStageIntegral (m : ℕ) :
    IsIntegral (projectiveContactStage (k := k) m) :=
  instStageIsIntegral (projectiveProductInitial (k := k)) m

-- Needed to elaborate `_root_.genericPoint (projectiveSpace k 1)` inside the *statement* of
-- `f29_graph_strict_generic_point`; `irreducibleSpace_of_isIntegral` is an instance.
local instance notInSupportLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **The blowdown image of `B`'s generic point is off the vertical fibre `x = c`.**
`f29_graph_strict_generic_point` rewrites the point into the graph's generic point, which the
previous module put off the fibre. -/
theorem toInitial_graphStrictGenericPoint_not_mem_support (m : ℕ) (c : k) :
    (projectiveContactProjection (k := k) (n + 1)).base
        ((graphStrictPrimeCurve n hproj m).genericPoint) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  rw [f29_graph_strict_generic_point k n hproj m]
  exact graphGenericPoint_not_mem_support_verticalFiberAt (m + (n + 1)) c

/-- **`B` is not contained in the support of the stage vertical fibre `x = c`.**
The first `NotInSupport` in this development obtained from geometry rather than assumed.
`stageVerticalDivisor` is a `pullbackDivisor` by definition, so `not_mem_support_pullbackDivisor`
applies as a term through the folded `def`. -/
theorem graphStrict_notInSupport (m : ℕ) (c : k) :
    (graphStrictPrimeCurve n hproj m).NotInSupport
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c) :=
  not_mem_support_pullbackDivisor (projectiveContactProjection (k := k) (n + 1))
    (verticalFiberDivisorAt (k := k) c) (verticalFiberDivisorAt_hasRegularEquations c)
    ((graphStrictPrimeCurve n hproj m).genericPoint)
    (toInitial_graphStrictGenericPoint_not_mem_support n hproj m c)

end KltDP.Examples.FrobeniusGraphStrictNotInSupport

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStrictTransformPrimeCurves
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusGraphStrictNotInSupport
open FrobeniusTowerFunctionField FrobeniusTowerFunctionField.PlaneChartedScheme

local instance notInSupportProductIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance notInSupportInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance notInSupportStageIntegral' {k : Type u} [Field k] (m : ℕ) :
    IsIntegral (projectiveContactStage (k := k) m) :=
  instStageIsIntegral (projectiveProductInitial (k := k)) m

local instance notInSupportLineIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- **F29: the strict transform `B` of the graph is not contained in the support of the vertical
fibre `x = c`** — the `NotInSupport` side condition that `restrictCartier`, `intersectionScheme` and
`intersectionDegree` require, here **produced from geometry** rather than assumed, for every residual
exponent `m` and every `c`. -/
theorem f29_graph_strict_not_in_support (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) :
    (graphStrictPrimeCurve n hproj m).NotInSupport
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c) :=
  graphStrict_notInSupport n hproj m c

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_strict_not_in_support_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) : True := by
  have _ := f29_graph_strict_not_in_support.{u} k n hproj m c
  trivial

end KltDP.Examples
