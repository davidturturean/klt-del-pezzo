import KltDP.Examples.FrobeniusVerticalSupportFibre
import KltDP.Examples.FrobeniusVerticalStageSupport
import KltDP.Examples.FrobeniusStrictCurveLift
import KltDP.Examples.FrobeniusGraphStrictNotInSupport
import KltDP.Examples.FrobeniusVerticalFibreCrossing
import KltDP.Examples.FrobeniusVerticalContactLength
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusSpecialFiberTower
import KltDP.Examples.FrobeniusStageComplement
import KltDP.Examples.FrobeniusGraphClosed
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusStageVerticalDivisor
import KltDP.Examples.CartierDivisorPullbackBlowdown
import KltDP.Geometry.CartierDivisorPullbackSupport
import KltDP.Geometry.PrimeCurveCartierRestriction
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusBlowupChartIteration
import KltDP.Examples.FrobeniusVerticalFiberClass
import KltDP.Examples.FrobeniusVerticalFiberTranslated
import KltDP.Examples.FrobeniusVerticalContactStalk
import KltDP.Examples.FrobeniusVerticalGermTransport
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# `B` meets the SUPPORT of the stage vertical divisor in at most one point (the count, subsingleton)

The rotation specification of this lane recorded the subsingleton half of the `B · a = 1` count as
research-shaped, on the ground that the accepted
`graphStrictPrimeCurve_inter_vertical_subsingleton` is stated against
`Set.range (verticalLift c hc (n+1)).base` while the sum formula runs over `B ∩ Supp D`, so that
bridging the two would need **the range of `verticalLift` characterised**, which nothing does.

**That analysis was wrong, and this module closes the gap without characterising that range.**
Reading the accepted proof rather than its statement shows the range of `verticalLift` is used for
exactly two things, and the support supplies both directly:

* `section_inter_verticalFiber_subsingleton` consumes a point of the vertical fibre **only** through
  `verticalFiber_fst`, i.e. only through `firstProjection.base _ = point c`; and
* `verticalLift_mem_stagePuncture` supplies stage-puncture membership, which
  `verticalCrossingPoint_mem_stagePuncture` derives from the *same* first-coordinate fact together
  with `originCenter_fst` and `c ≠ 0`.

And `FrobeniusVerticalSupportFibre.mem_support_verticalFiberAt_fst` says precisely that a point of
`Supp(x = c)` has first coordinate `point c`, while `mem_support_pullbackDivisor_iff` transports the
stage support to it. So the hypothesis "lies in the range of the lift" is replaced throughout by the
strictly weaker "lies in the support", which is what the intersection scheme actually offers.

* **`mem_stagePuncture_of_firstProjection_eq`** — a stage point whose blowdown has first coordinate
  `point c`, `c ≠ 0`, lies in the stage puncture (the generic form of
  `verticalCrossingPoint_mem_stagePuncture`);
* **`graphStrict_toInitial_eq_of_firstProjection_eq`** — a point of `B` whose blowdown has first
  coordinate `point c` blows down to the graph point over `point c`, because the graph is a section
  of the first projection;
* **`graphStrict_inter_support_subsingleton`** — hence `B ∩ Supp(stageVerticalDivisor (n+1) c)` has
  at most one point;
* **`graphStrict_intersectionScheme_subsingleton`** — hence the intersection *scheme* is a
  subsingleton, via the accepted `range_intersectionToSurface`;
* **`exists_graphStrict_intersection_crossing`** — and it is nonempty, with the crossing point of
  BRIEF52 as the witness, via `exists_intersection_point_of_mem_support` and the queued
  `stageCrossingPoint_mem_support_stageVerticalDivisor`.

## What this does NOT give

**No row.** This is the *count* only. `B · a = 1` further needs the sum formula collapsed at the one
point (the local term `cartierOrderAt_stageVerticalDivisor_eq_one` is queued) and, separately, the
identification of the divisor's Picard class with the table's `a`, for which lane F's accepted
`cartierPicardHom_pullbackDivisor_eq` is the input. Neither is done here. `B · b = p` and
`F̃ · a = 1` are untouched.

`c ≠ 0` is required and is used exactly where it always was: the centre of the contact tower lies
over `x = 0`, so only off it is the blowdown injective.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalSupportSubsingleton

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphClosed
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusStrictTransformIsoProjectiveLine
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor
open FrobeniusVerticalFibreCrossing
open FrobeniusVerticalContactLength FrobeniusVerticalContactStalk
open FrobeniusVerticalGermTransport
open FrobeniusVerticalSupportFibre FrobeniusVerticalStageSupport
open FrobeniusStrictCurveLift FrobeniusGraphStrictNotInSupport

variable {k : Type u} [Field k]

-- `mem_support_pullbackDivisor_iff` carries `[IsIntegral X] [IsIntegral Y]` in its STATEMENT, so
-- these are needed to elaborate the types below, not merely the proofs; and the `.carrier` form is a
-- separate instance, since search does not reduce `projectiveProductInitial.carrier`.
local instance supportSubsingletonProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance supportSubsingletonInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance supportSubsingletonStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- The first projection is a retraction of the graph section, pointwise. -/
theorem firstProjection_graphMorphism (p : ℕ) (t : projectiveSpace k 1) :
    (firstProjection (k := k)).base ((projectiveGraphMorphism (k := k) p).base t) = t := by
  change (projectiveGraphMorphism (k := k) p ≫ firstProjection).base t = t
  rw [projectiveGraphMorphism_fst]
  rfl

section AlgClosed

variable [IsAlgClosed k]

/-- **A stage point whose blowdown has first coordinate `point c`, `c ≠ 0`, lies in the stage
puncture.** The generic form of the accepted `verticalCrossingPoint_mem_stagePuncture`: its proof uses
nothing about the crossing point except this first-coordinate equality. -/
theorem mem_stagePuncture_of_firstProjection_eq (N : ℕ) (c : k) (hc : c ≠ 0)
    (z : projectiveContactStage (k := k) N)
    (hz : (firstProjection (k := k)).base
      ((projectiveContactProjection (k := k) N).base z) = point c) :
    z ∈ FrobeniusStageComplement.PlaneChartedScheme.stagePuncture
      (projectiveProductInitial (k := k)) N := by
  change ((projectiveProductInitial (k := k)).toInitial N).base z ≠
    (projectiveProductInitial (k := k)).chart.base (FrobeniusBlowupChartIteration.originPoint)
  intro h
  apply hc
  apply point_injective
  have h1 : (firstProjection (k := k)).base
      (((projectiveProductInitial (k := k)).toInitial N).base z) = point c := hz
  rw [h, originCenter_fst] at h1
  exact h1.symm

omit [IsAlgClosed k] in
/-- **A point of `B` whose blowdown has first coordinate `point c` blows down to the graph point over
`point c`.** The graph is a section of the first projection, so its first coordinate determines the
point; this is the content of the accepted `section_inter_verticalFiber_subsingleton`, restated
against the first coordinate instead of against the range of the vertical fibre. -/
theorem graphStrict_toInitial_eq_of_firstProjection_eq (n m : ℕ) (c : k)
    (z : projectiveContactStage (k := k) (n + 1))
    (hz : z ∈ Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base)
    (hfst : (firstProjection (k := k)).base
      ((projectiveContactProjection (k := k) (n + 1)).base z) = point c) :
    (projectiveContactProjection (k := k) (n + 1)).base z =
      (projectiveGraphMorphism (k := k) (m + (n + 1))).base (point c) := by
  obtain ⟨s, rfl⟩ := hz
  have hgraph : (projectiveGraphMorphism (k := k) (m + (n + 1))).base
      ((graphStrictIsoProjectiveLine (k := k) (n + 1) m).hom.base s) =
      (projectiveContactProjection (k := k) (n + 1)).base
        ((strictTransformι (k := k) (n + 1) (m + (n + 1))).base s) := by
    change ((graphStrictIsoProjectiveLine (k := k) (n + 1) m).hom ≫
      projectiveGraphMorphism (m + (n + 1))).base s = _
    rw [graphStrictIsoProjectiveLine_hom_comp (n + 1) m]
    rfl
  have hs : (graphStrictIsoProjectiveLine (k := k) (n + 1) m).hom.base s = point c := by
    have h2 := hfst
    rw [← hgraph, firstProjection_graphMorphism] at h2
    exact h2
  rw [← hgraph, hs]

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`B ∩ Supp(x = c)` has at most one point on the contact stage**, for `c ≠ 0`. The subsingleton
half of the intersection count, stated against the SUPPORT of the divisor — which is what the sum
formula runs over — rather than against the range of `verticalLift`. -/
theorem graphStrict_inter_support_subsingleton (m : ℕ) (c : k) (hc : c ≠ 0) :
    ((graphStrictPrimeCurve n hproj m : Set (stageSurface (n + 1) hproj).toScheme) ∩
      ((effectiveCartierIdealDataOfRegularEquations (stageSurface (n + 1) hproj).toScheme
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)).support :
          Set (stageSurface (n + 1) hproj).toScheme)).Subsingleton := by
  intro x hx y hy
  -- `stageVerticalDivisor` is a `pullbackDivisor` by definition, so `.mp` applies as a term through
  -- the folded `def`, where `rw` would need equation lemmas it does not supply.
  have hfx : (firstProjection (k := k)).base
      ((projectiveContactProjection (k := k) (n + 1)).base x) = point c :=
    mem_support_verticalFiberAt_fst c _
      ((mem_support_pullbackDivisor_iff (projectiveContactProjection (k := k) (n + 1))
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c) x).mp hx.2)
  have hfy : (firstProjection (k := k)).base
      ((projectiveContactProjection (k := k) (n + 1)).base y) = point c :=
    mem_support_verticalFiberAt_fst c _
      ((mem_support_pullbackDivisor_iff (projectiveContactProjection (k := k) (n + 1))
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c) y).mp hy.2)
  refine FrobeniusSpecialFiberTower.toInitial_injective_on_puncture
    (projectiveProductInitial (k := k)) (n + 1)
    (mem_stagePuncture_of_firstProjection_eq (n + 1) c hc x hfx)
    (mem_stagePuncture_of_firstProjection_eq (n + 1) c hc y hfy) ?_
  show (projectiveContactProjection (k := k) (n + 1)).base x =
    (projectiveContactProjection (k := k) (n + 1)).base y
  exact (graphStrict_toInitial_eq_of_firstProjection_eq n m c x hx.1 hfx).trans
    (graphStrict_toInitial_eq_of_firstProjection_eq n m c y hy.1 hfy).symm

/-- **The intersection scheme `B ∩ (x = c)` is a subsingleton.** The accepted
`range_intersectionToSurface` identifies its image with `B ∩ Supp D`, and a closed immersion is
injective on points. -/
theorem graphStrict_intersectionScheme_subsingleton (m : ℕ) (c : k) (hc : c ≠ 0) :
    Subsingleton ((graphStrictPrimeCurve n hproj m).intersectionScheme
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)) := by
  refine ⟨fun z w => ((graphStrictPrimeCurve n hproj m).intersectionToSurface
    (stageVerticalDivisor (k := k) (n + 1) c)
    (stageVerticalDivisor_hasRegularEquations (n + 1) c)
    (graphStrict_notInSupport n hproj m c)).isClosedEmbedding.injective ?_⟩
  have hz : ((graphStrictPrimeCurve n hproj m).intersectionToSurface
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)).base z ∈
      Set.range ((graphStrictPrimeCurve n hproj m).intersectionToSurface
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c)).base := ⟨z, rfl⟩
  have hw : ((graphStrictPrimeCurve n hproj m).intersectionToSurface
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)).base w ∈
      Set.range ((graphStrictPrimeCurve n hproj m).intersectionToSurface
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c)).base := ⟨w, rfl⟩
  rw [(graphStrictPrimeCurve n hproj m).range_intersectionToSurface] at hz hw
  exact graphStrict_inter_support_subsingleton n hproj m c hc hz hw

/-- **The intersection scheme is nonempty**, with BRIEF52's crossing point as the witness: the point
at which the queued local term `cartierOrderAt_stageVerticalDivisor_eq_one` is computed. -/
theorem exists_graphStrict_intersection_crossing (m : ℕ) (c : k) :
    ∃ z : (graphStrictPrimeCurve n hproj m).intersectionScheme
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c),
      ((graphStrictPrimeCurve n hproj m).intersectionInclusion
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c)).base z =
        (graphStrictLift n hproj m).base (crossingPoint (n + 1) m c) := by
  refine (graphStrictPrimeCurve n hproj m).exists_intersection_point_of_mem_support
    (stageVerticalDivisor (k := k) (n + 1) c)
    (stageVerticalDivisor_hasRegularEquations (n + 1) c)
    (graphStrict_notInSupport n hproj m c)
    ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)) ?_
  refine ((graphStrictPrimeCurve n hproj m).mem_support_restrictCartier_iff
    (stageVerticalDivisor (k := k) (n + 1) c)
    (stageVerticalDivisor_hasRegularEquations (n + 1) c)
    (graphStrict_notInSupport n hproj m c)
    ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))).mpr ?_
  rw [graphStrictLift_base n hproj m (crossingPoint (n + 1) m c)]
  exact stageCrossingPoint_mem_support_stageVerticalDivisor n m c

end AlgClosed

end KltDP.Examples.FrobeniusVerticalSupportSubsingleton

namespace KltDP.Examples

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusGraphStrictNotInSupport
open FrobeniusVerticalSupportSubsingleton

-- Re-declared: a `local instance` does not survive the `end` of its namespace block.
local instance supportSubsingletonProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance supportSubsingletonInitialIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance supportSubsingletonStageIntegralTop {k : Type u} [Field k] (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- **F29: `B` meets the support of the vertical fibre `x = c` in exactly one point of the
intersection scheme** — subsingleton and nonempty, for `c ≠ 0`. This is the count the sum formula
`graphStrict_intersectionDegree_eq_sum` needs; it is stated against the divisor's support, not
against the range of `verticalLift`, which is why no characterisation of that range is required. -/
theorem f29_graph_vertical_intersection_count (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) (hc : c ≠ 0) :
    Subsingleton ((graphStrictPrimeCurve n hproj m).intersectionScheme
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)) ∧
    Nonempty ((graphStrictPrimeCurve n hproj m).intersectionScheme
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)) :=
  ⟨graphStrict_intersectionScheme_subsingleton n hproj m c hc,
    ⟨(exists_graphStrict_intersection_crossing n hproj m c).choose⟩⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_vertical_intersection_count_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) (hc : c ≠ 0) : True := by
  have _ := f29_graph_vertical_intersection_count.{u} k n hproj m c hc
  trivial

end KltDP.Examples
