import KltDP.Examples.FrobeniusVerticalSupportSubsingleton
import KltDP.Examples.FrobeniusGraphVerticalLocalTerm
import KltDP.Examples.FrobeniusStrictTransformSmoothCurves
import KltDP.Geometry.PrimeCurveIntersectionFinite
import KltDP.Geometry.PrimeCurveIntersectionLocalLengthPoints
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Examples.FrobeniusGraphPicardClassIntegral
import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusVerticalFiberClass
import KltDP.Examples.FrobeniusVerticalFiberTranslated
import KltDP.Examples.FrobeniusVerticalContactStalk
import KltDP.Examples.FrobeniusStrictCurveLift
import KltDP.Examples.FrobeniusGraphStrictNotInSupport
import KltDP.Examples.FrobeniusStageVerticalDivisor
import KltDP.Examples.FrobeniusStrictTransformPrimeCurves
import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusGlobalBlowupStages
import KltDP.Examples.FrobeniusGlobalStrictTransform
import KltDP.Examples.FrobeniusProjectiveMorphism
import KltDP.Examples.FrobeniusProjectivePoints
import KltDP.Geometry.EffectiveCartierIdeal
import KltDP.Geometry.DivisorOrder
import KltDP.Geometry.PrimeCurveCartierRestriction

/-!
# `B · (x = c) = 1` as an intersection NUMBER (the sum formula collapsed)

Everything the sum formula `graphStrict_intersectionDegree_eq_sum` needs is now in place:

* the **count** — `FrobeniusVerticalSupportSubsingleton` makes the intersection scheme a subsingleton
  and exhibits BRIEF52's crossing point in it;
* the **local term** — the queued `cartierOrderAt_stageVerticalDivisor_eq_one` evaluates the Cartier
  order at exactly that point as `1`.

So the sum over `B ∩ Supp(x = c)` has a single summand, and it is `1`.

* **`graphStrict_intersectionDegree_vertical_eq_one`** — the scheme-theoretic intersection degree;
* **`graphStrict_intersectionNumber_vertical_eq_one`** — the same as the intersection *number*
  `B · D` of the accepted `PrimeCurveIntersectionNumber`, via
  `intersectionNumber_eq_intersectionDegree`.

## What this does NOT give — the row `B · a = 1` is still not proved

This is `B · D` for `D = stageVerticalDivisor (n+1) c`, a **Cartier divisor**. The table's `a` is
`firstFiberTotalClass (n+1)`, a **Picard class**, and `graphStrictPairing n hproj m` is
`picardRestrictionDegreeHom`. Bridging them needs

    cartierPicardHom (stage) (stageVerticalDivisor (n+1) c) = firstFiberTotalClass (n+1)

whose pullback half is lane F's accepted `cartierPicardHom_pullbackDivisor_eq` but whose base half —
the Picard class of `verticalFiberDivisorAt c` on `P¹ × P¹` as minus the class of
`verticalFiberIdealLine` — is **not** proved anywhere, and is not proved here. So `B · a = 1` remains
open, and `B · b = p` and `F̃ · a = 1` are untouched.

`c ≠ 0` throughout, as everywhere below the tower stalk transport.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphVerticalDegree

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor
open FrobeniusVerticalContactStalk
open FrobeniusStrictCurveLift FrobeniusGraphStrictNotInSupport
open FrobeniusStrictTransformSmoothCurves
open FrobeniusGraphVerticalLocalTerm
open FrobeniusVerticalSupportSubsingleton

variable {k : Type u} [Field k]

local instance verticalDegreeProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance verticalDegreeInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance verticalDegreeStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

-- `IsDiscreteValuationRing R` carries `[IsDomain R]`, so the DVR binders below do not elaborate at
-- all without this: an instance the TYPE needs is not optional.
local instance verticalDegreeStalkIsDomain {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (y : C.toScheme) : IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **The local term, transported to any point propositionally equal to the crossing point.** The
point sits inside the `[IsDiscreteValuationRing (… stalk y)]` instance argument of `cartierOrderAt`,
so rewriting it in the goal is a DEPENDENT rewrite whose motive does not typecheck (this lane's rule
14). Stating it with the point as a VARIABLE and consuming the identification by `subst` (rule 11)
carries the instance along with the point, so no transport ever forms. -/
theorem cartierOrderAt_eq_one_of_eq (m : ℕ) (c : k) (hc : c ≠ 0)
    (y : (graphStrictPrimeCurve n hproj m).toScheme)
    [IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk y)]
    (hy : y = (graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)) :
    cartierOrderAt (graphStrictPrimeCurve n hproj m).toScheme
      ((graphStrictPrimeCurve n hproj m).restrictCartier
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c)) y = 1 := by
  subst hy
  exact cartierOrderAt_stageVerticalDivisor_eq_one n hproj m c hc

/-- **The intersection degree of `B` with the vertical fibre `x = c` is one.** The sum formula over
`B ∩ Supp D` has one summand, by the subsingleton and the crossing witness, and that summand is the
queued local term. -/
theorem graphStrict_intersectionDegree_vertical_eq_one (m : ℕ) (c : k) (hc : c ≠ 0) :
    (graphStrictPrimeCurve n hproj m).intersectionDegree
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c) = 1 := by
  haveI := graphStrict_isSmooth_toSpec n hproj m
  haveI := graphStrict_intersectionScheme_subsingleton n hproj m c hc
  obtain ⟨z₀, hz₀⟩ := exists_graphStrict_intersection_crossing n hproj m c
  have hclosed : IsClosed ({(graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)} :
      Set (graphStrictPrimeCurve n hproj m).toScheme) := by
    rw [← hz₀]
    exact (graphStrictPrimeCurve n hproj m).intersectionInclusion_base_isClosed
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c) z₀
  haveI : IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))) :=
    graphStrict_stalk_isDiscreteValuationRing n hproj m _ hclosed
  -- The `letI`s are textually those of `graphStrict_intersectionDegree_eq_sum`'s own statement, so
  -- that `Finset.univ` below elaborates against the same `Fintype` instance the rewrite introduces.
  letI : Fintype ((graphStrictPrimeCurve n hproj m).intersectionScheme
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)) :=
    haveI := (graphStrictPrimeCurve n hproj m).intersectionScheme_finite'
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)
    Fintype.ofFinite _
  letI : ∀ z : (graphStrictPrimeCurve n hproj m).intersectionScheme
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c),
      IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
        (((graphStrictPrimeCurve n hproj m).intersectionInclusion
          (stageVerticalDivisor (k := k) (n + 1) c)
          (stageVerticalDivisor_hasRegularEquations (n + 1) c)
          (graphStrict_notInSupport n hproj m c)).base z)) :=
    fun z => graphStrict_stalk_isDiscreteValuationRing n hproj m _
      ((graphStrictPrimeCurve n hproj m).intersectionInclusion_base_isClosed
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalDivisor_hasRegularEquations (n + 1) c)
        (graphStrict_notInSupport n hproj m c) z)
  rw [graphStrict_intersectionDegree_eq_sum n hproj m
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c),
    Finset.sum_eq_single_of_mem z₀ (Finset.mem_univ z₀)
      (fun z _ hz => absurd (Subsingleton.elim z z₀) hz),
    cartierOrderAt_eq_one_of_eq n hproj m c hc _ hz₀]
  all_goals rfl

/-- **`B · (x = c) = 1` as an intersection number.** -/
theorem graphStrict_intersectionNumber_vertical_eq_one (m : ℕ) (c : k) (hc : c ≠ 0) :
    (graphStrictPrimeCurve n hproj m).intersectionNumber
      (stageVerticalDivisor (k := k) (n + 1) c) = 1 := by
  rw [(graphStrictPrimeCurve n hproj m).intersectionNumber_eq_intersectionDegree
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c),
    graphStrict_intersectionDegree_vertical_eq_one n hproj m c hc]
  all_goals rfl

end KltDP.Examples.FrobeniusGraphVerticalDegree

namespace KltDP.Examples

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor FrobeniusGraphStrictNotInSupport
open FrobeniusGraphVerticalDegree

local instance verticalDegreeProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance verticalDegreeInitialIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance verticalDegreeStageIntegralTop {k : Type u} [Field k] (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- **F29: `B · (x = c) = 1`.** The intersection number of the strict transform of the graph with the
vertical ruling fibre `x = c`, `c ≠ 0`, pulled back to the contact stage, is one — count and local
term both derived from geometry, with `NotInSupport` discharged rather than assumed. This is the
divisor form of the row; the Picard-class form `B · a = 1` additionally needs the class of
`verticalFiberDivisorAt c` on `P¹ × P¹`, which is not proved. -/
theorem f29_graph_vertical_intersection_number (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) (hc : c ≠ 0) :
    (graphStrictPrimeCurve n hproj m).intersectionNumber
      (stageVerticalDivisor (k := k) (n + 1) c) = 1 :=
  graphStrict_intersectionNumber_vertical_eq_one n hproj m c hc

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_vertical_intersection_number_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) (hc : c ≠ 0) : True := by
  have _ := f29_graph_vertical_intersection_number.{u} k n hproj m c hc
  trivial

end KltDP.Examples
