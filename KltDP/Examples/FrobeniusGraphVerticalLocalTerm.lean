import KltDP.Examples.FrobeniusVerticalCrossingContact
import KltDP.Examples.FrobeniusStrictCurveLift
import KltDP.Examples.FrobeniusGraphStrictNotInSupport
import KltDP.Geometry.PrimeCurveLocalLength
import KltDP.Geometry.PrimeCurveStalkCoordinates
import KltDP.Geometry.DivisorOrder

/-!
# The prime-curve layer: the local term of the intersection degree of `B` with `x = c` (BRIEF53)

The sum formula `graphStrict_intersectionDegree_eq_sum` expresses
`intersectionDegree = Σ_{z ∈ B ∩ D} (cartierOrderAt B (D|_B) (i z)).toNat`. This module computes the
**local term**: the Cartier order of the restricted vertical divisor at the crossing point is `1`.

## What this module gives, and what it does NOT

**Gives**: `cartierOrderAt B (D|_B) y = 1` at `y`, the crossing point transported to the prime-curve
scheme, for `D = stageVerticalDivisor (n+1) c` — the divisor `B`'s germ was computed against in
BRIEF52 — with `NotInSupport` discharged from geometry (`graphStrict_notInSupport`, not assumed).

**Does NOT give the row `B · a = 1`.** Two things are still missing, and neither is a corollary:

1. **The count.** The sum formula runs over `B ∩ D`, and nothing yet shows that set is a *singleton*.
   `graphStrictPrimeCurve_inter_vertical_subsingleton` bounds `B ∩ (x = c)` by one point, but its
   second factor is `Set.range (verticalLift c hc (n+1)).base`, whereas the sum runs over
   `B ∩ Supp D`. Bridging them needs `Supp (verticalFiberDivisorAt c) = ` the fibre downstairs,
   which **no module states**: lane A2's `support_pullbackDivisor_eq_preimage` reduces the stage
   support to the product support, but the product support of the vertical fibre divisor itself is
   unidentified. Nonemptiness of `B ∩ D` is likewise unproved. That is the next module.
2. **The class.** Even with the degree, the table's `a` is `firstFiberTotalClass`, a *Picard class*,
   while `stageVerticalDivisor` is a *Cartier divisor*. Identifying them needs
   `cartierPicardHom (pullbackDivisor π D) = schemePicardPullbackHom π (cartierPicardHom D)`, which
   the accepted `CartierDivisorPullbackBlowdown` explicitly records as **not proved**, and which
   `LANE_RULES` lists among the recurring gaps. `FrobeniusStrictTransformSmoothCurves` already flagged
   this: "no accepted statement exhibits a Cartier divisor on the stage with those classes".

So the honest reading is: this is the local half of the layer. `B · a`, `B · b` and `F̃ · a` are all
still open, and `B · b` and `F̃ · a` are untouched.

## The route

`restrictedCoefficient` is by definition `C.inclusion.app`, so its germ is `C.inclusion.stalkMap` of
the stage germ (`Scheme.stalkMap_germ_apply`). Leg 1's `graphStrictLift_inclusion` says
`lift ≫ C.inclusion = strictTransformι`; composing the two stalk maps and consuming that morphism
identity with BRIEF52's generic `stalkMap_germ_congr` — which takes both morphisms as **variables** and
`subst`s the identification, so no point index ever moves — turns the curve-side germ into exactly the
germ BRIEF52's `crossing_vertical_contact_length` measured. `lift` is an isomorphism, so its stalk map
is a ring isomorphism and `quotient_span_length_eq_of_ringEquiv` carries the length across unchanged.

* **`stalkMap_germ_restrictedCoefficient`** — the curve-side germ is the strict-transform germ;
* **`length_quotient_restrictedCoefficient_eq_one`** — its quotient has length `1` (no DVR needed);
* `localLength_restrictedCoefficient_eq_one`, **`cartierOrderAt_stageVerticalDivisor_eq_one`** — the
  same as a local length and as a Cartier order, under the DVR instance at that point.

The DVR instance is a hypothesis rather than a conclusion: `graphStrict_stalk_isDiscreteValuationRing`
supplies it at *closed* points, and the crossing point's closedness is not proved here — but at the
point the sum formula is applied it comes free from `intersectionInclusion_base_isClosed`, so the
hypothesis is discharged exactly where it is consumed.

`c ≠ 0` throughout, entering as it has since Leg 3b through stage-puncture membership.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphVerticalLocalTerm

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphStalkContact
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusStageVerticalDivisor
open FrobeniusVerticalGermTransport FrobeniusVerticalContactStalk
open FrobeniusVerticalCrossingContact
open FrobeniusStrictCurveLift FrobeniusGraphStrictNotInSupport

variable {k : Type u} [Field k]

-- The integrality instances `RegularCartierEquationChart X D` needs to elaborate the *type* of
-- `stageVerticalChartZero`. `FrobeniusStageVerticalDivisor` supplies them only as `local instance`s,
-- which reach neither an importing module nor a later namespace block.
local instance localTermProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance localTermInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance localTermStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

-- `IsDiscreteValuationRing R` carries `[IsDomain R]`, so the DVR binders below do not elaborate at
-- all without this: an instance the TYPE needs is not optional. Stated for an arbitrary prime curve,
-- as the accepted `PrimeCurveLocalLength` and `PrimeCurveTransversalPoint` each do.
local instance localTermStalkIsDomain {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    (y : C.toScheme) : IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
  (m : ℕ)

/-- The crossing point of `B` with `x = c` lies in the chart open of the vertical divisor, read on the
prime-curve scheme. Point-level throughout, so no cast arises. -/
theorem lift_crossingPoint_mem (c : k) :
    (graphStrictLift n hproj m).base (crossingPoint (n + 1) m c) ∈
      (graphStrictPrimeCurve n hproj m).chartPreimage (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalChartZero (k := k) (n + 1) c 0) := by
  show (graphStrictPrimeCurve n hproj m).inclusion.base
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)) ∈
    (stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet
  rw [graphStrictLift_base n hproj m (crossingPoint (n + 1) m c)]
  exact stageCrossingPoint_mem_translatedOpen n m c

/-- The vertical chart is a **generic** chart for `B`: it contains a point of `B`, hence `B`'s generic
point (`genericPoint_mem_of_mem`). This is what `cartierOrderAt_restrictCartier_eq_localLength` asks
for. -/
def verticalGenericChart (c : k) :
    (graphStrictPrimeCurve n hproj m).GenericChart (stageVerticalDivisor (k := k) (n + 1) c) :=
  ⟨stageVerticalChartZero (k := k) (n + 1) c 0,
    genericPoint_mem_of_mem (graphStrictPrimeCurve n hproj m)
      (⟨(graphStrictPrimeCurve n hproj m).inclusion.base
          ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)),
        lift_crossingPoint_mem n hproj m c⟩ :
        (stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
      ((graphStrictPrimeCurve n hproj m).inclusion_base_mem _)⟩

/-- **The curve-side germ of the restricted coefficient is the strict-transform germ of BRIEF52.**
`restrictedCoefficient` is `C.inclusion.app` by definition, and Leg 1's `graphStrictLift_inclusion` is
consumed by `stalkMap_germ_congr`, which `subst`s it at morphism variables so that no point index
moves. -/
theorem stalkMap_germ_restrictedCoefficient (c : k) :
    (graphStrictLift n hproj m).stalkMap (crossingPoint (n + 1) m c)
        ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.germ
          ((graphStrictPrimeCurve n hproj m).chartPreimage
            (stageVerticalDivisor (k := k) (n + 1) c)
            (stageVerticalChartZero (k := k) (n + 1) c 0))
          ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
          (lift_crossingPoint_mem n hproj m c)
          ((graphStrictPrimeCurve n hproj m).restrictedCoefficient
            (stageVerticalDivisor (k := k) (n + 1) c)
            (stageVerticalChartZero (k := k) (n + 1) c 0))) =
      (strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap (crossingPoint (n + 1) m c)
        ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
          ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
          (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
          ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient)) := by
  refine Eq.trans (congrArg
    (fun z => (graphStrictLift n hproj m).stalkMap (crossingPoint (n + 1) m c) z)
    (Scheme.stalkMap_germ_apply ((graphStrictPrimeCurve n hproj m).inclusion)
      ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
      (lift_crossingPoint_mem n hproj m c)
      ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient)).symm) ?_
  refine Eq.trans (stalkMap_stalkMap _ _ _ _) ?_
  exact stalkMap_germ_congr _ _ (graphStrictLift_inclusion n hproj m) _ _ _ _ _

/-- **The local term: the quotient by the restricted coefficient's germ has length one.** The stalk
map of the isomorphism `lift` carries it to BRIEF52's germ, whose length is `1`. No discrete
valuation ring is needed for this statement. -/
theorem length_quotient_restrictedCoefficient_eq_one (c : k) (hc : c ≠ 0) :
    Module.length
        ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
          ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)))
        ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
            ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)) ⧸
          Ideal.span
            {(graphStrictPrimeCurve n hproj m).toScheme.presheaf.germ
              ((graphStrictPrimeCurve n hproj m).chartPreimage
                (stageVerticalDivisor (k := k) (n + 1) c)
                (stageVerticalChartZero (k := k) (n + 1) c 0))
              ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
              (lift_crossingPoint_mem n hproj m c)
              ((graphStrictPrimeCurve n hproj m).restrictedCoefficient
                (stageVerticalDivisor (k := k) (n + 1) c)
                (stageVerticalChartZero (k := k) (n + 1) c 0))}) = 1 := by
  haveI : IsIso ((graphStrictLift n hproj m).stalkMap (crossingPoint (n + 1) m c)) :=
    isIso_stalkMap_of_isIso _ _
  have he := quotient_span_length_eq_of_ringEquiv
    (asIso ((graphStrictLift n hproj m).stalkMap
      (crossingPoint (n + 1) m c))).commRingCatIsoToRingEquiv
    ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.germ
      ((graphStrictPrimeCurve n hproj m).chartPreimage
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalChartZero (k := k) (n + 1) c 0))
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
      (lift_crossingPoint_mem n hproj m c)
      ((graphStrictPrimeCurve n hproj m).restrictedCoefficient
        (stageVerticalDivisor (k := k) (n + 1) c)
        (stageVerticalChartZero (k := k) (n + 1) c 0)))
  have hf : (asIso ((graphStrictLift n hproj m).stalkMap
        (crossingPoint (n + 1) m c))).commRingCatIsoToRingEquiv
      ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.germ
        ((graphStrictPrimeCurve n hproj m).chartPreimage
          (stageVerticalDivisor (k := k) (n + 1) c)
          (stageVerticalChartZero (k := k) (n + 1) c 0))
        ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
        (lift_crossingPoint_mem n hproj m c)
        ((graphStrictPrimeCurve n hproj m).restrictedCoefficient
          (stageVerticalDivisor (k := k) (n + 1) c)
          (stageVerticalChartZero (k := k) (n + 1) c 0))) =
      (strictTransformι (k := k) (n + 1) (m + (n + 1))).stalkMap (crossingPoint (n + 1) m c)
        ((projectiveContactStage (k := k) (n + 1)).presheaf.germ
          ((stageVerticalChartZero (k := k) (n + 1) c 0).chart.openSet)
          (stageCrossingPoint n m c) (stageCrossingPoint_mem_translatedOpen n m c)
          ((stageVerticalChartZero (k := k) (n + 1) c 0).coefficient)) :=
    stalkMap_germ_restrictedCoefficient n hproj m c
  rw [he, hf]
  exact crossing_vertical_contact_length n m c hc

variable (c : k)

/-- The same as a local length, under the discrete-valuation-ring instance at that point. -/
theorem localLength_restrictedCoefficient_eq_one (hc : c ≠ 0)
    [IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)))] :
    (graphStrictPrimeCurve n hproj m).localLength
        ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
        ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.germ
          ((graphStrictPrimeCurve n hproj m).chartPreimage
            (stageVerticalDivisor (k := k) (n + 1) c)
            (stageVerticalChartZero (k := k) (n + 1) c 0))
          ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
          (lift_crossingPoint_mem n hproj m c)
          ((graphStrictPrimeCurve n hproj m).restrictedCoefficient
            (stageVerticalDivisor (k := k) (n + 1) c)
            (stageVerticalChartZero (k := k) (n + 1) c 0))) = 1 := by
  unfold KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.localLength
  rw [length_quotient_restrictedCoefficient_eq_one n hproj m c hc]
  rfl

/-- **The Cartier order of the restricted vertical divisor at the crossing point is one.** This is the
local term the sum formula `graphStrict_intersectionDegree_eq_sum` adds up; `NotInSupport` is the one
derived from geometry, not assumed. -/
theorem cartierOrderAt_stageVerticalDivisor_eq_one (hc : c ≠ 0)
    [IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)))] :
    cartierOrderAt (graphStrictPrimeCurve n hproj m).toScheme
        ((graphStrictPrimeCurve n hproj m).restrictCartier
          (stageVerticalDivisor (k := k) (n + 1) c)
          (stageVerticalDivisor_hasRegularEquations (n + 1) c)
          (graphStrict_notInSupport n hproj m c))
        ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)) = 1 := by
  rw [(graphStrictPrimeCurve n hproj m).cartierOrderAt_restrictCartier_eq_localLength
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c))
      (stageVerticalDivisor (k := k) (n + 1) c)
      (stageVerticalDivisor_hasRegularEquations (n + 1) c)
      (graphStrict_notInSupport n hproj m c)
      (verticalGenericChart n hproj m c) (lift_crossingPoint_mem n hproj m c)]
  -- `(verticalGenericChart …).1` is `stageVerticalChartZero …` by definition but not syntactically,
  -- and that chart argument also sits inside the germ's membership proof, so a `rw` here would be a
  -- dependent rewrite. `congrArg`/`Eq.trans` absorb the definitional difference instead.
  refine Eq.trans (congrArg (fun t : ℕ => (t : ℤ))
    (localLength_restrictedCoefficient_eq_one n hproj m c hc)) ?_
  exact Nat.cast_one

end KltDP.Examples.FrobeniusGraphVerticalLocalTerm

namespace KltDP.Examples

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusStageVerticalDivisor FrobeniusVerticalContactStalk
open FrobeniusStrictCurveLift FrobeniusGraphStrictNotInSupport
open FrobeniusGraphVerticalLocalTerm

local instance localTermProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance localTermInitialIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance localTermStageIntegralTop {k : Type u} [Field k] (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

-- Re-declared: a `local instance` dies at the `end` of its namespace block.
local instance localTermStalkIsDomainTop {k : Type u} [Field k]
    {X : NormalProjectiveSurface k} (C : X.PrimeCurve) (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

/-- **F29: the local term of `B · (x = c)` is one.** The Cartier order of the restricted vertical
divisor at the crossing point of `B` with the fibre `x = c` is `1`, against the divisor `B`'s germ was
actually computed for, with `NotInSupport` derived from geometry. This is the local half of the
prime-curve layer; the row `B · a = 1` needs in addition that `B ∩ (x = c)` is a single point and that
the divisor's Picard class is the table's `a`, neither of which is proved. -/
theorem f29_graph_vertical_local_term (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) (hc : c ≠ 0)
    [IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)))] :
    cartierOrderAt (graphStrictPrimeCurve n hproj m).toScheme
        ((graphStrictPrimeCurve n hproj m).restrictCartier
          (stageVerticalDivisor (k := k) (n + 1) c)
          (stageVerticalDivisor_hasRegularEquations (n + 1) c)
          (graphStrict_notInSupport n hproj m c))
        ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)) = 1 :=
  cartierOrderAt_stageVerticalDivisor_eq_one n hproj m c hc

/-- The statement has exactly one universe parameter. -/
theorem f29_graph_vertical_local_term_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) (c : k) (hc : c ≠ 0)
    [IsDiscreteValuationRing ((graphStrictPrimeCurve n hproj m).toScheme.presheaf.stalk
      ((graphStrictLift n hproj m).base (crossingPoint (n + 1) m c)))] : True := by
  have _ := f29_graph_vertical_local_term.{u} k n hproj m c hc
  trivial

end KltDP.Examples
