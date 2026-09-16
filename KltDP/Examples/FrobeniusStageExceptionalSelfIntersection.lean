import KltDP.Examples.FrobeniusStageExceptionalPullback
import KltDP.Geometry.PrimeCurveIntersectionNumber
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.ClosedImmersionKerDegree
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# `E·E` in lane D's intersection-number API: reduction to the conormal degree, and `E·π^*D = 0`

On the stage-`(n+1)` surface `stageSurface (n+1) hproj` (regular everywhere, `k` algebraically
closed) the exceptional prime curve `E = exceptionalPrimeCurve n hproj` has lane D's self-intersection
number `E.selfIntersectionNumber hreg = E · D_E`, where `D_E = primeCurveCartier E` is the Cartier
divisor with Weil divisor `1·E`. This module proves

* `exceptionalCartier_ker`: the zero scheme of `D_E` and the accepted centre fibre
  `stepExceptionalInclusion n` have the same kernel ideal sheaf (lane D's
  `primeCurveCartier_idealData_eq_vanishingIdeal` and `stepExceptionalInclusion_ker`);
* `negativeCartierKernelIso`: `O_X(-D_E) ≅ I(E)`, the kernel ideal module of the centre fibre
  (accepted `effectiveCartierKernelIso`, lane D's `kernelIsoOfKerEq`);
* `intersectionNumber_neg_exceptionalCartier`: `E · (−D_E) = deg_E (conormal)`, the degree on `E` of
  the accepted conormal line `globalConormalLine` transported along the isomorphism
  `exceptionalLift : (centre fibre) ≅ E.toScheme`;
* **`selfIntersectionNumber_eq_neg_conormal_degree`: `E·E = −deg_E (conormal line of E)`**
  (accepted `intersectionNumber_neg`, admitted 0AYX through lane D's additivity);
* `intersectionNumber_eq_zero_of_pullback`: `E · D = 0` for every Cartier divisor `D` on the stage
  whose line bundle is (isomorphic to) the pullback `π^*L` of a line bundle on stage `n`, and the
  F09 export `f09_exceptional_pullback_degree_zero` (`E · π^*L = 0` for every `L`).

**Not proved: `deg_E (conormal) = 1`, hence `E·E = −1`.** The accepted Euler difference
`f09_exceptional_euler_difference` computes the normal line on `P¹` with the structure morphism
`projectiveSpaceToSpec k 1`; lane D's `lineDegree` is the Euler difference on `E.toScheme` with
`E.toSpec`. Transporting `eulerCharacteristic` along the isomorphism of `k`-schemes
`E.toScheme ≅ centre fibre ≅ P¹` (or Stacks 0AYY on `E.toScheme` for a point divisor with
`O_E(pt) ≅ conormal`) is not available in the accepted tree and is the remaining step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStageExceptionalSelfIntersection

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalNormal
open FrobeniusStrictTransformProductKernel FrobeniusStageSurface
open FrobeniusStageExceptionalPullback

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- Regularity of every point of the stage-`(n+1)` surface. -/
abbrev stageRegular :
    ∀ x : (stageSurface (n + 1) hproj).Point, RegularPoint (stageSurface (n + 1) hproj).toScheme x :=
  stageSurface_regularPoints (n + 1) hproj

/-- The Cartier divisor `D_E` of the exceptional prime curve (lane D's `primeCurveCartier`). -/
abbrev exceptionalCartier : CartierDivisor (stageSurface (n + 1) hproj).toScheme :=
  (stageSurface (n + 1) hproj).primeCurveCartier (stageRegular n hproj) (exceptionalPrimeCurve n hproj)

/-- `D_E` has regular local equations. -/
theorem exceptionalCartier_hasRegularEquations :
    HasRegularCartierEquations (stageSurface (n + 1) hproj).toScheme (exceptionalCartier n hproj) :=
  (stageSurface (n + 1) hproj).primeCurveCartier_hasRegularEquations (stageRegular n hproj)
    (exceptionalPrimeCurve n hproj)

/-- The zero scheme of `D_E` and the exceptional centre fibre have the same kernel ideal sheaf. -/
theorem exceptionalCartier_ker :
    (effectiveCartierIdealDataOfRegularEquations (stageSurface (n + 1) hproj).toScheme
        (exceptionalCartier n hproj) (exceptionalCartier_hasRegularEquations n hproj)).gluedTo.ker =
      (stepExceptionalInclusion (k := k) n).ker := by
  rw [effectiveCartierIdealDataOfRegularEquations_ker,
    (stageSurface (n + 1) hproj).primeCurveCartier_idealData_eq_vanishingIdeal
      (stageRegular n hproj) (exceptionalPrimeCurve n hproj),
    stepExceptionalInclusion_ker n hproj]

/-- `O_X(−D_E) ≅ I(E)`: the negative Cartier module is the kernel ideal module of the centre fibre. -/
def negativeCartierKernelIso :
    cartierDivisorModule (stageSurface (n + 1) hproj).toScheme (-(exceptionalCartier n hproj)) ≅
      schemeKernelIdeal (stepExceptionalInclusion (k := k) n) :=
  effectiveCartierKernelIso (stageSurface (n + 1) hproj).toScheme (exceptionalCartier n hproj)
      (exceptionalCartier_hasRegularEquations n hproj) ≪≫
    kernelIsoOfKerEq _ (stepExceptionalInclusion (k := k) n) (exceptionalCartier_ker n hproj)

/-- The accepted conormal line of the centre fibre, transported to the prime-curve scheme of `E`. -/
abbrev exceptionalConormalLine : InvertibleSheaf (exceptionalPrimeCurve n hproj).toScheme :=
  pullbackInvertibleSheaf (inv (exceptionalLift n hproj))
    (globalConormalLine ((projectiveProductInitial (k := k)).stage n))

/-- `E · (−D_E) = deg_E (conormal line)`. -/
theorem intersectionNumber_neg_exceptionalCartier :
    (exceptionalPrimeCurve n hproj).intersectionNumber (-(exceptionalCartier n hproj)) =
      (exceptionalPrimeCurve n hproj).lineDegree (exceptionalConormalLine n hproj) := by
  unfold PrimeCurve.intersectionNumber
  apply (exceptionalPrimeCurve n hproj).lineDegree_eq_of_iso
  refine (schemeModulePullback (exceptionalPrimeCurve n hproj).inclusion).mapIso
    (negativeCartierKernelIso n hproj) ≪≫ ?_
  rw [inclusion_eq_inv_exceptionalLift]
  exact (schemeModulePullbackCompIso (inv (exceptionalLift n hproj))
    (stepExceptionalInclusion (k := k) n)).symm.app
      (schemeKernelIdeal (stepExceptionalInclusion (k := k) n))

/-- **`E·E = −deg_E (conormal line of E)`** in lane D's `selfIntersectionNumber`. -/
theorem selfIntersectionNumber_eq_neg_conormal_degree :
    (exceptionalPrimeCurve n hproj).selfIntersectionNumber (stageRegular n hproj) =
      -(exceptionalPrimeCurve n hproj).lineDegree (exceptionalConormalLine n hproj) := by
  rw [← intersectionNumber_neg_exceptionalCartier n hproj, PrimeCurve.intersectionNumber_neg,
    neg_neg]
  rfl

/-- **`E · D = 0`** for every Cartier divisor `D` on the stage whose line bundle is a pullback
`π^*L` from stage `n`. -/
theorem intersectionNumber_eq_zero_of_pullback (D : CartierDivisor (stageSurface (n + 1) hproj).toScheme)
    (L : InvertibleSheaf (projectiveContactStage (k := k) n))
    (e : (cartierDivisorInvertibleSheaf (stageSurface (n + 1) hproj).toScheme D).obj ≅
      (pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n) L).obj) :
    (exceptionalPrimeCurve n hproj).intersectionNumber D = 0 := by
  rw [PrimeCurve.intersectionNumber_eq_restrictionDegree,
    (exceptionalPrimeCurve n hproj).restrictionDegree_eq_of_iso e]
  exact restrictionDegree_pullback_stepProjection n hproj L

end KltDP.Examples.FrobeniusStageExceptionalSelfIntersection

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface
  FrobeniusStageExceptionalPullback FrobeniusStageExceptionalSelfIntersection

/-- **F09, pullback clause: `E · π^*L = 0`** for the exceptional prime curve `E` of stage `n+1` and
every invertible sheaf `L` on stage `n`, in lane D's restriction-degree API; together with the
reduction `E·E = −deg_E(conormal)`. Hypotheses: `k` algebraically closed and a closed projective
embedding `hproj` of the stage over `k`. -/
theorem f09_exceptional_pullback_degree_zero (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    (∀ L : InvertibleSheaf (projectiveContactStage (k := k) n),
      (exceptionalPrimeCurve n hproj).restrictionDegree
        (pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n) L) = 0) ∧
    (exceptionalPrimeCurve n hproj).selfIntersectionNumber (stageRegular n hproj) =
      -(exceptionalPrimeCurve n hproj).lineDegree (exceptionalConormalLine n hproj) :=
  ⟨restrictionDegree_pullback_stepProjection n hproj,
    selfIntersectionNumber_eq_neg_conormal_degree n hproj⟩

/-- The bundle has exactly one universe parameter. -/
theorem f09_exceptional_pullback_degree_zero_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap) :
    True := by
  have _ := f09_exceptional_pullback_degree_zero.{u} k n hproj
  trivial

end KltDP.Examples
