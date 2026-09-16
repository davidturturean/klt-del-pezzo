import KltDP.Examples.FrobeniusExceptionalEulerDegrees
import KltDP.Examples.FrobeniusExceptionalChainTransversalLater
import KltDP.Examples.FrobeniusMultiCentreChainTransversal
import KltDP.Examples.FrobeniusStageNoetherianFiniteType
import KltDP.Examples.FrobeniusStageExceptionalTable
import KltDP.Examples.FrobeniusFiberZeroInvertible

/-!
# Euler-degree forms of Lemma 2.2 for the exceptional chains and locus, and the stage-one F29 table,
without the single-point, transversality and fibre hypotheses

BRIEF31, task 1 (review B22, action C-4): one-line compositions, no new mathematics.

* `chain_rationalTreePicard_degrees_unconditional A q`: the accepted
  `FrobeniusExceptionalEulerDegrees.chain_rationalTreePicard_degrees` with `hyp`, `htrans` supplied by the
  accepted `chainSinglePoints` and `chainTransversal`; the remaining assumptions are those of the charted
  plane `A` (`[IsAlgClosed k] [NoetherianSpace A.carrier] [IsLocallyNoetherian A.carrier]
  [IsProper A.structureMap]`), the chain-stage instances coming from the accepted global instances
  `FrobeniusStageNoetherianFiniteType.chainStage_noetherianSpace`/`chainStage_isLocallyNoetherian`.
* `contactTower_chain_rationalTreePicard_degrees_unconditional k q`: the same for the Frobenius contact
  tower over `P¹ × P¹` (`projectiveProductInitial`), with the plane instances discharged by the accepted
  `projectiveProduct_noetherianSpace`, `projectiveProduct_isLocallyNoetherian`,
  `projectiveProductInitial_structure_isProper`; only `[IsAlgClosed k]` remains.
* `towerChain_rationalTreePicard_degrees_unconditional` and `locusEulerMultidegree_bijective_unconditional`
  (`S_{p,n}`): `hyp`, `htrans` supplied by the accepted `singlePoints`, `towerTransversal`; assumptions
  `[IsAlgClosed k]` and `ha : Function.Injective a`.
* `f29_intersection_table_unconditional_stage_one k`: lane A2's accepted `f29_intersection_table_stage_one`
  with `h0` supplied by the accepted `f29_fiber_zero_invertible`; assumption `[IsAlgClosed k]`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusExceptionalEulerDegreesUnconditional

open KltDP.Geometry KltDP.Geometry.RationalTreePicard

/-! ## The exceptional chain of a contact tower -/

section Tower

open KltDP.Geometry.AffineBlowup KltDP.Geometry.PointBlowupGluing
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
  FrobeniusExceptionalCharts FrobeniusExceptionalProjectiveLine FrobeniusExceptionalBaseField
  FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor FrobeniusPreviousStrictBlowdown
  FrobeniusPreviousStrictIsoProjectiveLine FrobeniusExceptionalFinalConfiguration
  FrobeniusExceptionalChainPicard FrobeniusStageNoetherianFiniteType

variable {k : Type u} [Field k]

local instance eulerDegreesUnconditional_originMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- **Lemma 2.2 in Euler-degree form for the exceptional chain of a contact tower**, with the chain
single-point and transversality hypotheses discharged. -/
theorem chain_rationalTreePicard_degrees_unconditional [IsAlgClosed k] (A : PlaneChartedScheme k)
    [NoetherianSpace A.carrier] [IsLocallyNoetherian A.carrier] [IsProper A.structureMap] (q : ℕ) :
    Function.Bijective (eulerMultidegree (chainScheme q A)
      (chainInclusion q A ≫ (A.stage (q + 1)).structureMap)) :=
  FrobeniusExceptionalEulerDegrees.chain_rationalTreePicard_degrees A q
    (FrobeniusExceptionalChainTransversal.chainSinglePoints A q)
    (FrobeniusExceptionalChainTransversalLater.chainTransversal A q)

local instance eulerDegreesUnconditional_contactNoetherianSpace :
    NoetherianSpace (projectiveProductInitial (k := k)).carrier :=
  FrobeniusStageNoetherianFiniteType.projectiveProduct_noetherianSpace

local instance eulerDegreesUnconditional_contactLocallyNoetherian :
    IsLocallyNoetherian (projectiveProductInitial (k := k)).carrier :=
  FrobeniusStageNoetherianFiniteType.projectiveProduct_isLocallyNoetherian

local instance eulerDegreesUnconditional_contactIsProper :
    IsProper (projectiveProductInitial (k := k)).structureMap :=
  FrobeniusStageNoetherianFiniteType.projectiveProductInitial_structure_isProper

variable (k) in
/-- The same for the Frobenius contact tower over `P¹ × P¹`: only `[IsAlgClosed k]` remains. -/
theorem contactTower_chain_rationalTreePicard_degrees_unconditional [IsAlgClosed k] (q : ℕ) :
    Function.Bijective (eulerMultidegree (chainScheme q (projectiveProductInitial (k := k)))
      (chainInclusion q (projectiveProductInitial (k := k)) ≫
        ((projectiveProductInitial (k := k)).stage (q + 1)).structureMap)) :=
  chain_rationalTreePicard_degrees_unconditional (projectiveProductInitial (k := k)) q

end Tower

/-! ## The exceptional chains and the exceptional locus of `S_{p,n}` -/

section MultiCentre

open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusPreviousStrictIsoProjectiveLine FrobeniusGlobalExceptionalSuccessor
  FrobeniusTranslatedCharts FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreChainPicard FrobeniusMultiCentreLocusPicard FrobeniusMultiCentreHalfClass
  FrobeniusContactTowerSelectedPoint

variable {k : Type u} [Field k] [IsAlgClosed k] (q n : ℕ) (a : Fin n → k)
  (ha : Function.Injective a)

/-- **Lemma 2.2 in Euler-degree form for the `i`-th exceptional chain of `S_{p,n}`**, with the
single-point and transversality hypotheses discharged. -/
theorem towerChain_rationalTreePicard_degrees_unconditional (i : Fin n) :
    Function.Bijective (eulerMultidegree (towerChain q n a ha i)
      (towerChainInclusion q n a ha i ≫ multiStructure (q + 1) n a)) :=
  FrobeniusExceptionalEulerDegrees.towerChain_rationalTreePicard_degrees q n a ha
    (FrobeniusMultiCentreChainTransversal.singlePoints q n a ha)
    (FrobeniusMultiCentreChainTransversal.towerTransversal q n a ha) i

/-- **The Euler multidegrees of the whole exceptional locus of `S_{p,n}` form a bijection**, with the
single-point and transversality hypotheses discharged. -/
theorem locusEulerMultidegree_bijective_unconditional :
    Function.Bijective (FrobeniusExceptionalEulerDegrees.locusEulerMultidegree q n a ha) :=
  FrobeniusExceptionalEulerDegrees.locusEulerMultidegree_bijective q n a ha
    (FrobeniusMultiCentreChainTransversal.singlePoints q n a ha)
    (FrobeniusMultiCentreChainTransversal.towerTransversal q n a ha)

end MultiCentre

end KltDP.Examples.FrobeniusExceptionalEulerDegreesUnconditional

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageExceptionalPairing
open FrobeniusStrictTransformPicardStep FrobeniusStrictTransformClassesTower
open FrobeniusGraphPicardClassTotalTransform FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard
open FrobeniusStageOneProjective FrobeniusStageExceptionalTable

/-- **The stage-one F29 table without the fibre hypothesis**: `f29_intersection_table_stage_one` with
`h0 := f29_fiber_zero_invertible k`. -/
theorem f29_intersection_table_unconditional_stage_one (k : Type u) [Field k] [IsAlgClosed k] :
    stageOnePairing (k := k) (stepExceptionalPicardClass 0) = -1 ∧
      stageOnePairing (k := k) (firstFiberTotalClass 1) = 0 ∧
      stageOnePairing (k := k) (secondFiberTotalClass 1) = 0 ∧
      (∀ m : ℕ, stageOnePairing (k := k) (strictCurvePicardClass 1 m) = 1) ∧
      stageOnePairing (k := k) (fiberPicardClass (f29_fiber_zero_invertible k) 1) = 1 :=
  f29_intersection_table_stage_one k (f29_fiber_zero_invertible k)

/-- The bundle has exactly one universe parameter. -/
theorem f29_intersection_table_unconditional_stage_one_universe_check (k : Type u) [Field k]
    [IsAlgClosed k] : True := by
  have _ := f29_intersection_table_unconditional_stage_one.{u} k
  trivial

end KltDP.Examples
