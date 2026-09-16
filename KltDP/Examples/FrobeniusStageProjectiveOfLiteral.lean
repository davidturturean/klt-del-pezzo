import KltDP.Geometry.SmoothFieldRegularPoints
import KltDP.Literature.ResolutionDebtLiterals
import KltDP.Examples.FrobeniusGlobalBlowupSmooth
import KltDP.Examples.FrobeniusStageDimension
import KltDP.Examples.FrobeniusStageNormal
import KltDP.Examples.FrobeniusStageNoetherianFiniteType
import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusGraphPicardClassIntegral

/-!
# Every stage of the origin contact tower is projective, given Stacks 0C5P (BRIEF20, item 1)

For an algebraically closed field `k`, every stage `(projectiveProductInitial).stage n` of the origin
contact tower satisfies the hypotheses of lane E's `RegularProperProjectiveLiteral k`
(Stacks 0C5P over `Spec k`).
* Its structure morphism is proper (accepted `projectiveContactStage_structure_isProper`).
* Every point is regular (`stage_regularPoint`). The structure morphism is smooth (accepted
  `projectiveContactStage_structure_smooth`, of relative dimension two), the stage is normal
  (`projectiveContactStage_isNormalScheme`), integral (accepted `stage_isIntegral` over the integral
  `projectiveProduct`), locally Noetherian (`projectiveContactStage_isLocallyNoetherian`) and of
  dimension two (`projectiveContactStage_topologicalKrullDim`). The generic adapter
  `regularPoint_of_isSmooth_of_isNormalScheme` then applies, generic points included.
* It has dimension two.

Hence **`stage_isProjective_of_literal (h : RegularProperProjectiveLiteral k) n : IsProjectiveOverField
(stage n).structureMap`**, exported as `KltDP.Examples.f29_stage_projective_of_literal`. The only
hypothesis is the literal. Stage `1` is projective unconditionally (BRIEF11, `stage_one_projective`);
the general stage is not proved here without the literal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageProjectiveOfLiteral

open KltDP.Geometry KltDP.Geometry.SmoothFieldRegularPoints KltDP.Literature.Stacks
open FrobeniusGlobalBlowupStages FrobeniusStageDimension FrobeniusStageNormal
  FrobeniusStageNoetherianFiniteType

section Integrality

variable {k : Type u} [Field k]

/-- Every stage of the origin contact tower is an integral scheme (accepted `stage_isIntegral`, over
the integral `projectiveProduct`); no algebraic closedness is used. -/
theorem stage_isIntegral' (n : ℕ) : IsIntegral (projectiveContactStage (k := k) n) :=
  haveI : IsIntegral (projectiveProductInitial (k := k)).carrier :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  FrobeniusTowerFunctionField.PlaneChartedScheme.stage_isIntegral
    (projectiveProductInitial (k := k)) n

end Integrality

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Every point of every stage of the origin contact tower is regular** (no projectivity used). -/
theorem stage_regularPoint (n : ℕ) (x : projectiveContactStage (k := k) n) :
    RegularPoint (projectiveContactStage (k := k) n) x := by
  haveI := projectiveContactStage_isLocallyNoetherian (k := k) n
  haveI : IsIntegral (projectiveContactStage (k := k) n) := stage_isIntegral' n
  exact regularPoint_of_isSmooth_of_isNormalScheme
    ((projectiveProductInitial (k := k)).stage n).structureMap
    (projectiveContactStage_isNormalScheme (k := k) n)
    (fun y => isNoetherianRing_stalk_of_isLocallyNoetherian _ y)
    (projectiveContactStage_topologicalKrullDim (k := k) n).le x

/-- **Every stage of the origin contact tower is projective over `k`**, given Stacks 0C5P. -/
theorem stage_isProjective_of_literal (h : RegularProperProjectiveLiteral k) (n : ℕ) :
    IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap :=
  h.projective (projectiveContactStage (k := k) n)
    ((projectiveProductInitial (k := k)).stage n).structureMap inferInstance
    (stage_regularPoint n) (projectiveContactStage_topologicalKrullDim (k := k) n)

end KltDP.Examples.FrobeniusStageProjectiveOfLiteral

namespace KltDP.Examples

open KltDP.Geometry KltDP.Literature.Stacks FrobeniusGlobalBlowupStages
  FrobeniusStageProjectiveOfLiteral

/-- **F29, stage projectivity from Stacks 0C5P**: every point of every stage is regular, and every
stage is projective over `k` given `RegularProperProjectiveLiteral k`. -/
theorem f29_stage_projective_of_literal (k : Type u) [Field k] [IsAlgClosed k]
    (h : RegularProperProjectiveLiteral k) :
    (∀ (n : ℕ) (x : projectiveContactStage (k := k) n),
      RegularPoint (projectiveContactStage (k := k) n) x) ∧
    ∀ n : ℕ, IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap :=
  ⟨fun n x => stage_regularPoint n x, fun n => stage_isProjective_of_literal h n⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_stage_projective_of_literal_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (h : RegularProperProjectiveLiteral k) : True := by
  have _ := f29_stage_projective_of_literal.{u} k h
  trivial

end KltDP.Examples
