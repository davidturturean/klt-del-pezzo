import KltDP.Examples.FrobeniusBlowupDifferentialRightMap

/-!
# Actual two-chart compatibility of the original determinant maps

Extend the actual second-chart differential along the original homogeneous
overlap map. The canonical tensor cancellation comparison gives the same
source as the original plane-to-overlap differential. Their coordinate values
agree, and the existing original plane frame proves equality on the entire
module. Consequently the original native transition carries the entire first
chart differential to the entire second chart differential.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialRightOverlap

open FrobeniusBlowupContact FrobeniusBlowupDifferential FrobeniusBlowupDifferentialMap
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialOverlapFrame
open FrobeniusBlowupDifferentialRestriction FrobeniusBlowupDifferentialRightMap
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (rightChartRing k) :=
  FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra
local instance : Algebra (planeRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra
local instance : Algebra k (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra
local instance : Algebra (rightChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra
local instance :
    @IsScalarTower k (planeRing k) (rightChartRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialRightMap.rightScalarTower (k := k)
local instance :
    @IsScalarTower k (planeRing k) (overlapRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneTower (k := k)
local instance :
    @IsScalarTower k (rightChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapRightTower (k := k)
local instance :
    @IsScalarTower (planeRing k) (rightChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq (planeRing k) (rightChartRing k) (overlapRing k)
    _ _ _ (FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)) fun r =>
      (conormalOverlapRight_baseMap (centerIdeal (k := k)) centerU centerV r).symm

/-- Scalar extension of the actual second-chart differential along the
original right overlap map, with the canonical source cancellation. -/
def planeRightOverlapMap : baseModule k →ₗ[overlapRing k] rightModule k :=
  ((planeRightTopMap (k := k)).baseChange (overlapRing k)).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      (planeRing k) (rightChartRing k) (overlapRing k) (overlapRing k)
      (⋀[planeRing k]^2 (PlaneDifferential k))).symm.toLinearMap

theorem planeRightOverlapMap_tmul (r : overlapRing k)
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    planeRightOverlapMap (k := k) (r ⊗ₜ[planeRing k] ω) =
      r ⊗ₜ[rightChartRing k] planeRightTopMap (k := k) (1 ⊗ₜ[planeRing k] ω) :=
  (congrArg ((planeRightTopMap (k := k)).baseChange (overlapRing k))
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
      (planeRing k) (rightChartRing k) (overlapRing k) r ω)).trans
    (LinearMap.baseChange_tmul (planeRightTopMap (k := k)) r (1 ⊗ₜ[planeRing k] ω))

/-- The original negative exceptional equation is restricted along the
actual overlap ring map, keeping the existing native right wedge. -/
theorem planeRightOverlapMap_coordinate :
    planeRightOverlapMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      (-overlapV (k := k)) • (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) := by
  letI : SMul (rightChartRing k) (overlapRing k) :=
    (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k)).toSMul
  have hv : (-rightV (k := k)) • (1 : overlapRing k) = -overlapV (k := k) := by
    change overlapRight (-rightV (k := k)) * 1 = -overlapV (k := k)
    rw [map_neg, mul_one]
    exact congrArg Neg.neg
      (conormalOverlapRight_baseMap (centerIdeal (k := k)) centerU centerV vCoord)
  calc
    _ = (1 : overlapRing k) ⊗ₜ[rightChartRing k]
        planeRightTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
      planeRightOverlapMap_tmul (k := k) 1 (coordinateTopForm (k := k))
    _ = (1 : overlapRing k) ⊗ₜ[rightChartRing k]
        ((-rightV (k := k)) • rightChartForm (k := k)) :=
      congrArg (fun z : ⋀[rightChartRing k]^2 (RightDifferential k) =>
        (1 : overlapRing k) ⊗ₜ[rightChartRing k] z) (planeRightTopMap_coordinate (k := k))
    _ = ((-rightV (k := k)) • (1 : overlapRing k)) ⊗ₜ[rightChartRing k]
        rightChartForm (k := k) :=
      (TensorProduct.smul_tmul (R := rightChartRing k) (R' := rightChartRing k)
        (M := overlapRing k) (N := ⋀[rightChartRing k]^2 (RightDifferential k))
        (-rightV (k := k)) 1 (rightChartForm (k := k))).symm
    _ = (-overlapV (k := k)) ⊗ₜ[rightChartRing k] rightChartForm (k := k) :=
      congrArg (fun r : overlapRing k => r ⊗ₜ[rightChartRing k] rightChartForm (k := k)) hv
    _ = (-overlapV (k := k)) •
        (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k)) :=
      (congrArg (fun r : overlapRing k => r ⊗ₜ[rightChartRing k] rightChartForm (k := k))
        (mul_one (-overlapV (k := k))).symm).trans
        (TensorProduct.smul_tmul' (R := rightChartRing k) (R' := overlapRing k)
          (M := overlapRing k) (N := ⋀[rightChartRing k]^2 (RightDifferential k))
          (-overlapV (k := k)) (1 : overlapRing k) (rightChartForm (k := k))).symm

/-- The entire original plane-to-right-chart-to-overlap square commutes. -/
theorem rightTopMap_comp_planeRightOverlapMap :
    (rightTopMap (k := k)).comp (planeRightOverlapMap (k := k)) = baseTopMap (k := k) := by
  let f : baseModule k →ₗ[overlapRing k]
      FrobeniusBlowupDifferentialOverlapSheaf.targetModule k :=
    (rightTopMap (k := k)).comp (planeRightOverlapMap (k := k))
  have hc : f (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
    (congrArg (rightTopMap (k := k)) (planeRightOverlapMap_coordinate (k := k))).trans
      (((rightTopMap (k := k)).map_smul (-overlapV (k := k))
        (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k))).trans
        (baseTopMap_coordinate_right (k := k)).symm)
  change f = baseTopMap (k := k)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r ω =>
      let c : overlapRing k :=
        r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)
      have hz := FrobeniusBlowupDifferentialOverlapSheaf.tensor_coordinate (k := k) r ω
      calc
        f (r ⊗ₜ[planeRing k] ω) =
            f (c • (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) := congrArg f hz
        _ = c • f (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) := f.map_smul c _
        _ = c • baseTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
          congrArg (fun w : FrobeniusBlowupDifferentialOverlapSheaf.targetModule k => c • w) hc
        _ = baseTopMap (k := k) (c • (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) :=
          ((baseTopMap (k := k)).map_smul c _).symm
        _ = baseTopMap (k := k) (r ⊗ₜ[planeRing k] ω) :=
          congrArg (baseTopMap (k := k)) hz.symm
  | add x y hx hy =>
      exact (f.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans ((baseTopMap (k := k)).map_add x y).symm)

/-- The existing native transition carries the entire actual first-chart
differential to the entire actual second-chart differential. -/
theorem chartTransition_comp_planeChartOverlapMap :
    (chartTransition (k := k)).toLinearMap.comp (planeChartOverlapMap (k := k)) =
      planeRightOverlapMap (k := k) := by
  apply LinearMap.ext
  intro z
  apply (rightTopEquiv (k := k)).injective
  exact (rightTopMap_chartTransition (k := k) (planeChartOverlapMap (k := k) z)).trans
    ((DFunLike.congr_fun (leftTopMap_comp_planeChartOverlapMap (k := k)) z).trans
      (DFunLike.congr_fun (rightTopMap_comp_planeRightOverlapMap (k := k)) z).symm)

end KltDP.Examples.FrobeniusBlowupDifferentialRightOverlap
