import KltDP.Examples.FrobeniusBlowupDifferentialOverlap
import KltDP.Examples.FrobeniusCoordinateDifferentialFrame

/-!
# Actual top-differential sheaf-map compatibility on the Rees overlap

The source module is the scalar extension of the original plane top line.
Its actual coordinate frame proves the coefficient formula for every
element, not only for its named coordinate wedge. The two original chart
descriptions give the same full linear map into the native overlap top
differentials. Applying the original tilde functor gives equal actual
module-sheaf maps, compatible with every restriction of overlap opens.

This is a compatibility theorem for constructed differential maps. No
global differential sheaf, canonical divisor or numerical order is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialOverlapSheaf

open FrobeniusBlowupContact FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialOverlap FrobeniusCoordinateDifferentialFrame
open KltDP.Geometry

universe u

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra

local instance : Algebra k (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra

local instance :
    @IsScalarTower k (planeRing k) (overlapRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneTower (k := k)

/-- The original base top line, extended along the actual overlap structure map. -/
abbrev sourceModule (k : Type u) [Field k] : ModuleCat (overlapRing k) :=
  ModuleCat.of (overlapRing k)
    (overlapRing k ⊗[planeRing k] (⋀[planeRing k]^2 (PlaneDifferential k)))

/-- The original native overlap top-differential module. -/
abbrev targetModule (k : Type u) [Field k] : ModuleCat (overlapRing k) :=
  ModuleCat.of (overlapRing k) (⋀[overlapRing k]^2 (OverlapDifferential k))

/-- Scalar extension of the original plane determinant functional. -/
def baseFrameCoordinate : sourceModule k →ₗ[overlapRing k] overlapRing k :=
  ((Algebra.linearMap (planeRing k) (overlapRing k)).comp
    (coordinateTopDifferentialEquiv (k := k)).toLinearMap).liftBaseChange (overlapRing k)

theorem baseFrameCoordinate_tmul (r : overlapRing k)
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    baseFrameCoordinate (r ⊗ₜ[planeRing k] ω) =
      r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω) := by
  change r * algebraMap (planeRing k) (overlapRing k) (coordinateTopDifferentialEquiv ω) = _
  rw [coordinateTopDifferentialEquiv_apply]

/-- The original plane frame controls every tensor in the source. -/
theorem tensor_coordinate (r : overlapRing k)
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    r ⊗ₜ[planeRing k] ω =
      (r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)) •
        (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) := by
  letI : SMul (planeRing k) (overlapRing k) :=
    (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul
  calc
    r ⊗ₜ[planeRing k] ω =
        r ⊗ₜ[planeRing k] (coordinateTopFormEvaluator ω • coordinateTopForm (k := k)) :=
      congrArg (fun x : ⋀[planeRing k]^2 (PlaneDifferential k) => r ⊗ₜ[planeRing k] x)
        (coordinateTopForm_expansion ω).symm
    _ = (coordinateTopFormEvaluator ω • r) ⊗ₜ[planeRing k] coordinateTopForm (k := k) :=
      (TensorProduct.smul_tmul (R := planeRing k) (R' := planeRing k)
        (M := overlapRing k) (N := ⋀[planeRing k]^2 (PlaneDifferential k))
        (coordinateTopFormEvaluator ω) r (coordinateTopForm (k := k))).symm
    _ = (r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω))
        ⊗ₜ[planeRing k] coordinateTopForm (k := k) :=
      congrArg (fun x : overlapRing k => x ⊗ₜ[planeRing k] coordinateTopForm (k := k))
        ((Algebra.smul_def (coordinateTopFormEvaluator ω) r).trans
          (mul_comm (algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)) r))
    _ = (r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)) •
        (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem baseTopMap_tmul (r : overlapRing k)
    (ω : ⋀[planeRing k]^2 (PlaneDifferential k)) :
    baseTopMap (k := k) (r ⊗ₜ[planeRing k] ω) =
      (r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)) •
        baseForm (k := k) := by
  let c : overlapRing k :=
    r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)
  exact (congrArg (baseTopMap (k := k)) (tensor_coordinate (k := k) r ω)).trans
    (((baseTopMap (k := k)).map_smul c
      (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))).trans
      (congrArg (fun z : targetModule k => c • z) (baseTopMap_coordinate (k := k))))

/-- The first coordinate expression is an actual linear map, with the
original exceptional coefficient multiplying the original overlap wedge. -/
def leftDescription : sourceModule k →ₗ[overlapRing k] targetModule k :=
  (LinearMap.toSpanSingleton (overlapRing k) (targetModule k)
    (overlapU (k := k) • leftForm (k := k))).comp baseFrameCoordinate

/-- The second coordinate expression keeps its actual coordinate order
and its derived minus sign. -/
def rightDescription : sourceModule k →ₗ[overlapRing k] targetModule k :=
  (LinearMap.toSpanSingleton (overlapRing k) (targetModule k)
    ((-overlapV (k := k)) • rightForm (k := k))).comp baseFrameCoordinate

set_option maxHeartbeats 800000 in
theorem baseTopMap_eq_leftDescription :
    baseTopMap (k := k) = leftDescription (k := k) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r ω =>
      change baseTopMap (k := k) (r ⊗ₜ[planeRing k] ω) =
        baseFrameCoordinate (r ⊗ₜ[planeRing k] ω) •
          (overlapU (k := k) • leftForm (k := k))
      let c : overlapRing k :=
        r * algebraMap (planeRing k) (overlapRing k) (coordinateTopFormEvaluator ω)
      exact (baseTopMap_tmul (k := k) r ω).trans
        ((congrArg (fun z : targetModule k => c • z) (baseForm_left (k := k))).trans
          (congrArg (fun a : overlapRing k => a • (overlapU (k := k) • leftForm (k := k)))
            (baseFrameCoordinate_tmul (k := k) r ω).symm))
  | add x y hx hy =>
      exact ((baseTopMap (k := k)).map_add x y).trans
        ((congrArg₂ (fun a b : targetModule k => a + b) hx hy).trans
          ((leftDescription (k := k)).map_add x y).symm)

theorem leftDescription_eq_rightDescription :
    leftDescription (k := k) = rightDescription (k := k) :=
  congrArg (fun w : targetModule k =>
    (LinearMap.toSpanSingleton (overlapRing k) (targetModule k) w).comp
      (baseFrameCoordinate (k := k)))
    ((baseForm_left (k := k)).symm.trans baseForm_right)

theorem baseTopMap_eq_rightDescription :
    baseTopMap (k := k) = rightDescription (k := k) :=
  baseTopMap_eq_leftDescription.trans leftDescription_eq_rightDescription

/-- The original scalar-extended top differential map on actual tilde sheaves. -/
def baseTopSheafMap : (sourceModule k).tilde ⟶ (targetModule k).tilde :=
  AffineModuleTilde.map (ModuleCat.ofHom (baseTopMap (k := k)))

set_option maxHeartbeats 800000 in
theorem baseTopSheafMap_eq_leftDescription :
    baseTopSheafMap (k := k) =
      AffineModuleTilde.map (ModuleCat.ofHom (leftDescription (k := k))) := by
  unfold baseTopSheafMap
  apply congrArg (AffineModuleTilde.map (M := sourceModule k) (N := targetModule k))
  apply ModuleCat.hom_ext
  exact baseTopMap_eq_leftDescription (k := k)

set_option maxHeartbeats 800000 in
theorem baseTopSheafMap_eq_rightDescription :
    baseTopSheafMap (k := k) =
      AffineModuleTilde.map (ModuleCat.ofHom (rightDescription (k := k))) := by
  unfold baseTopSheafMap
  apply congrArg (AffineModuleTilde.map (M := sourceModule k) (N := targetModule k))
  apply ModuleCat.hom_ext
  exact baseTopMap_eq_rightDescription (k := k)

set_option maxHeartbeats 800000 in
/-- Canonical sections follow the original differential map. -/
theorem baseTopSheafMap_toOpen (U : Opens (PrimeSpectrum (overlapRing k)))
    (z : sourceModule k) :
    (baseTopSheafMap (k := k)).val.app (op U)
        (ModuleCat.Tilde.toOpen (sourceModule k) U z) =
      ModuleCat.Tilde.toOpen (targetModule k) U (baseTopMap (k := k) z) :=
  AffineModuleTilde.map_app_toOpen (M := sourceModule k) (N := targetModule k)
    (ModuleCat.ofHom (baseTopMap (k := k))) U z

/-- The same actual base two-form has the first-chart coefficient on
every open of the original overlap. -/
theorem baseTopSheafMap_coordinate_left (U : Opens (PrimeSpectrum (overlapRing k))) :
    (baseTopSheafMap (k := k)).val.app (op U)
        (ModuleCat.Tilde.toOpen (sourceModule k) U
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) =
      ModuleCat.Tilde.toOpen (targetModule k) U
        (overlapU (k := k) • leftForm (k := k)) := by
  exact (baseTopSheafMap_toOpen (k := k) U
    (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))).trans
    (congrArg (fun z : targetModule k => ModuleCat.Tilde.toOpen (targetModule k) U z)
      ((baseTopMap_coordinate (k := k)).trans (baseForm_left (k := k))))

theorem baseTopSheafMap_coordinate_right (U : Opens (PrimeSpectrum (overlapRing k))) :
    (baseTopSheafMap (k := k)).val.app (op U)
        (ModuleCat.Tilde.toOpen (sourceModule k) U
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) =
      ModuleCat.Tilde.toOpen (targetModule k) U
        ((-overlapV (k := k)) • rightForm (k := k)) := by
  exact (baseTopSheafMap_toOpen (k := k) U
    (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))).trans
    (congrArg (fun z : targetModule k => ModuleCat.Tilde.toOpen (targetModule k) U z)
      ((baseTopMap_coordinate (k := k)).trans (baseForm_right (k := k))))

/-- The equality of coordinate descriptions belongs to a genuine sheaf
map, so it commutes with every restriction of actual overlap opens. -/
theorem baseTopSheafMap_restrict {U V : Opens (PrimeSpectrum (overlapRing k))}
    (i : V ⟶ U) (s : (sourceModule k).tilde.val.obj (op U)) :
    (targetModule k).tilde.val.map i.op ((baseTopSheafMap (k := k)).val.app (op U) s) =
      (baseTopSheafMap (k := k)).val.app (op V) ((sourceModule k).tilde.val.map i.op s) :=
  (_root_.PresheafOfModules.naturality_apply (baseTopSheafMap (k := k)).val i.op s).symm

end KltDP.Examples.FrobeniusBlowupDifferentialOverlapSheaf
