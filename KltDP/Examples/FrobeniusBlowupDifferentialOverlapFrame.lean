import KltDP.Examples.FrobeniusBlowupDifferentialOverlap
import KltDP.Geometry.TopExteriorBaseChange
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Actual top differential frames on the Rees-chart intersection

The original chart differential modules have bases from their actual
standard-smooth presentations. The canonical top-exterior scalar-extension
map is therefore invertible. Applying the pinned exterior-power functor to
the original differential localization isomorphisms proves that the
previously defined left and right top maps are themselves isomorphisms.

The original first-chart coordinate frame then gives an actual frame of
the native overlap top differential module. The original second-chart
wedge has coordinate minus the reciprocal ratio, and the original base
two-form has coordinate U. The induced tilde isomorphisms use the same
linear maps and the original structure-sheaf unit.

All algebra structures below reuse the named original maps. No frame,
comparison isomorphism, or canonical-divisor formula is assumed. Global
differential-sheaf descent and a global canonical divisor remain separate
obligations. Only existing pinned functors and proved project maps are
applied; no additional proof port or literature axiom is introduced here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialOverlapFrame

open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferentialMap
open FrobeniusBlowupDifferentialOverlap FrobeniusReesChartDifferentialFrame
open KltDP.Geometry

universe u

variable {k : Type u} [Field k]

local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra
local instance : Algebra k (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra
local instance : Algebra (reesChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra
local instance : Algebra (rightChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra
local instance :
    @IsScalarTower k (reesChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftTower (k := k)
local instance :
    @IsScalarTower k (rightChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapRightTower (k := k)

/-- The actual second-chart polynomial presentation respects its original field map. -/
def rightChartPolynomialAlgEquiv : rightChartRing k ≃ₐ[k] planeRing k where
  __ := vChartPolynomialEquiv
  commutes' := vChartPolynomialEquiv_constants

/-- Standard smoothness for the original second-chart field algebra. -/
theorem rightChart_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 2 k (rightChartRing k) := by
  have hc : (rightChartPolynomialAlgEquiv (k := k)).symm.toRingHom.comp
      planeConstants = chartConstants (centerV (k := k)) := by
    apply RingHom.ext
    intro r
    exact (rightChartPolynomialAlgEquiv (k := k)).symm.commutes r
  have h : RingHom.IsStandardSmoothOfRelativeDimension 2
      ((rightChartPolynomialAlgEquiv (k := k)).symm.toRingHom.comp planeConstants) :=
    (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (rightChartPolynomialAlgEquiv (k := k)).symm.toRingEquiv).comp
        (planeConstants_standardSmooth (k := k))
  rw [hc] at h
  exact h

/-- The actual first-chart differential basis, derived from its proved presentation. -/
def leftDifferentialBasis : Basis (Fin 2) (reesChartRing k) (ChartDifferential k) := by
  letI := chart_standardSmooth (k := k)
  exact AffineTopDifferentialFrame.standardSmoothDifferentialBasis k (reesChartRing k)

/-- The actual second-chart differential basis, with no supplied rank premise. -/
def rightDifferentialBasis : Basis (Fin 2) (rightChartRing k) (RightDifferential k) := by
  letI := rightChart_standardSmooth (k := k)
  exact AffineTopDifferentialFrame.standardSmoothDifferentialBasis k (rightChartRing k)

set_option maxHeartbeats 800000 in
/-- The original first top differential map is invertible. Its forward map
is the previously constructed canonical scalar-extension/localization map. -/
def leftTopEquiv :
    overlapRing k ⊗[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k)) ≃ₗ[overlapRing k]
      ⋀[overlapRing k]^2 (OverlapDifferential k) := by
  let e := TopExteriorBaseChange.equiv (overlapRing k) (leftDifferentialBasis (k := k))
  let f := ((ModuleCat.exteriorPower.functor (overlapRing k) 2).mapIso
    (leftDifferentialEquiv (k := k)).toModuleIso).toLinearEquiv
  apply LinearEquiv.ofBijective (leftTopMap (k := k))
  have h : Function.Bijective (f.toLinearMap.comp e.toLinearMap) :=
    f.bijective.comp e.bijective
  change Function.Bijective
    ((exteriorPower.map 2 (leftDifferentialEquiv (k := k)).toLinearMap).comp
      e.toLinearMap) at h
  have he : e.toLinearMap = KltDP.Compatibility.ExteriorPowerBaseChange.map
      (reesChartRing k) (overlapRing k) 2 (ChartDifferential k) :=
    TopExteriorBaseChange.equiv_toLinearMap (overlapRing k) (leftDifferentialBasis (k := k))
  rw [he] at h
  exact h

theorem leftTopEquiv_toLinearMap :
    (leftTopEquiv (k := k)).toLinearMap = leftTopMap (k := k) := rfl

set_option maxHeartbeats 800000 in
/-- The same conclusion for the original second top differential restriction. -/
def rightTopEquiv :
    overlapRing k ⊗[rightChartRing k] (⋀[rightChartRing k]^2 (RightDifferential k)) ≃ₗ[overlapRing k]
      ⋀[overlapRing k]^2 (OverlapDifferential k) := by
  let e := TopExteriorBaseChange.equiv (overlapRing k) (rightDifferentialBasis (k := k))
  let f := ((ModuleCat.exteriorPower.functor (overlapRing k) 2).mapIso
    (rightDifferentialEquiv (k := k)).toModuleIso).toLinearEquiv
  apply LinearEquiv.ofBijective (rightTopMap (k := k))
  have h : Function.Bijective (f.toLinearMap.comp e.toLinearMap) :=
    f.bijective.comp e.bijective
  change Function.Bijective
    ((exteriorPower.map 2 (rightDifferentialEquiv (k := k)).toLinearMap).comp
      e.toLinearMap) at h
  have he : e.toLinearMap = KltDP.Compatibility.ExteriorPowerBaseChange.map
      (rightChartRing k) (overlapRing k) 2 (RightDifferential k) :=
    TopExteriorBaseChange.equiv_toLinearMap (overlapRing k) (rightDifferentialBasis (k := k))
  rw [he] at h
  exact h

theorem rightTopEquiv_toLinearMap :
    (rightTopEquiv (k := k)).toLinearMap = rightTopMap (k := k) := rfl

/-- Scalar extension of the original first-chart determinant coordinate,
followed by the actual tensor-unit equivalence. -/
def extendedLeftFrameEquiv :
    overlapRing k ⊗[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k)) ≃ₗ[overlapRing k]
      overlapRing k :=
  (LinearEquiv.baseChange (reesChartRing k) (overlapRing k)
    (⋀[reesChartRing k]^2 (ChartDifferential k)) (reesChartRing k)
      (chartTopDifferentialEquiv (k := k))).trans
    (TensorProduct.AlgebraTensorModule.rid (reesChartRing k) (overlapRing k) (overlapRing k))

theorem extendedLeftFrameEquiv_coordinate :
    extendedLeftFrameEquiv (k := k)
      (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k)) = 1 := by
  change (chartTopDifferentialEquiv (k := k)
    (chartCoordinateTopForm (k := k))) • (1 : overlapRing k) = 1
  rw [chartTopDifferentialEquiv_apply, chartTopFormEvaluator_coordinateTopForm, one_smul]

/-- The original native overlap top module has a frame obtained through
the inverse of the original first-chart top restriction. -/
def overlapFrameEquiv :
    (⋀[overlapRing k]^2 (OverlapDifferential k)) ≃ₗ[overlapRing k] overlapRing k :=
  (leftTopEquiv (k := k)).symm.trans (extendedLeftFrameEquiv (k := k))

theorem overlapFrameEquiv_leftTopMap
    (z : overlapRing k ⊗[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k))) :
    overlapFrameEquiv (k := k) (leftTopMap (k := k) z) = extendedLeftFrameEquiv (k := k) z := by
  change extendedLeftFrameEquiv (k := k)
    ((leftTopEquiv (k := k)).symm (leftTopEquiv (k := k) z)) = _
  exact congrArg (extendedLeftFrameEquiv (k := k)) ((leftTopEquiv (k := k)).symm_apply_apply z)

theorem overlapFrameEquiv_leftForm :
    overlapFrameEquiv (k := k) (leftForm (k := k)) = 1 :=
  (congrArg (overlapFrameEquiv (k := k)) (leftTopMap_coordinate (k := k)).symm).trans
    ((overlapFrameEquiv_leftTopMap _).trans extendedLeftFrameEquiv_coordinate)

set_option maxHeartbeats 800000 in
theorem overlapFrameEquiv_symm_apply (a : overlapRing k) :
    (overlapFrameEquiv (k := k)).symm a = a • leftForm (k := k) := by
  apply (overlapFrameEquiv (k := k)).injective
  rw [LinearEquiv.apply_symm_apply,
    (overlapFrameEquiv (k := k)).map_smul a (leftForm (k := k)), overlapFrameEquiv_leftForm,
    smul_eq_mul, mul_one]

/-- Every native overlap top differential is its coordinate times the
original dU wedge dT, without an added generation hypothesis. -/
theorem leftForm_expansion (ω : ⋀[overlapRing k]^2 (OverlapDifferential k)) :
    overlapFrameEquiv (k := k) ω • leftForm (k := k) = ω :=
  (overlapFrameEquiv_symm_apply (overlapFrameEquiv (k := k) ω)).symm.trans
    ((overlapFrameEquiv (k := k)).symm_apply_apply ω)

theorem leftForm_spans :
    Submodule.span (overlapRing k) {leftForm (k := k)} = ⊤ := by
  apply top_unique
  intro ω _
  exact Submodule.mem_span_singleton.mpr
    ⟨overlapFrameEquiv (k := k) ω, leftForm_expansion ω⟩

set_option maxHeartbeats 800000 in
/-- The second native wedge retains its original reciprocal transition coefficient. -/
theorem overlapFrameEquiv_rightForm :
    overlapFrameEquiv (k := k) (rightForm (k := k)) = -overlapS (k := k) := by
  rw [rightForm_eq,
    (overlapFrameEquiv (k := k)).map_smul (-overlapS (k := k)) (leftForm (k := k)),
    overlapFrameEquiv_leftForm, smul_eq_mul, mul_one]

set_option maxHeartbeats 800000 in
/-- The second native wedge also spans: its transition scalar is an actual unit. -/
theorem rightForm_spans :
    Submodule.span (overlapRing k) {rightForm (k := k)} = ⊤ := by
  have hu : IsUnit (-overlapS (k := k)) := by
    exact (show IsUnit (overlapS (k := k)) from
      ((overlapRatioUnit (k := k))⁻¹).isUnit).neg
  rw [rightForm_eq, Submodule.span_singleton_smul_eq hu, leftForm_spans]

set_option maxHeartbeats 800000 in
/-- The actual base form has its original exceptional-coordinate coefficient. -/
theorem overlapFrameEquiv_baseForm :
    overlapFrameEquiv (k := k) (baseForm (k := k)) = overlapU (k := k) := by
  rw [baseForm_left,
    (overlapFrameEquiv (k := k)).map_smul (overlapU (k := k)) (leftForm (k := k)),
    overlapFrameEquiv_leftForm, smul_eq_mul, mul_one]

/-- The first original top restriction induces an actual tilde isomorphism. -/
def leftTopSheafIso :
    (ModuleCat.of (overlapRing k)
      (overlapRing k ⊗[reesChartRing k] (⋀[reesChartRing k]^2 (ChartDifferential k)))).tilde ≅
    (ModuleCat.of (overlapRing k) (⋀[overlapRing k]^2 (OverlapDifferential k))).tilde :=
  AffineModuleTilde.linearEquivIso (leftTopEquiv (k := k))

set_option synthInstance.maxHeartbeats 80000 in
theorem leftTopSheafIso_hom :
    (leftTopSheafIso (k := k)).hom =
      AffineModuleTilde.map (ModuleCat.ofHom (leftTopMap (k := k))) := rfl

/-- The second original top restriction induces the analogous actual tilde isomorphism. -/
def rightTopSheafIso :
    (ModuleCat.of (overlapRing k)
      (overlapRing k ⊗[rightChartRing k] (⋀[rightChartRing k]^2 (RightDifferential k)))).tilde ≅
    (ModuleCat.of (overlapRing k) (⋀[overlapRing k]^2 (OverlapDifferential k))).tilde :=
  AffineModuleTilde.linearEquivIso (rightTopEquiv (k := k))

set_option synthInstance.maxHeartbeats 80000 in
theorem rightTopSheafIso_hom :
    (rightTopSheafIso (k := k)).hom =
      AffineModuleTilde.map (ModuleCat.ofHom (rightTopMap (k := k))) := rfl

/-- The original overlap frame gives a unit isomorphism of actual module sheaves. -/
def overlapFrameSheafIso :
    (ModuleCat.of (overlapRing k) (⋀[overlapRing k]^2 (OverlapDifferential k))).tilde ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of (overlapRing k))).ringCatSheaf :=
  AffineModuleTilde.linearEquivIso
    (M := ModuleCat.of (overlapRing k) (⋀[overlapRing k]^2 (OverlapDifferential k)))
    (N := ModuleCat.of (overlapRing k) (overlapRing k))
    (overlapFrameEquiv (k := k)) ≪≫ AffineModuleTilde.unitIso (overlapRing k)

end KltDP.Examples.FrobeniusBlowupDifferentialOverlapFrame
