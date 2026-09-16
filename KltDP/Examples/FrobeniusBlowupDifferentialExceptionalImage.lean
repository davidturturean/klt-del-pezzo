import KltDP.Examples.FrobeniusBlowupDifferentialPullbackComp
import KltDP.Examples.FrobeniusCoordinateDifferentialFrame
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The actual Rees-chart determinant has the exceptional ideal as its image

The original plane differential frame extends to a frame of the original
scalar-extension module. The previously proved value of the actual exterior
differential on that frame therefore determines the whole map: its coefficient
is multiplication by the original exceptional equation `chartU`.

The image is the original extended center ideal, and regularity of its actual
Rees equation proves injectivity. Thus the determinant gives an equivalence
onto this actual ideal, through which the original top-differential map factors.
No canonical divisor formula or determinant compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialExceptionalImage

open FrobeniusBlowupContact FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialMap FrobeniusBlowupDifferentialRestriction
open FrobeniusBlowupDifferentialPullbackComp
open FrobeniusCoordinateDifferentialFrame FrobeniusReesChartDifferentialFrame
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartBaseAlgebra
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra

/-- The original plane frame, extended along the actual plane-to-chart map. -/
def planeChartFrameEquiv : planeChartModule k ≃ₗ[reesChartRing k] reesChartRing k :=
  (LinearEquiv.baseChange (planeRing k) (reesChartRing k)
    (⋀[planeRing k]^2 (PlaneDifferential k)) (planeRing k)
      (coordinateTopDifferentialEquiv (k := k))).trans
    (TensorProduct.AlgebraTensorModule.rid
      (planeRing k) (reesChartRing k) (reesChartRing k))

theorem planeChartFrameEquiv_coordinate :
    planeChartFrameEquiv (k := k)
      (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = 1 := by
  change algebraMap (planeRing k) (reesChartRing k)
    (coordinateTopDifferentialEquiv (k := k) (coordinateTopForm (k := k))) * 1 = 1
  rw [coordinateTopDifferentialEquiv_apply,
    coordinateTopFormEvaluator_coordinateTopForm, map_one, mul_one]

/-- Every element of the actual scalar extension is a multiple of the
extended original coordinate wedge. -/
theorem planeChartFrame_expansion (ω : planeChartModule k) :
    planeChartFrameEquiv (k := k) ω •
      (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = ω := by
  apply (planeChartFrameEquiv (k := k)).injective
  rw [LinearEquiv.map_smul, planeChartFrameEquiv_coordinate, smul_eq_mul, mul_one]

/-- The previously constructed exterior differential is multiplication by
the actual exceptional equation on the whole original source module. -/
theorem planeChartTopMap_frame (ω : planeChartModule k) :
    planeChartTopMap (k := k) ω =
      (planeChartFrameEquiv (k := k) ω * chartU (k := k)) •
        chartCoordinateTopForm (k := k) := by
  calc
    _ = planeChartTopMap (k := k)
        (planeChartFrameEquiv (k := k) ω •
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) :=
      congrArg (planeChartTopMap (k := k)) (planeChartFrame_expansion ω).symm
    _ = planeChartFrameEquiv (k := k) ω •
        planeChartTopMap (k := k) (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) :=
      LinearMap.map_smul (planeChartTopMap (k := k))
        (planeChartFrameEquiv (k := k) ω)
        (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))
    _ = planeChartFrameEquiv (k := k) ω •
        (chartU (k := k) • chartCoordinateTopForm (k := k)) :=
      congrArg (fun η : ⋀[reesChartRing k]^2 (ChartDifferential k) =>
        planeChartFrameEquiv (k := k) ω • η) (planeChartTopMap_coordinate (k := k))
    _ = _ := smul_smul (planeChartFrameEquiv (k := k) ω)
      (chartU (k := k)) (chartCoordinateTopForm (k := k))

/-- Coefficient of the actual top-differential map in the proved native frame. -/
def planeChartDeterminant : planeChartModule k →ₗ[reesChartRing k] reesChartRing k :=
  (chartTopDifferentialEquiv (k := k)).toLinearMap.comp (planeChartTopMap (k := k))

theorem planeChartDeterminant_apply (ω : planeChartModule k) :
    planeChartDeterminant (k := k) ω =
      planeChartFrameEquiv (k := k) ω * chartU (k := k) := by
  change chartTopDifferentialEquiv (k := k) (planeChartTopMap (k := k) ω) = _
  rw [planeChartTopMap_frame, LinearEquiv.map_smul, chartTopDifferentialEquiv_apply,
    chartTopFormEvaluator_coordinateTopForm, smul_eq_mul, mul_one]

/-- The actual image of the original center ideal on the original Rees chart. -/
abbrev exceptionalIdeal (k : Type u) [Field k] : Ideal (reesChartRing k) :=
  chartCenterIdeal (centerIdeal (k := k)) (centerU (k := k))

/-- Identify the existing Rees principalization with the coordinate in the
actual differential calculation. -/
theorem exceptionalIdeal_span :
    Ideal.span {chartU (k := k)} = exceptionalIdeal k :=
  span_chartCenterEquation (centerIdeal (k := k)) (centerU (k := k))

theorem chartU_mem_exceptionalIdeal : chartU (k := k) ∈ exceptionalIdeal k :=
  (chartCenterEquation (centerIdeal (k := k)) (centerU (k := k))).property

/-- Regularity is inherited from the actual Rees equation. -/
theorem chartU_regular : chartU (k := k) ∈ nonZeroDivisors (reesChartRing k) :=
  chartCenterEquation_regular (centerIdeal (k := k)) (centerU (k := k))

theorem planeChartDeterminant_mem (ω : planeChartModule k) :
    planeChartDeterminant (k := k) ω ∈ exceptionalIdeal k := by
  rw [planeChartDeterminant_apply]
  exact (exceptionalIdeal k).mul_mem_left _ (chartU_mem_exceptionalIdeal (k := k))

/-- The determinant lands in the original exceptional ideal. -/
def planeChartToExceptionalIdeal : planeChartModule k →ₗ[reesChartRing k] exceptionalIdeal k :=
  LinearMap.codRestrict (exceptionalIdeal k) (planeChartDeterminant (k := k))
    (planeChartDeterminant_mem (k := k))

theorem planeChartToExceptionalIdeal_val (ω : planeChartModule k) :
    (planeChartToExceptionalIdeal (k := k) ω : reesChartRing k) =
      planeChartDeterminant (k := k) ω := rfl

/-- Regularity of the original equation proves injectivity without a new
domain, determinant-rank, or nonvanishing premise. -/
theorem planeChartDeterminant_injective :
    Function.Injective (planeChartDeterminant (k := k)) := by
  intro ω η h
  apply (planeChartFrameEquiv (k := k)).injective
  rw [planeChartDeterminant_apply, planeChartDeterminant_apply] at h
  exact (mul_cancel_right_mem_nonZeroDivisors (chartU_regular (k := k))).mp h

theorem planeChartToExceptionalIdeal_injective :
    Function.Injective (planeChartToExceptionalIdeal (k := k)) := by
  intro ω η h
  exact planeChartDeterminant_injective (congrArg Subtype.val h)

/-- Every element of the original exceptional ideal is the determinant of
an element of the original scalar-extended plane top module. -/
theorem planeChartToExceptionalIdeal_surjective :
    Function.Surjective (planeChartToExceptionalIdeal (k := k)) := by
  intro r
  have hr : (r : reesChartRing k) ∈ Ideal.span {chartU (k := k)} := by
    rw [exceptionalIdeal_span]
    exact r.property
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hr
  refine ⟨(planeChartFrameEquiv (k := k)).symm a, ?_⟩
  apply Subtype.ext
  change planeChartDeterminant (k := k) ((planeChartFrameEquiv (k := k)).symm a) = _
  rw [planeChartDeterminant_apply, LinearEquiv.apply_symm_apply]
  exact ha

/-- Equality with the original ideal, rather than only containment or a
statement about the value on one coordinate wedge. -/
theorem planeChartDeterminant_range :
    LinearMap.range (planeChartDeterminant (k := k)) = exceptionalIdeal k := by
  apply le_antisymm
  · rintro r ⟨ω, rfl⟩
    exact planeChartDeterminant_mem ω
  · intro r hr
    obtain ⟨ω, hω⟩ := planeChartToExceptionalIdeal_surjective (⟨r, hr⟩ : exceptionalIdeal k)
    exact ⟨ω, congrArg Subtype.val hω⟩

/-- The actual determinant identifies the original source with the original
exceptional ideal. -/
def planeChartExceptionalEquiv : planeChartModule k ≃ₗ[reesChartRing k] exceptionalIdeal k :=
  LinearEquiv.ofBijective (planeChartToExceptionalIdeal (k := k))
    ⟨planeChartToExceptionalIdeal_injective, planeChartToExceptionalIdeal_surjective⟩

theorem planeChartExceptionalEquiv_val (ω : planeChartModule k) :
    (planeChartExceptionalEquiv (k := k) ω : reesChartRing k) =
      planeChartDeterminant (k := k) ω := rfl

/-- The original differential map factors through the original exceptional
ideal inclusion and the inverse of the actual native differential frame. -/
theorem planeChartTopMap_factor :
    (chartTopDifferentialEquiv (k := k)).symm.toLinearMap.comp
        ((exceptionalIdeal k).subtype.comp (planeChartExceptionalEquiv (k := k)).toLinearMap) =
      planeChartTopMap (k := k) := by
  apply LinearMap.ext
  intro ω
  change (chartTopDifferentialEquiv (k := k)).symm
    (chartTopDifferentialEquiv (k := k) (planeChartTopMap (k := k) ω)) = _
  exact (chartTopDifferentialEquiv (k := k)).symm_apply_apply _

theorem planeChartTopMap_injective : Function.Injective (planeChartTopMap (k := k)) := by
  intro ω η h
  exact planeChartDeterminant_injective
    (congrArg (chartTopDifferentialEquiv (k := k)) h)

end KltDP.Examples.FrobeniusBlowupDifferentialExceptionalImage
