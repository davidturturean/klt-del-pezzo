import KltDP.Examples.FrobeniusBlowupDifferentialRightFrame
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The complementary determinant image is the original exceptional ideal

The actual top-differential map has coefficient `-v` in the proved original
right-chart frame. Its range is exactly the original extended center ideal;
regularity of the original Rees equation proves injectivity. The sign of the
native wedge affects the normalized generator, but not the original ideal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialRightExceptionalImage

open FrobeniusBlowupContact FrobeniusBlowupDifferential FrobeniusBlowupDifferentialOverlap
open FrobeniusBlowupDifferentialRightMap FrobeniusBlowupDifferentialRightFrame
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (rightChartRing k) :=
  FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra

/-- Coordinate of the entire actual second-chart exterior differential. -/
def planeRightDeterminant : planeRightModule k →ₗ[rightChartRing k] rightChartRing k :=
  (rightTopDifferentialEquiv (k := k)).toLinearMap.comp (planeRightTopMap (k := k))

theorem planeRightDeterminant_apply (ω : planeRightModule k) :
    planeRightDeterminant (k := k) ω =
      planeRightFrameEquiv (k := k) ω * (-rightV (k := k)) :=
  rightTopDifferentialEquiv_differential ω

/-- The actual image of the original center on the complementary Rees chart. -/
abbrev rightExceptionalIdeal (k : Type u) [Field k] : Ideal (rightChartRing k) :=
  chartCenterIdeal (centerIdeal (k := k)) (centerV (k := k))

theorem rightExceptionalIdeal_span :
    Ideal.span {rightV (k := k)} = rightExceptionalIdeal k :=
  span_chartCenterEquation (centerIdeal (k := k)) (centerV (k := k))

theorem rightExceptionalIdeal_span_neg :
    Ideal.span {-rightV (k := k)} = rightExceptionalIdeal k :=
  (Ideal.span_singleton_neg (rightV (k := k))).trans (rightExceptionalIdeal_span (k := k))

theorem rightV_mem_exceptionalIdeal : rightV (k := k) ∈ rightExceptionalIdeal k :=
  (chartCenterEquation (centerIdeal (k := k)) (centerV (k := k))).property

theorem rightV_regular : rightV (k := k) ∈ nonZeroDivisors (rightChartRing k) :=
  chartCenterEquation_regular (centerIdeal (k := k)) (centerV (k := k))

theorem planeRightDeterminant_mem (ω : planeRightModule k) :
    planeRightDeterminant (k := k) ω ∈ rightExceptionalIdeal k := by
  rw [planeRightDeterminant_apply]
  exact (rightExceptionalIdeal k).mul_mem_left _
    ((rightExceptionalIdeal k).neg_mem (rightV_mem_exceptionalIdeal (k := k)))

def planeRightToExceptionalIdeal :
    planeRightModule k →ₗ[rightChartRing k] rightExceptionalIdeal k :=
  LinearMap.codRestrict (rightExceptionalIdeal k) (planeRightDeterminant (k := k))
    (planeRightDeterminant_mem (k := k))

theorem planeRightDeterminant_injective :
    Function.Injective (planeRightDeterminant (k := k)) := by
  intro ω η h
  apply (planeRightFrameEquiv (k := k)).injective
  rw [planeRightDeterminant_apply, planeRightDeterminant_apply, mul_neg, mul_neg, neg_inj] at h
  exact (mul_cancel_right_mem_nonZeroDivisors (rightV_regular (k := k))).mp h

theorem planeRightToExceptionalIdeal_injective :
    Function.Injective (planeRightToExceptionalIdeal (k := k)) := by
  intro ω η h
  exact planeRightDeterminant_injective (congrArg Subtype.val h)

theorem planeRightToExceptionalIdeal_surjective :
    Function.Surjective (planeRightToExceptionalIdeal (k := k)) := by
  intro r
  have hr : (r : rightChartRing k) ∈ Ideal.span {-rightV (k := k)} := by
    rw [rightExceptionalIdeal_span_neg]
    exact r.property
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hr
  refine ⟨(planeRightFrameEquiv (k := k)).symm a, ?_⟩
  apply Subtype.ext
  change planeRightDeterminant (k := k) ((planeRightFrameEquiv (k := k)).symm a) = _
  rw [planeRightDeterminant_apply, LinearEquiv.apply_symm_apply]
  exact ha

/-- The determinant image is the original ideal on the original second chart. -/
theorem planeRightDeterminant_range :
    LinearMap.range (planeRightDeterminant (k := k)) = rightExceptionalIdeal k := by
  apply le_antisymm
  · rintro r ⟨ω, rfl⟩
    exact planeRightDeterminant_mem ω
  · intro r hr
    obtain ⟨ω, hω⟩ := planeRightToExceptionalIdeal_surjective
      (⟨r, hr⟩ : rightExceptionalIdeal k)
    exact ⟨ω, congrArg Subtype.val hω⟩

def planeRightExceptionalEquiv :
    planeRightModule k ≃ₗ[rightChartRing k] rightExceptionalIdeal k :=
  LinearEquiv.ofBijective (planeRightToExceptionalIdeal (k := k))
    ⟨planeRightToExceptionalIdeal_injective, planeRightToExceptionalIdeal_surjective⟩

/-- The original plane wedge gives minus the original exceptional equation,
as an element of the actual ideal and before any exceptional quotient. -/
theorem planeRightExceptionalEquiv_coordinate :
    planeRightExceptionalEquiv (k := k)
        (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      -chartCenterEquation (centerIdeal (k := k)) (centerV (k := k)) := by
  apply Subtype.ext
  change planeRightDeterminant (k := k)
    (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = -rightV (k := k)
  rw [planeRightDeterminant_apply, planeRightFrameEquiv_coordinate, one_mul]

theorem planeRightTopMap_factor :
    (rightTopDifferentialEquiv (k := k)).symm.toLinearMap.comp
        ((rightExceptionalIdeal k).subtype.comp (planeRightExceptionalEquiv (k := k)).toLinearMap) =
      planeRightTopMap (k := k) := by
  apply LinearMap.ext
  intro ω
  change (rightTopDifferentialEquiv (k := k)).symm
    (rightTopDifferentialEquiv (k := k) (planeRightTopMap (k := k) ω)) = _
  exact (rightTopDifferentialEquiv (k := k)).symm_apply_apply _

theorem planeRightTopMap_injective : Function.Injective (planeRightTopMap (k := k)) := by
  intro ω η h
  exact planeRightDeterminant_injective
    (congrArg (rightTopDifferentialEquiv (k := k)) h)

end KltDP.Examples.FrobeniusBlowupDifferentialRightExceptionalImage
