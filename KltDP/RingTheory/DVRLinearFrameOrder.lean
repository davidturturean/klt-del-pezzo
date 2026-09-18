import KltDP.Compatibility.ModuleTransitionUnit
import KltDP.Geometry.DivisorOrder

/-!
# Original DVR order under actual linear changes of frame

The accepted transition unit of two actual rank-one trivializations
identifies their evaluated elements. Its original DVR order is zero.
No equality of orders or arbitrary proportionality scalar is an input.
-/

noncomputable section

universe u v w

namespace KltDP.RingTheory.DVRLinearFrameOrder

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    {M : Type w} [AddCommGroup M] [Module R M]
    (t₁ t₂ : M ≃ₗ[R] R) (z : M)

/-- Nonzero coordinates remain nonzero through the derived actual unit. -/
theorem coordinate_ne_zero (hz : t₁ z ≠ 0) : t₂ z ≠ 0 := by
  rw [← KltDP.Module.transitionUnit_mul_apply t₁ t₂ z]
  exact mul_ne_zero (KltDP.Module.transitionUnit t₁ t₂).ne_zero hz

/-- The two original field units are related by the image of the actual
linear transition unit over the same original DVR. -/
theorem fractionFieldUnit_coordinate
    (hz : t₁ z ≠ 0) :
    fractionFieldUnit R K (t₂ z) (coordinate_ne_zero R t₁ t₂ z hz) =
      Units.map (algebraMap R K) (KltDP.Module.transitionUnit t₁ t₂) *
        fractionFieldUnit R K (t₁ z) hz := by
  apply Units.ext
  change algebraMap R K (t₂ z) =
    algebraMap R K (KltDP.Module.transitionUnit t₁ t₂ : R) * algebraMap R K (t₁ z)
  rw [← map_mul, KltDP.Module.transitionUnit_mul_apply]

/-- Every actual rank-one linear coordinate computes the same original
divisor order of the same nonzero element. -/
theorem order_eq (hz : t₁ z ≠ 0) :
    divisorOrder R K (fractionFieldUnit R K (t₂ z)
        (coordinate_ne_zero R t₁ t₂ z hz)) =
      divisorOrder R K (fractionFieldUnit R K (t₁ z) hz) := by
  rw [fractionFieldUnit_coordinate R K t₁ t₂ z hz, divisorOrder_mul,
    divisorOrder_map_unit, zero_add]

end KltDP.RingTheory.DVRLinearFrameOrder

#check @KltDP.RingTheory.DVRLinearFrameOrder.order_eq
#print axioms KltDP.RingTheory.DVRLinearFrameOrder.order_eq
