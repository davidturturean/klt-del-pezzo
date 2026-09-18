import KltDP.Geometry.NullCurveIntersectionMatrix
import KltDP.Geometry.QCartierPullback
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Original intersection numbers extended to actual rational Weil sums

The linear map is the finite sum of the original prime Cartier degrees.
Its value on each original Cartier divisor is its original intersection
number. The actual matrix row on a divisor's finite support is that same sum.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
open scoped BigOperators
universe u

namespace KltDP.Geometry.RationalWeilIntersection

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (S : NormalProjectiveSurface k)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

/-- Linear extension of the original degree on the original prime divisors. -/
def degreeLinearMap (C : S.PrimeCurve) : S.RationalWeilDivisor →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ
    (fun E => (C.intersectionNumber (S.primeCurveCartier hregular E) : ℚ))

theorem degreeLinearMap_apply (C : S.PrimeCurve) (D : S.RationalWeilDivisor) :
    degreeLinearMap S hregular C D =
      ∑ E ∈ D.support, D E * (C.intersectionNumber (S.primeCurveCartier hregular E) : ℚ) := rfl

/-- The extension recovers the original intersection of every signed Cartier divisor. -/
@[simp]
theorem degreeLinearMap_rationalCartier (C : S.PrimeCurve) (D : CartierDivisor S.toScheme) :
    degreeLinearMap S hregular C (S.rationalCartierToWeilHom D) =
      (C.intersectionNumber D : ℚ) := by
  rw [degreeLinearMap_apply]
  change (∑ E ∈ (rationalizeWeilDivisor S (S.cartierToWeilHom D)).support,
    (rationalizeWeilDivisor S (S.cartierToWeilHom D)) E *
      (C.intersectionNumber (S.primeCurveCartier hregular E) : ℚ)) = _
  rw [rationalizeWeilDivisor_componentSupport,
    S.intersectionNumber_eq_weil_sum hregular C D]
  simp only [Finsupp.sum, rationalizeWeilDivisor_apply,
    primeCurveMatrix, Int.cast_sum, Int.cast_mul]

/-- The original matrix applied to the actual coefficient vector computes
the original rational intersection, using precisely the divisor's support. -/
theorem intersectionMatrix_mulVec_support (D : S.RationalWeilDivisor) (i : D.support) :
    (NullCurveIntersectionMatrix.intersectionMatrix S hregular
      (fun E : D.support => E.val) *ᵥ (fun E : D.support => D E.val)) i =
      degreeLinearMap S hregular i.val D := by
  classical
  simp only [Matrix.mulVec, dotProduct, NullCurveIntersectionMatrix.intersectionMatrix,
    degreeLinearMap_apply]
  rw [← Finset.sum_coe_sort D.support]
  apply Finset.sum_congr rfl
  intro E hE
  rw [S.intersectionPairing_symm hregular
      (S.primeCurveCartier hregular i.val) (S.primeCurveCartier hregular E.val),
    S.intersectionPairing_primeCurve]
  exact mul_comm _ _

end KltDP.Geometry.RationalWeilIntersection

#check @KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_rationalCartier
#print axioms KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_rationalCartier
#print axioms KltDP.Geometry.RationalWeilIntersection.intersectionMatrix_mulVec_support
