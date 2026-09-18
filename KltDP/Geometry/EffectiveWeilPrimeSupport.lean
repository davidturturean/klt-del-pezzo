import KltDP.Geometry.NefIntersectionSectionVanishing
import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.Geometry.AmpleCurveRestrictionPositive
import KltDP.Geometry.RiemannRochEffectiveMultiple

/-!
# Negative intersection detects an actual prime component

An effective Weil divisor has nonnegative intersection with every prime
outside its finite support. In particular, an effective representative of
nD-H contains every degree-zero curve of D when H is ample. The argument
uses the original prime decomposition and rational-function equivalence.
-/

noncomputable section

open AlgebraicGeometry
open KltDP.Geometry.NormalProjectiveSurface
open scoped BigOperators

universe u

namespace KltDP.Geometry.EffectiveWeilPrimeSupport

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- Every prime outside the actual finite support of an effective Weil
divisor has nonnegative intersection with that divisor. -/
theorem intersection_nonneg_of_not_mem_support (E : X.WeilDivisor)
    (hE : EffectiveDivisor E) (C : X.PrimeCurve) (hC : C ∉ E.support) :
    0 ≤ intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm E)
      (X.primeCurveCartier hregular C) := by
  have hmap : X.cartierToWeilHom ((X.regularCartierWeilEquiv hregular).symm E) = E :=
    (X.regularCartierWeilEquiv hregular).apply_symm_apply E
  rw [X.intersectionPairing_eq_weil_sum_right hregular, hmap]
  change 0 ≤ ∑ P ∈ E.support, E P * P.intersectionNumber (X.primeCurveCartier hregular C)
  apply Finset.sum_nonneg
  intro P hP
  apply mul_nonneg (hE P)
  rw [← X.intersectionPairing_primeCurve hregular (X.primeCurveCartier hregular C) P]
  apply PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg X hregular C P
  intro hCP
  exact hC (hCP.symm ▸ hP)

/-- Negative intersection forces the original prime to occur in the
effective Weil divisor, with a nonzero actual coefficient. -/
theorem mem_support_of_intersection_neg (E : X.WeilDivisor)
    (hE : EffectiveDivisor E) (C : X.PrimeCurve)
    (hneg : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm E)
      (X.primeCurveCartier hregular C) < 0) : C ∈ E.support := by
  by_contra hC
  exact (not_le_of_gt hneg)
    (intersection_nonneg_of_not_mem_support X hregular E hE C hC)

/-- Every actual degree-zero prime of D occurs in any effective Weil
representative of nD-H, for the original ample Cartier divisor H. -/
theorem mem_support_of_degree_zero (D H : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (n : ℕ) (E : X.WeilDivisor) (hE : EffectiveDivisor E)
    (hED : X.LinearlyEquivalent E (X.cartierToWeilHom (n • D - H)))
    (C : X.PrimeCurve) (hC : C.intersectionNumber D = 0) : C ∈ E.support := by
  apply mem_support_of_intersection_neg X hregular E hE C
  rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent
    X hregular (X.primeCurveCartier hregular C) hED,
    RiemannRochEffectiveMultiple.inverse_toWeil,
    sub_eq_add_neg (n • D), X.intersectionPairing_add_left,
    X.intersectionPairing_neg_left,
    RiemannRochEffectiveMultiple.intersection_nsmul_left,
    X.intersectionPairing_primeCurve, X.intersectionPairing_primeCurve, hC]
  have hpos : 0 < C.intersectionNumber H := by
    rw [C.intersectionNumber_eq_restrictionDegree H]
    exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme H) hH C
  omega

end KltDP.Geometry.EffectiveWeilPrimeSupport
