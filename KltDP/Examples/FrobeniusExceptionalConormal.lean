import KltDP.Examples.FrobeniusExceptionalOverlap
import KltDP.Geometry.AffineBlowupConormalFrames

/-!
# Actual plane-blowup conormal and normal transition coefficients

The actual exceptional overlap is identified with the Laurent polynomial
ring by the proved quotient-localization equivalence. The two conormal
frames are the restricted classes of the actual equations u and v.
Their transition unit maps to T, and the inverse unit maps to T⁻¹.

The coordinate maps below are actual semilinear maps on the conormal
module and its quotient-linear dual. Their transition laws distinguish
frame changes from coordinate changes explicitly. These are the local
formulas for the later O(1) conormal / O(-1) normal comparison; no global
line-bundle or projective-line identification is assumed here.
-/

noncomputable section

namespace KltDP.Examples.FrobeniusExceptionalConormal

open KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalOverlap

universe u

variable {k : Type u} [Field k]

/-- The actual ring of the exceptional intersection, before transport
to its proved Laurent presentation. -/
abbrev overlapRing := exceptionalOverlapRing centerIdeal (centerU (k := k)) centerV

/-- The actual conormal module of the original extended center on the intersection. -/
abbrev overlapConormal :=
  (conormalOverlapIdeal centerIdeal (centerU (k := k)) centerV).Cotangent

/-- The actual quotient-linear dual of that conormal module. -/
abbrev overlapNormal := Module.Dual (overlapRing (k := k)) (overlapConormal (k := k))

/-- The original conormal frame transition is the Laurent coordinate T. -/
@[simp] theorem transitionUnit_image :
    exceptionalOverlapLaurentEquiv
      (exceptionalOverlapTransitionUnit centerIdeal (centerU (k := k)) centerV :
        overlapRing (k := k)) = LaurentPolynomial.T 1 :=
  exceptionalOverlapLaurentEquiv_ratio

/-- The inverse unit is the actual second chart coordinate, hence T⁻¹. -/
@[simp] theorem transitionUnit_inv_image :
    exceptionalOverlapLaurentEquiv
      (↑((exceptionalOverlapTransitionUnit centerIdeal (centerU (k := k)) centerV)⁻¹) :
        overlapRing (k := k)) = LaurentPolynomial.T (-1) :=
  exceptionalOverlapLaurentEquiv_right_coordinate

/-- Actual conormal coordinates in the left equation frame, transported
through the proved Laurent ring equivalence. -/
def leftConormalCoordinate : overlapConormal (k := k) →ₛₗ[
    (exceptionalOverlapLaurentEquiv (k := k)).toRingHom] LaurentPolynomial k :=
  (exceptionalOverlapLaurentEquiv (k := k)).toRingHom.toSemilinearMap.comp
    (conormalOverlapNormalFrameLeft centerIdeal centerU centerV)

/-- Actual conormal coordinates in the right equation frame. -/
def rightConormalCoordinate : overlapConormal (k := k) →ₛₗ[
    (exceptionalOverlapLaurentEquiv (k := k)).toRingHom] LaurentPolynomial k :=
  (exceptionalOverlapLaurentEquiv (k := k)).toRingHom.toSemilinearMap.comp
    (conormalOverlapNormalFrameRight centerIdeal centerU centerV)

theorem leftConormalCoordinate_bijective :
    Function.Bijective (leftConormalCoordinate (k := k)) :=
  exceptionalOverlapLaurentEquiv.bijective.comp
    (conormalOverlapEquiv centerIdeal (centerU (k := k)) centerV).symm.bijective

theorem rightConormalCoordinate_bijective :
    Function.Bijective (rightConormalCoordinate (k := k)) :=
  exceptionalOverlapLaurentEquiv.bijective.comp
    (conormalOverlapRightEquiv centerIdeal (centerU (k := k)) centerV).symm.bijective

/-- Conormal coordinates transform inversely to the conormal frames.
This is the explicit T⁻¹ coordinate relation on the actual module. -/
theorem conormal_coordinate_transition (m : overlapConormal (k := k)) :
    rightConormalCoordinate m = LaurentPolynomial.T (-1) * leftConormalCoordinate m := by
  change exceptionalOverlapLaurentEquiv
    (conormalOverlapNormalFrameRight centerIdeal centerU centerV m) =
      LaurentPolynomial.T (-1) * exceptionalOverlapLaurentEquiv
        (conormalOverlapNormalFrameLeft centerIdeal centerU centerV m)
  rw [conormalOverlap_normal_frames_transition (centerIdeal (k := k)) centerU centerV]
  simp only [LinearMap.smul_apply, Units.smul_def, smul_eq_mul,
    map_mul, transitionUnit_inv_image]

/-- Coordinates of a normal functional are its actual values on the
left conormal frame, followed by the actual Laurent ring equivalence. -/
def leftNormalCoordinate : overlapNormal (k := k) →ₛₗ[
    (exceptionalOverlapLaurentEquiv (k := k)).toRingHom] LaurentPolynomial k :=
  (exceptionalOverlapLaurentEquiv (k := k)).toRingHom.toSemilinearMap.comp
    (((conormalOverlapEquiv centerIdeal (centerU (k := k)) centerV).dualMap.trans
      (LinearMap.ringLmapEquivSelf (overlapRing (k := k))
        (overlapRing (k := k)) (overlapRing (k := k)))).toLinearMap)

/-- Coordinates of the same actual normal functional in the right frame. -/
def rightNormalCoordinate : overlapNormal (k := k) →ₛₗ[
    (exceptionalOverlapLaurentEquiv (k := k)).toRingHom] LaurentPolynomial k :=
  (exceptionalOverlapLaurentEquiv (k := k)).toRingHom.toSemilinearMap.comp
    (((conormalOverlapRightEquiv centerIdeal (centerU (k := k)) centerV).dualMap.trans
      (LinearMap.ringLmapEquivSelf (overlapRing (k := k))
        (overlapRing (k := k)) (overlapRing (k := k)))).toLinearMap)

/-- Normal coordinates transform by T, while the actual dual normal
frames transform by T⁻¹. -/
theorem normal_coordinate_transition (ℓ : overlapNormal (k := k)) :
    rightNormalCoordinate ℓ = LaurentPolynomial.T 1 * leftNormalCoordinate ℓ := by
  change exceptionalOverlapLaurentEquiv
    (ℓ (conormalOverlapRightEquiv centerIdeal centerU centerV 1)) =
      LaurentPolynomial.T 1 * exceptionalOverlapLaurentEquiv
        (ℓ (conormalOverlapEquiv centerIdeal centerU centerV 1))
  rw [conormalOverlapRightEquiv_one (centerIdeal (k := k)) centerU centerV,
    conormalOverlapEquiv_one (centerIdeal (k := k)) centerU centerV,
    conormalOverlap_frames_transition (centerIdeal (k := k)) centerU centerV, map_smul]
  simp only [smul_eq_mul, map_mul, transitionUnit_image]

end KltDP.Examples.FrobeniusExceptionalConormal
