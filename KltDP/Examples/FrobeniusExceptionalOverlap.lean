import KltDP.Examples.FrobeniusExceptionalCharts
import KltDP.Geometry.AffineBlowupExceptionalOverlap
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Reciprocal coordinates on the actual plane-blowup exceptional overlap

The actual quotient of the homogeneous product chart is proved to be
`k[T,T⁻¹]` by its derived localization property. Its first and second
exceptional affine-line coordinates are `T` and `T⁻¹`. Both full ring
restriction maps are identified, including the original coefficient field.
These are the ring comparisons needed for the global fiber gluing.
-/

noncomputable section

namespace KltDP.Examples.FrobeniusExceptionalOverlap

open KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusExceptionalCharts

universe u

variable {k : Type u} [Field k]

/-- The actual exceptional overlap ring, localized by its first affine-line coordinate. -/
def exceptionalOverlapLaurentEquiv :
    exceptionalOverlapRing centerIdeal (centerU (k := k)) centerV ≃+* LaurentPolynomial k := by
  letI := (exceptionalOverlapLeft centerIdeal (centerU (k := k)) centerV).toAlgebra
  letI : IsLocalization
      (Submonoid.powers
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU) (chartW (k := k))))
      (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV) :=
    exceptionalOverlapLeft_isLocalization centerIdeal (centerU (k := k)) centerV
  exact IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU) (chartW (k := k))))
    (T := Submonoid.powers (Polynomial.X : Polynomial k))
    (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV) (LaurentPolynomial k)
    uExceptionalEquiv (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers uExceptionalEquiv_coordinate)

/-- The entire first restriction is the usual polynomial-to-Laurent map. -/
theorem exceptionalOverlapLaurentEquiv_left
    (x : exceptionalChartRing centerIdeal (centerU (k := k))) :
    exceptionalOverlapLaurentEquiv (exceptionalOverlapLeft centerIdeal centerU centerV x) =
      Polynomial.toLaurent (uExceptionalEquiv x) := by
  letI := (exceptionalOverlapLeft centerIdeal (centerU (k := k)) centerV).toAlgebra
  letI : IsLocalization
      (Submonoid.powers
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU) (chartW (k := k))))
      (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV) :=
    exceptionalOverlapLeft_isLocalization centerIdeal (centerU (k := k)) centerV
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (M := Submonoid.powers
      (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU) (chartW (k := k))))
    (T := Submonoid.powers (Polynomial.X : Polynomial k))
    (S := exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV)
    (Q := LaurentPolynomial k) (j := uExceptionalEquiv (k := k))
    (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (uExceptionalEquiv_coordinate (k := k))) x

/-- The existing conormal transition ratio becomes the Laurent coordinate `T`. -/
@[simp] theorem exceptionalOverlapLaurentEquiv_ratio :
    exceptionalOverlapLaurentEquiv (k := k)
      (Ideal.Quotient.mk (conormalOverlapIdeal (centerIdeal (k := k)) centerU centerV)
        (conormalOverlapRatio centerIdeal (centerU (k := k)) centerV)) =
          LaurentPolynomial.T 1 := by
  change exceptionalOverlapLaurentEquiv
    (exceptionalOverlapLeft centerIdeal centerU centerV
      (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU) chartW)) = _
  rw [exceptionalOverlapLaurentEquiv_left, uExceptionalEquiv_coordinate, Polynomial.toLaurent_X]

/-- The second actual affine-line coordinate is the inverse Laurent coordinate. -/
@[simp] theorem exceptionalOverlapLaurentEquiv_right_coordinate :
    exceptionalOverlapLaurentEquiv (k := k)
      (exceptionalOverlapRight centerIdeal centerU centerV
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
          (chartFraction centerIdeal (centerV (k := k)) centerU))) =
      LaurentPolynomial.T (-1) := by
  have h := congrArg (exceptionalOverlapLaurentEquiv (k := k))
    (exceptionalOverlap_chartFractions_mul centerIdeal (centerU (k := k)) centerV)
  rw [map_mul, exceptionalOverlapLeft_mk, map_one] at h
  change exceptionalOverlapLaurentEquiv (k := k)
      (Ideal.Quotient.mk (conormalOverlapIdeal (centerIdeal (k := k)) centerU centerV)
        (conormalOverlapRatio centerIdeal centerU centerV)) *
    exceptionalOverlapLaurentEquiv (k := k)
      (exceptionalOverlapRight centerIdeal centerU centerV
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
          (chartFraction centerIdeal centerV centerU))) = 1 at h
  rw [exceptionalOverlapLaurentEquiv_ratio] at h
  calc
    _ = (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) *
        exceptionalOverlapLaurentEquiv
          (exceptionalOverlapRight centerIdeal centerU centerV
            (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
              (chartFraction centerIdeal centerV centerU))) := by
      rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
    _ = _ := by rw [mul_assoc, h, mul_one]

/-- The two actual quotient restrictions agree on every original scalar. -/
theorem exceptionalOverlap_constants (r : k) :
    exceptionalOverlapLeft centerIdeal (centerU (k := k)) centerV
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU)
          (chartConstants centerU r)) =
      exceptionalOverlapRight centerIdeal centerU centerV
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
          (chartConstants centerV r)) := by
  change Ideal.Quotient.mk (conormalOverlapIdeal (centerIdeal (k := k)) centerU centerV)
      (conormalOverlapLeft centerIdeal centerU centerV
        (chartBaseMap centerIdeal centerU (planeConstants r))) =
    Ideal.Quotient.mk (conormalOverlapIdeal (centerIdeal (k := k)) centerU centerV)
      (conormalOverlapRight centerIdeal centerU centerV
        (chartBaseMap centerIdeal centerV (planeConstants r)))
  rw [conormalOverlapLeft_baseMap, conormalOverlapRight_baseMap]

/-- The second coordinate restriction fixes the actual coefficient field. -/
@[simp] theorem exceptionalOverlapLaurentEquiv_right_constants (r : k) :
    exceptionalOverlapLaurentEquiv
      (exceptionalOverlapRight centerIdeal (centerU (k := k)) centerV
        (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
          (chartConstants centerV r))) =
      LaurentPolynomial.C r := by
  rw [← exceptionalOverlap_constants, exceptionalOverlapLaurentEquiv_left,
    uExceptionalEquiv_constants, Polynomial.toLaurent_C]

/-- The complete second restriction is polynomial inclusion followed by inversion of `T`. -/
theorem exceptionalOverlapLaurentEquiv_right
    (x : exceptionalChartRing centerIdeal (centerV (k := k))) :
    exceptionalOverlapLaurentEquiv (exceptionalOverlapRight centerIdeal centerU centerV x) =
      LaurentPolynomial.invert (Polynomial.toLaurent (vExceptionalEquiv x)) := by
  have h : ((exceptionalOverlapLaurentEquiv (k := k)).toRingHom.comp
      (exceptionalOverlapRight centerIdeal centerU centerV)).comp
        (vExceptionalEquiv (k := k)).symm.toRingHom =
      (LaurentPolynomial.invert (R := k)).toRingHom.comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro r
      have hc : (vExceptionalEquiv (k := k)).symm (Polynomial.C r) =
          Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
            (chartConstants centerV r) := by
        apply (vExceptionalEquiv (k := k)).injective
        rw [(vExceptionalEquiv (k := k)).apply_symm_apply, vExceptionalEquiv_constants]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.coe_ringEquiv']
      rw [hc, exceptionalOverlapLaurentEquiv_right_constants,
        Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
    · have hx : (vExceptionalEquiv (k := k)).symm Polynomial.X =
          Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
            (chartFraction centerIdeal (centerV (k := k)) centerU) := by
        apply (vExceptionalEquiv (k := k)).injective
        rw [(vExceptionalEquiv (k := k)).apply_symm_apply, vExceptionalEquiv_coordinate]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.coe_ringEquiv']
      rw [hx, exceptionalOverlapLaurentEquiv_right_coordinate,
        Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
  have hx := RingHom.congr_fun h (vExceptionalEquiv x)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, AlgEquiv.coe_ringEquiv', RingEquiv.symm_apply_apply] using hx

end KltDP.Examples.FrobeniusExceptionalOverlap
