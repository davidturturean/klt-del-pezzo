/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Paul Lezeau, Junyan Xu
-/
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Scaling a minimal polynomial over an integrally closed domain

Bounded port of `IsIntegrallyClosed.minpoly_smul` from official Mathlib
`5aedf732b6987e8c26ab3c9ebc855314f82b045f`,
`Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean:175–197`.
Original whole-file SHA-256:
`bd3d00c600bac2f6373adc035722fa59c3a33e148249932117bac5cd316b1976`.

The actual polynomial proof is preserved. Its torsion-free hypothesis is
spelled using the pinned `NoZeroSMulDivisors` interface, and the existing
fraction-field scalar tower is installed explicitly. No new field map or
minimal-polynomial equality is assumed.
-/

noncomputable section

namespace KltDP.Compatibility

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] [NoZeroSMulDivisors R S] [IsIntegrallyClosed R]

/-- The minimal polynomial of an actual nonzero scalar multiple is the
root-scaled original minimal polynomial. -/
theorem minpoly_smul {r : R} (hr : r ≠ 0) {s : S} (hs : IsIntegral R s) :
    minpoly R (r • s) = (minpoly R s).scaleRoots r := by
  let K := FractionRing R
  let L := FractionRing S
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  apply map_injective _ (FaithfulSMul.algebraMap_injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L (hs.smul r),
    map_scaleRoots _ _ _ (by simpa [minpoly.ne_zero_iff]),
    ← minpoly.isIntegrallyClosed_eq_field_fractions K L hs]
  simp_rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R K L]
  refine eq_of_monic_of_associated (minpoly.monic ?_) ?_
    (associated_of_dvd_dvd (minpoly.dvd _ _ ?_) ?_)
  · exact isIntegral_algebraMap.mul (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · simpa [monic_scaleRoots_iff] using minpoly.monic
      (hs.map (IsScalarTower.toAlgHom R S L)).tower_top
  · exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)
  · rw [← Polynomial.scaleRoots_dvd_iff _ _ (r := (algebraMap R K r)⁻¹)
        (IsUnit.mk0 _ (by simpa)),
      ← scaleRoots_mul, mul_inv_cancel₀ (by simpa), scaleRoots_one]
    refine minpoly.dvd _ _ ?_
    nth_rw 1 [← inv_mul_cancel_left₀ (b := algebraMap S L s)
      (a := algebraMap K L (algebraMap R K r)) (by simpa), ← map_inv₀]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval _ _)

end KltDP.Compatibility
