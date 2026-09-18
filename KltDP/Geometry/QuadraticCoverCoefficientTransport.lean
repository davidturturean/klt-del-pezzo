import KltDP.Geometry.QuadraticCoverMappedRescaling

/-!
# Coefficients of the original quadratic atlas maps

The actual restriction-and-rescaling homomorphism preserves the constant
coefficient and multiplies the root coefficient by the original transition
unit. Consequently matching functions on two original quadratic charts
have an ordinary matching constant part and an inverse-transition root
part. This fixes the dual, rather than positive, line bundle in the cover
algebra decomposition. No matching-coefficient equation is an input.
-/

noncomputable section

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual quotient map on a scalar-plus-root expression. -/
theorem mappedRescaleHom_ofCoeffs (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (a b : R) :
    mappedRescaleHom f s t v h (ofCoeffs s a b) =
      ofCoeffs t (f a) (f b * (v : S)) := by
  simp only [ofCoeffs, map_add, map_mul, mappedRescaleHom_algebraMap,
    mappedRescaleHom_root, mul_assoc]

variable [Nontrivial R] [Nontrivial S]

/-- Constant coordinates follow the original coefficient restriction. -/
@[simp]
theorem constantCoeff_mappedRescaleHom (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (x : CoverAlgebra s) :
    constantCoeff t (mappedRescaleHom f s t v h x) = f (constantCoeff s x) := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [mappedRescaleHom_ofCoeffs, constantCoeff_ofCoeffs]

/-- Root coordinates retain the original generator-change unit. -/
@[simp]
theorem rootCoeff_mappedRescaleHom (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (x : CoverAlgebra s) :
    rootCoeff t (mappedRescaleHom f s t v h x) =
      f (rootCoeff s x) * (v : S) := by
  conv_lhs => rw [← ofCoeffs_coefficients s x]
  rw [mappedRescaleHom_ofCoeffs, rootCoeff_ofCoeffs]

/-- The original rank-two coordinates commute with an actual atlas map. -/
theorem coordinatesEquiv_mappedRescaleHom (f : R →+* S)
    (s : R) (t : S) (v : Sˣ) (h : f s = (v : S) ^ 2 * t)
    (x : CoverAlgebra s) :
    coordinatesEquiv t (mappedRescaleHom f s t v h x) =
      (f (constantCoeff s x), f (rootCoeff s x) * (v : S)) := by
  exact Prod.ext (constantCoeff_mappedRescaleHom f s t v h x)
    (rootCoeff_mappedRescaleHom f s t v h x)

/-- Equality of the original chart functions is exactly matching of their
constant and inverse-transition coordinates. -/
theorem mappedRescaleHom_eq_iff (f : R →+* S) (s : R) (t : S) (v : Sˣ)
    (h : f s = (v : S) ^ 2 * t) (x : CoverAlgebra s) (y : CoverAlgebra t) :
    mappedRescaleHom f s t v h x = y ↔
      f (constantCoeff s x) = constantCoeff t y ∧
        f (rootCoeff s x) = ((v⁻¹ : Sˣ) : S) * rootCoeff t y := by
  constructor
  · intro he
    constructor
    · simpa only [constantCoeff_mappedRescaleHom] using
        congrArg (constantCoeff t) he
    · have hb := congrArg (rootCoeff t) he
      rw [rootCoeff_mappedRescaleHom] at hb
      exact (Units.eq_inv_mul_iff_mul_eq v).mpr (by simpa only [mul_comm] using hb)
  · rintro ⟨ha, hb⟩
    apply (coordinatesEquiv t).injective
    apply Prod.ext
    · exact (constantCoeff_mappedRescaleHom f s t v h x).trans ha
    · change rootCoeff t (mappedRescaleHom f s t v h x) = rootCoeff t y
      rw [rootCoeff_mappedRescaleHom]
      simpa only [mul_comm] using (Units.eq_inv_mul_iff_mul_eq v).mp hb

end KltDP.Geometry.QuadraticCover

#check @KltDP.Geometry.QuadraticCover.mappedRescaleHom_eq_iff
#print axioms KltDP.Geometry.QuadraticCover.mappedRescaleHom_eq_iff
