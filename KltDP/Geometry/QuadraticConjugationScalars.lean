import KltDP.Geometry.QuadraticCoverAlgebra

/-! # Scalar sum and product of the original quadratic conjugates -/

noncomputable section

namespace KltDP.Geometry.QuadraticCover

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The sum with the actual conjugate is the constant twice the original constant coordinate. -/
theorem add_conjugation_eq_scalar (s : R) (z : CoverAlgebra s) :
    z + conjugation s z = algebraMap R (CoverAlgebra s) (2 * constantCoeff s z) := by
  apply (coordinatesEquiv s).injective
  apply Prod.ext
  · change constantCoeff s (z + conjugation s z) =
      constantCoeff s (algebraMap R (CoverAlgebra s) (2 * constantCoeff s z))
    rw [map_add, constantCoeff_conjugation, constantCoeff_algebraMap, two_mul]
  · change rootCoeff s (z + conjugation s z) =
      rootCoeff s (algebraMap R (CoverAlgebra s) (2 * constantCoeff s z))
    rw [map_add, rootCoeff_conjugation, rootCoeff_algebraMap, add_neg_cancel]

/-- The product with the actual conjugate is the original quadratic norm scalar. -/
theorem mul_conjugation_eq_scalar (s : R) (z : CoverAlgebra s) :
    z * conjugation s z = algebraMap R (CoverAlgebra s)
      (constantCoeff s z ^ 2 - s * rootCoeff s z ^ 2) := by
  let a := constantCoeff s z
  let b := rootCoeff s z
  have hz : z = ofCoeffs s a b := (ofCoeffs_coefficients s z).symm
  change z * conjugation s z = algebraMap R (CoverAlgebra s) (a ^ 2 - s * b ^ 2)
  calc
    z * conjugation s z = ofCoeffs s a b * conjugation s (ofCoeffs s a b) :=
      congrArg (fun w => w * conjugation s w) hz
    _ = ofCoeffs s (a * a + s * b * (-b)) (a * (-b) + b * a) := by
      rw [conjugation_ofCoeffs, ofCoeffs_mul]
    _ = algebraMap R (CoverAlgebra s) (a ^ 2 - s * b ^ 2) := by
      have hzero : a * (-b) + b * a = 0 := by ring
      rw [hzero, ofCoeffs_zero_right]
      congr 1
      ring

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.add_conjugation_eq_scalar
#print axioms KltDP.Geometry.QuadraticCover.mul_conjugation_eq_scalar
