import KltDP.Geometry.AffineQuadraticCover
import KltDP.Compatibility.AdjoinRootStandardEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The actual quadratic cover is étale where two and the branch coefficient are units

The equation in the original quotient makes its generator invertible when
the branch coefficient is invertible. Thus the evaluated derivative 2t is
invertible when 2 is a unit. The actual singleton polynomial presentation
is then standard smooth of relative dimension zero, the pinned definition
used by scheme étaleness. No formal-to-geometric smoothness equivalence is
assumed: that equivalence is still a TODO in the pinned Smooth.lean.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R]

/-- The actual generator is a unit whenever its square, the branch coefficient, is a unit. -/
theorem root_isUnit (s : R) (hs : IsUnit s) : IsUnit (root s) := by
  have h := hs.map (algebraMap R (CoverAlgebra s))
  rw [← root_sq, pow_two] at h
  exact isUnit_of_mul_isUnit_left h

/-- The evaluated derivative of the original quotient equation is exactly 2t. -/
theorem aeval_derivative_polynomial (s : R) :
    aeval (root s) (polynomial s).derivative =
      algebraMap R (CoverAlgebra s) 2 * root s := by
  simp only [polynomial, map_sub, derivative_X_sq, derivative_C, sub_zero,
    map_mul, aeval_C, aeval_X]

/-- Derivative invertibility is derived from the two original base-ring unit hypotheses. -/
theorem aeval_derivative_isUnit (s : R) (h2 : IsUnit (2 : R)) (hs : IsUnit s) :
    IsUnit (aeval (root s) (polynomial s).derivative) := by
  rw [aeval_derivative_polynomial]
  exact (h2.map (algebraMap R (CoverAlgebra s))).mul (root_isUnit s hs)

/-- The actual monic quotient has a standard-smooth presentation of relative dimension zero. -/
theorem isStandardSmoothOfRelativeDimension_zero (s : R)
    (h2 : IsUnit (2 : R)) (hs : IsUnit s) :
    Algebra.IsStandardSmoothOfRelativeDimension 0 R (CoverAlgebra s) :=
  KltDP.Compatibility.AdjoinRootStandardEtale.adjoinRoot_isStandardSmoothOfRelativeDimension_zero
    (polynomial s) (aeval_derivative_isUnit s h2 hs)

/-- The actual structural morphism of the quadratic spectrum is étale. -/
theorem toBase_isEtale (s : R) (h2 : IsUnit (2 : R)) (hs : IsUnit s) :
    IsEtale (toBase s) := by
  have hAlg := isStandardSmoothOfRelativeDimension_zero s h2 hs
  have hMap : RingHom.IsStandardSmoothOfRelativeDimension 0
      (algebraMap R (CoverAlgebra s)) := by
    have he : (algebraMap R (CoverAlgebra s)).toAlgebra =
        (inferInstance : Algebra R (CoverAlgebra s)) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [RingHom.IsStandardSmoothOfRelativeDimension, he]
    exact hAlg
  apply (HasRingHomProperty.Spec_iff (P := @IsEtale)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hMap

end KltDP.Geometry.QuadraticCover
