import KltDP.Geometry.IntegralNumericalClassGroup
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite integral numerical generation implies rational finite dimension

The finite-generation premise concerns the actual integral Picard quotient.
Scalar extension is finite by Mathlib, and the proved canonical numerical
tensor equivalence transports that finiteness to the original rational
numerical quotient. No freeness or Hodge premise is needed for this implication.
-/

noncomputable section

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Finite generation of the original integral numerical group proves finite
dimensionality of the existing rational numerical class space. -/
theorem numericalClassGroup_finite_of_integralNum_finite
    [Module.Finite ℤ X.IntegralNumericalClassGroup] :
    Module.Finite ℚ X.NumericalClassGroup :=
  Module.Finite.equiv X.integralNumericalTensorRationalEquiv

/-- The same conclusion in the vector-space API, for the same original quotient. -/
theorem numericalClassGroup_finiteDimensional_of_integralNum_finite
    [Module.Finite ℤ X.IntegralNumericalClassGroup] :
    FiniteDimensional ℚ X.NumericalClassGroup :=
  X.numericalClassGroup_finite_of_integralNum_finite

end KltDP.Geometry.NormalProjectiveSurface
