import KltDP.Literature.Hartshorne.IntegralNumericalGroup

/-!
# Finite dimensionality of the original numerical divisor space

The complete integral Num source is applied to the original regular surface.
The proved canonical tensor equivalence then supplies finite dimensionality
of the existing rational numerical quotient. No finite-generation, Hodge or
rank hypothesis remains in these consumers.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.SurfaceNumericalFinitenessProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- Both source conclusions for the original integral numerical quotient. -/
theorem integralNum_free_and_finite :
    Module.Free ℤ X.IntegralNumericalClassGroup ∧
      Module.Finite ℤ X.IntegralNumericalClassGroup :=
  SurfaceNumericalFinitenessSource.integralNum_free_and_finite X hregular
    KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal

/-- Freeness concerns the actual integral quotient, not the rational space. -/
theorem integralNum_free : Module.Free ℤ X.IntegralNumericalClassGroup :=
  (integralNum_free_and_finite X hregular).1

/-- Finite generation concerns the actual integral quotient. -/
theorem integralNum_finite : Module.Finite ℤ X.IntegralNumericalClassGroup :=
  (integralNum_free_and_finite X hregular).2

/-- The original rational numerical classes form a finite module. -/
theorem numericalClassGroup_finite : Module.Finite ℚ X.NumericalClassGroup :=
  SurfaceNumericalFinitenessSource.numericalClassGroup_finite X hregular
    KltDP.Literature.Hartshorne.integral_numerical_group_free_finite_literal

/-- The existing numerical-space finite-dimensionality obligation is supplied. -/
theorem numericalSpaceFiniteDimensional : X.NumericalSpaceFiniteDimensional :=
  numericalClassGroup_finite X hregular

end KltDP.Geometry.SurfaceNumericalFinitenessProved
