import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.Ring.Basic

/-! Reflect an isomorphism of the original spectrum map before specializing
its ring homomorphism to a tensor-algebra scalar map. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.AffineSpecMapReflection

/-- Fully faithful Spec reflects the original bundled ring map. -/
theorem bijective_of_isIso_spec {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsIso (Spec.map φ)] : Function.Bijective φ.hom := by
  letI : IsIso (Scheme.Spec.map φ.op) :=
    show IsIso (Spec.map φ) from inferInstance
  letI : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  letI : IsIso φ := isIso_of_op φ
  exact (ConcreteCategory.isIso_iff_bijective φ).mp inferInstance

#check KltDP.Geometry.AffineSpecMapReflection.bijective_of_isIso_spec
#print axioms KltDP.Geometry.AffineSpecMapReflection.bijective_of_isIso_spec

end KltDP.Geometry.AffineSpecMapReflection
