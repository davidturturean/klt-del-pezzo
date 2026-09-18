import KltDP.Geometry.CartierSectionProducts
import KltDP.Geometry.BaseFieldCohomology

/-!
# Original base-field linearity of Cartier rational values

The scalar map is the actual structure morphism on global sections,
followed by its original generic-point germ. The existing fractional
submodule and linear rational-section comparison prove linearity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.SectionMonomialGrowth

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The existing rational-value map as a linear map over the original
ring of global regular functions. -/
def rationalValueGlobalLinearMap (D : CartierDivisor X) :
    sections (cartierDivisorModule X D) →ₗ[Γ(X, ⊤)] X.functionField :=
  (rationalFunctionModuleSectionsEquiv X ⊤).toLinearMap.comp
    (cartierSectionSubmodule X D ⊤).subtype

section OverField

variable {X} {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- The original structure morphism followed by the original generic germ. -/
def functionFieldScalar : k →+* X.functionField :=
  (algebraMap Γ(X, ⊤) X.functionField).comp (baseFieldToGlobalSections f)

abbrev functionFieldAlgebra : Algebra k X.functionField :=
  (functionFieldScalar f).toAlgebra

/-- Rational values preserve exactly the original base-field section action. -/
theorem rationalValue_base_smul (D : CartierDivisor X) (a : k)
    (s : sections (cartierDivisorModule X D)) :
    letI := baseSectionsModule f (cartierDivisorModule X D)
    cartierGlobalSectionRationalValue X D (a • s) =
      functionFieldScalar f a * cartierGlobalSectionRationalValue X D s := by
  letI := baseSectionsModule f (cartierDivisorModule X D)
  change rationalFunctionModuleSectionsEquiv X ⊤
      ((baseFieldToGlobalSections f a) • s.val) =
    functionFieldScalar f a * rationalFunctionModuleSectionsEquiv X ⊤ s.val
  rw [map_smul, Algebra.smul_def]
  rfl

/-- The actual original rational-value map with the original k-linear action. -/
def rationalValueBaseLinearMap (D : CartierDivisor X) :
    letI := baseSectionsModule f (cartierDivisorModule X D)
    letI := functionFieldAlgebra f
    sections (cartierDivisorModule X D) →ₗ[k] X.functionField := by
  letI := baseSectionsModule f (cartierDivisorModule X D)
  letI := functionFieldAlgebra f
  exact {
    toFun := cartierGlobalSectionRationalValue X D
    map_add' := (rationalValueGlobalLinearMap X D).map_add
    map_smul' := fun a s => rationalValue_base_smul f D a s }

end OverField

end KltDP.Geometry.SectionMonomialGrowth
