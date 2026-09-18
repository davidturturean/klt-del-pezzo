import KltDP.Geometry.BirationalFunctionField

/-! A surjective original generic-stalk map is birational once the
original generic-point equality is known: the associated field map is
also injective. No whole-scheme isomorphism is inferred. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

theorem isBirationalScheme_of_generic_stalkMap_surjective
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (f : C ⟶ D) [GenericPointPreserving f]
    (h : Function.Surjective (f.stalkMap (genericPoint C)).hom) :
    IsBirationalScheme f := by
  letI := BirationalFunctionField.genericSpecialization_isIso f
  have hs : Function.Surjective (functionFieldMap f).hom := by
    unfold functionFieldMap
    exact h.comp
      (asIso (D.presheaf.stalkSpecializes (base_genericPoint_specializes f))).commRingCatIsoToRingEquiv.surjective
  letI : IsIso (functionFieldMap f) :=
    (ConcreteCategory.isIso_iff_bijective (functionFieldMap f)).mpr
      ⟨(functionFieldMap f).hom.injective, hs⟩
  exact (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso f).mpr
    inferInstance

end KltDP.Geometry

#check @KltDP.Geometry.isBirationalScheme_of_generic_stalkMap_surjective
#print axioms KltDP.Geometry.isBirationalScheme_of_generic_stalkMap_surjective
