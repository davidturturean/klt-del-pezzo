import KltDP.Geometry.BirationalFunctionField
import KltDP.Geometry.ProperGenericPointSurjective
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.AffineFiberScalarRank

/-!
# Original data for degree transport along a birational curve map

Properness and the original generic-point map exclude a constant map onto
a curve. Birationality identifies the original function-field map with an
isomorphism, so the degree of that original field extension is one. These
ordinary results do not assert any formula for the degree of a line sheaf.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperBirationalCurveDegree

/-- A proper original birational map onto a one-dimensional integral
scheme cannot be constant on its original points. -/
theorem not_constant_of_birational
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (f : C ⟶ D) [IsProper f] (hbir : IsBirationalScheme f)
    (hdim : topologicalKrullDim D = 1) :
    ¬ ∃ y : D, ∀ x : C, f.base x = y := by
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  letI : Surjective f := surjective_of_proper_genericPointPreserving f
  rintro ⟨y, hy⟩
  letI : Subsingleton D := ⟨fun a b => by
    obtain ⟨a', rfl⟩ := f.surjective a
    obtain ⟨b', rfl⟩ := f.surjective b
    exact (hy a').trans (hy b').symm⟩
  have hle := topologicalKrullDim_nonpos_of_subsingleton D
  rw [hdim] at hle
  have hpos : (0 : WithBot ℕ∞) < 1 :=
    WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)
  exact hpos.not_le hle

/-- The scalar action is induced by the original function-field map.
Its finrank is one because that same map is an isomorphism. -/
theorem functionField_finrank_eq_one
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (f : C ⟶ D) [GenericPointPreserving f] (hbir : IsBirationalScheme f) :
    letI : Algebra D.functionField C.functionField :=
      (functionFieldMap f).hom.toAlgebra
    Module.finrank D.functionField C.functionField = 1 := by
  letI : Algebra D.functionField C.functionField :=
    (functionFieldMap f).hom.toAlgebra
  letI : IsIso (functionFieldMap f) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso f).mp hbir
  have hbij : Function.Bijective (algebraMap D.functionField C.functionField) := by
    change Function.Bijective (functionFieldMap f).hom
    exact (ConcreteCategory.isIso_iff_bijective (functionFieldMap f)).mp inferInstance
  exact AffineFiberScalarRank.finrank_eq_one_of_algebraMap_bijective
    D.functionField C.functionField hbij

end KltDP.Geometry.ProperBirationalCurveDegree

#check @KltDP.Geometry.ProperBirationalCurveDegree.not_constant_of_birational
#check @KltDP.Geometry.ProperBirationalCurveDegree.functionField_finrank_eq_one
#print axioms KltDP.Geometry.ProperBirationalCurveDegree.not_constant_of_birational
#print axioms KltDP.Geometry.ProperBirationalCurveDegree.functionField_finrank_eq_one
