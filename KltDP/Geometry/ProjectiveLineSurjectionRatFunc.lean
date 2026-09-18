import KltDP.Geometry.ProjectiveLineFunctionField
import KltDP.Geometry.BirationalFunctionFieldStalkAlgebra

/-! The original function-field embedding induced by an actual surjection
from the original projective line, with the intrinsic base-field actions. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProjectiveLineSurjectionRatFunc

open IntrinsicNodal

theorem exists_embedding
    {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k))
    (f : projectiveSpace k 1 ⟶ C)
    (hf : f ≫ c = projectiveSpaceToSpec k 1)
    (hsurj : Function.Surjective f.base) :
    letI := stalkAlgebra c (genericPoint C)
    ∃ φ : C.functionField →ₐ[k] RatFunc k, Function.Injective φ := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : GenericPointPreserving f := ⟨by
    apply ((genericPoint_spec C).eq _).symm
    convert (genericPoint_spec (projectiveSpace k 1)).image
      (show Continuous f.base by fun_prop) using 1
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj, closure_univ]⟩
  letI := stalkAlgebra c (genericPoint C)
  letI := stalkAlgebra (projectiveSpaceToSpec k 1)
    (genericPoint (projectiveSpace k 1))
  let φ := (ProjectiveLineFunctionField.equiv k).toAlgHom.comp
    (BirationalFunctionFieldStalkAlgebra.hom (projectiveSpaceToSpec k 1) c f hf)
  exact ⟨φ, φ.toRingHom.injective⟩

end KltDP.Geometry.ProjectiveLineSurjectionRatFunc

#check @KltDP.Geometry.ProjectiveLineSurjectionRatFunc.exists_embedding
#print axioms KltDP.Geometry.ProjectiveLineSurjectionRatFunc.exists_embedding
