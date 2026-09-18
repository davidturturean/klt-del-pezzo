import KltDP.Geometry.NonconstantProperCurveSurjective
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.ProjectiveSpaceIntegral
import KltDP.Geometry.LocallyOfFiniteTypeNoetherian
import KltDP.Geometry.BirationalFunctionFieldStalkAlgebra

/-! An actual over-k map from the original projective line to an original
proper integral curve is constant on points or surjective and dominant.
In the latter case its literal generic stalk map is an injective algebra
homomorphism for the original intrinsic ground actions. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProjectiveLineCurveMapDichotomy

open IntrinsicNodal

variable {k : Type u} [Field k]

local instance line_integral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- Regularity of the target is not needed for this dichotomy. All
properness, dominance, generic-point and field-injectivity data in its
second branch are derived for the original map. -/
theorem constant_or_dominant_surjective
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hdim : topologicalKrullDim C ≤ 1)
    (f : projectiveSpace k 1 ⟶ C)
    (hf : f ≫ c = projectiveSpaceToSpec k 1) :
    (∃ y : C, ∀ x : projectiveSpace k 1, f.base x = y) ∨
      (IsProper f ∧ IsDominant f ∧ Function.Surjective f.base ∧
        ∃ hg : GenericPointPreserving f,
          letI := hg
          letI := stalkAlgebra c (genericPoint C)
          letI := stalkAlgebra (projectiveSpaceToSpec k 1)
            (genericPoint (projectiveSpace k 1))
          ∃ φ : C.functionField →ₐ[k] (projectiveSpace k 1).functionField,
            Function.Injective φ ∧ φ.toRingHom = (functionFieldMap f).hom) := by
  classical
  by_cases hconstant : ∃ y : C, ∀ x : projectiveSpace k 1, f.base x = y
  · exact Or.inl hconstant
  · letI : NoetherianSpace C :=
      noetherianSpace_of_locallyOfFiniteType_quasiCompact_spec c
    letI : IsProper (f ≫ c) := by rw [hf]; infer_instance
    letI : IsProper f := IsProper.of_comp_of_isSeparated f c
    obtain ⟨hgp, hdom, hsurj⟩ :=
      NonconstantProperCurveSurjective.surjective_of_nonconstant_base f hdim hconstant
    refine Or.inr ⟨inferInstance, hdom, hsurj, hgp, ?_⟩
    letI : GenericPointPreserving f := hgp
    letI := stalkAlgebra c (genericPoint C)
    letI := stalkAlgebra (projectiveSpaceToSpec k 1)
      (genericPoint (projectiveSpace k 1))
    let φ := BirationalFunctionFieldStalkAlgebra.hom (projectiveSpaceToSpec k 1) c f hf
    exact ⟨φ, φ.toRingHom.injective, rfl⟩

#print axioms constant_or_dominant_surjective

end KltDP.Geometry.ProjectiveLineCurveMapDichotomy
