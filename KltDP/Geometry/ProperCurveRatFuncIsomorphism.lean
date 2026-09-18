import KltDP.Geometry.ProperCurveRatFuncFieldRange
import KltDP.Geometry.ProjectiveLineFunctionField
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.RegularLocalDimensionTwo
import KltDP.Compatibility.LurothTheorem

/-! An actual embedding of the intrinsic function field of a regular
proper integral curve into RatFunc k gives an actual over-k isomorphism
with the original projective line. Nontriviality of the image, the
projective-line regularity, and the scheme isomorphism are all derived. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperCurveRatFuncIsomorphism

open IntrinsicNodal

variable {k : Type u} [Field k]

local instance line_integral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

private theorem line_dim_le_one :
    topologicalKrullDim (projectiveSpace k 1) ≤ 1 := by
  rw [projectiveSpace_topologicalKrullDim]
  simp

private theorem line_regular (x : projectiveSpace k 1) :
    RegularPoint (projectiveSpace k 1) x := by
  letI : IsLocallyNoetherian (projectiveSpace k 1) :=
    projectiveSpace_isLocallyNoetherian k 1
  letI : IsNoetherianRing ((projectiveSpace k 1).presheaf.stalk x) :=
    isNoetherianRing_stalk_of_isLocallyNoetherian _ x
  exact regularPoint_of_normal_of_ringKrullDim_le_one
    (projectiveSpace k 1) (projectiveSpace_isNormalScheme k 1) x
    ((ringKrullDim_stalk_le_topologicalKrullDim _ x).trans line_dim_le_one)

theorem exists_iso_of_embedding
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hC : ∀ x : C, RegularPoint C x)
    (hdim : topologicalKrullDim C = 1) :
    letI := stalkAlgebra c (genericPoint C)
    ∀ φ : C.functionField →ₐ[k] RatFunc k,
      ∃ i : C ≅ projectiveSpace k 1,
        i.hom ≫ projectiveSpaceToSpec k 1 = c := by
  letI := stalkAlgebra c (genericPoint C)
  intro φ
  letI := stalkAlgebra (projectiveSpaceToSpec k 1)
    (genericPoint (projectiveSpace k 1))
  let e : C.functionField ≃ₐ[k] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  let eL : RatFunc k ≃ₐ[k] φ.fieldRange := RatFunc.Luroth.algEquiv
    (ProperCurveRatFuncFieldRange.fieldRange_ne_bot c hC hdim φ)
  obtain ⟨i, hi, _⟩ := RegularProperCurveFieldIso.exists_iso
    hC line_regular hdim.le line_dim_le_one c (projectiveSpaceToSpec k 1)
    ((ProjectiveLineFunctionField.equiv k).trans (eL.trans e.symm))
  exact ⟨i, hi⟩

#print axioms exists_iso_of_embedding

end KltDP.Geometry.ProperCurveRatFuncIsomorphism
