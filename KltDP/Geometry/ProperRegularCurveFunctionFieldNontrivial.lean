import KltDP.Geometry.RegularProperCurveFieldIso
import KltDP.Geometry.SpecFieldFunctionFieldIntrinsic
import KltDP.Geometry.PrimeCurveCodimension

/-! A regular proper integral curve of dimension one cannot have the
ground field as its original function field with its intrinsic scalars.
The proved curve extension theorem would identify it with Spec k. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperRegularCurveFunctionFieldNontrivial

open IntrinsicNodal

variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]

theorem not_nonempty_equiv
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hC : ∀ x : C, RegularPoint C x)
    (hdim : topologicalKrullDim C = 1) :
    letI := stalkAlgebra c (genericPoint C)
    ¬ Nonempty (C.functionField ≃ₐ[k] k) := by
  letI := stalkAlgebra c (genericPoint C)
  letI := stalkAlgebra (𝟙 (Spec (CommRingCat.of k)))
    (genericPoint (Spec (CommRingCat.of k)))
  rintro ⟨e⟩
  have h0 : ∀ x : Spec (CommRingCat.of k),
      RegularPoint (Spec (CommRingCat.of k)) x := by
    intro x
    have hx : x = genericPoint (Spec (CommRingCat.of k)) :=
      Subsingleton.elim _ _
    rw [hx]
    exact regularPoint_genericPoint _
  have d0 : topologicalKrullDim (Spec (CommRingCat.of k)) ≤ 1 :=
    (topologicalKrullDim_nonpos_of_subsingleton
      (Spec (CommRingCat.of k))).trans (by norm_num)
  obtain ⟨i, _, _⟩ := RegularProperCurveFieldIso.exists_iso
    hC h0 hdim.le d0 c (𝟙 (Spec (CommRingCat.of k)))
    ((SpecFieldFunctionFieldIntrinsic.equiv k).trans e.symm)
  letI : Subsingleton C := ⟨fun x y =>
    i.schemeIsoToHomeo.injective (Subsingleton.elim _ _)⟩
  have hnonpos := topologicalKrullDim_nonpos_of_subsingleton C
  rw [hdim] at hnonpos
  have hpositive : (0 : WithBot ℕ∞) < 1 :=
    WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 1)
  exact hpositive.not_le hnonpos

#print axioms not_nonempty_equiv

end KltDP.Geometry.ProperRegularCurveFunctionFieldNontrivial
