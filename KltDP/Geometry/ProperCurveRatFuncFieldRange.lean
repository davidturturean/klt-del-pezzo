import KltDP.Geometry.ProperRegularCurveFunctionFieldNontrivial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.RatFunc.Basic

/-! The actual function-field image of an integral regular proper curve
of dimension one in RatFunc k is a nonbottom intermediate field. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ProperCurveRatFuncFieldRange

open IntrinsicNodal

variable {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]

theorem fieldRange_ne_bot
    (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c]
    (hC : ∀ x : C, RegularPoint C x)
    (hdim : topologicalKrullDim C = 1) :
    letI := stalkAlgebra c (genericPoint C)
    ∀ φ : C.functionField →ₐ[k] RatFunc k, φ.fieldRange ≠ ⊥ := by
  letI := stalkAlgebra c (genericPoint C)
  intro φ hbot
  let e : C.functionField ≃ₐ[k] φ.fieldRange :=
    AlgEquiv.ofInjectiveField φ
  exact ProperRegularCurveFunctionFieldNontrivial.not_nonempty_equiv
    c hC hdim ⟨(e.trans (IntermediateField.equivOfEq hbot)).trans
      (IntermediateField.botEquiv k (RatFunc k))⟩

#print axioms fieldRange_ne_bot

end KltDP.Geometry.ProperCurveRatFuncFieldRange
