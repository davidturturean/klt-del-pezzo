import KltDP.Geometry.InvertibleSheafSectionPowers

/-!
# Literal transition coefficients of actual power frames

The original frame generator tensors to the inverse of the constructed
power frame. Thus a change between two original frames becomes the literal
power of its coefficient. These are actual module-sheaf maps and section
ring elements on the scheme in question, including any actual overlap
scheme. No transition formula is assumed and no twisted sections are glued
in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.InvertibleSheafPowerFrameTransition

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance frameTransitionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- The compatible family corresponding to the original inverse frame. -/
def frameGenerator (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :
    L.obj.sections := L.obj.unitHomEquiv e.inv

/-- Its coefficient in that same original frame is the literal unit. -/
theorem frameGenerator_coefficient
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) :
    frameCoefficient L e (frameGenerator L e) = 1 := by
  change e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    (1 : Γ(X, ⊤))
  exact congrArg (fun g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf =>
    g.val.app (op ⊤) (1 : Γ(X, ⊤))) e.inv_hom_id

/-- Tensoring the actual frame generator gives exactly the inverse of
the induced power frame. -/
theorem powerSectionHom_frameGenerator
    (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    powerSectionHom L (frameGenerator L e) n = (powerFrame L e n).inv := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (schemeStructureTensorRightIso
        (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (powerSectionHom L (frameGenerator L e) n ⊗
          L.obj.unitHomEquiv.symm (frameGenerator L e)) =
      (schemeStructureTensorRightIso
        (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
        ((powerFrame L e n).inv ⊗ e.inv)
    rw [ih]
    simp only [frameGenerator, Equiv.symm_apply_apply]

/-- The original transition between the induced power frames is
multiplication by the literal power of the original frame-change coefficient. -/
theorem powerFrame_transition
    (e d : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    (powerFrame L e n).inv ≫ (powerFrame L d n).hom =
      schemeScalarEnd (frameCoefficient L d (frameGenerator L e) ^ n) := by
  rw [← powerSectionHom_frameGenerator L e n]
  exact powerSectionHom_frame L d (frameGenerator L e) n

/-- The same actual transition evaluated on the original unit section
has exactly the expected coefficient in the original section ring. -/
theorem powerFrame_transition_coefficient
    (e d : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) (n : ℕ) :
    (powerFrame L d n).hom.val.app (op ⊤)
        ((powerFrame L e n).inv.val.app (op ⊤) (1 : Γ(X, ⊤))) =
      frameCoefficient L d (frameGenerator L e) ^ n := by
  have h := congrArg (fun g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf =>
    g.val.app (op ⊤) (1 : Γ(X, ⊤))) (powerFrame_transition L e d n)
  change (powerFrame L d n).hom.val.app (op ⊤)
      ((powerFrame L e n).inv.val.app (op ⊤) (1 : Γ(X, ⊤))) =
    (schemeScalarEnd (frameCoefficient L d (frameGenerator L e) ^ n)).val.app
      (op ⊤) (1 : Γ(X, ⊤)) at h
  exact h.trans (by rw [schemeScalarEnd_appTop, one_mul])

end KltDP.Geometry.InvertibleSheafPowerFrameTransition
