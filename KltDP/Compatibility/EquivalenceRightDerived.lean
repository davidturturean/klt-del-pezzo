import KltDP.Compatibility.EquivalenceInjectiveResolution
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Right-derived functors and an additive equivalence

The comparison is computed on an original injective resolution and its image
under the equivalence. Naturality uses the image of the original descent of
each coefficient map.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
  {A : Type u₃} [Category.{v₃} A] [Abelian A]

namespace InjectiveResolution

variable (e : C ≌ D) [e.functor.Additive] (F : D ⥤ A) [F.Additive] (n : ℕ)

/-- The comparison computed on the original resolution and its image. -/
def equivalenceRightDerivedIso {X : C} (R : InjectiveResolution X) :
    (F.rightDerived n).obj (e.functor.obj X) ≅
      ((e.functor ⋙ F).rightDerived n).obj X :=
  (mapEquivalence e R).isoRightDerivedObj F n ≪≫
    (R.isoRightDerivedObj (e.functor ⋙ F) n).symm

/-- The chosen-resolution comparison commutes with each original coefficient map. -/
lemma equivalenceRightDerivedIso_hom_naturality {X Y : C}
    (R : InjectiveResolution X) (R' : InjectiveResolution Y) (f : X ⟶ Y) :
    (F.rightDerived n).map (e.functor.map f) ≫
        (equivalenceRightDerivedIso e F n R').hom =
      (equivalenceRightDerivedIso e F n R).hom ≫
        ((e.functor ⋙ F).rightDerived n).map f := by
  have h₁ := isoRightDerivedObj_hom_naturality (e.functor.map f)
    (mapEquivalence e R) (mapEquivalence e R')
    (mapEquivalenceHom e R R' (desc f R' R))
    (mapEquivalence_desc_commutes_zero e R R' f) F n
  have h₂ := isoRightDerivedObj_inv_naturality f R R' (desc f R' R)
    (desc_commutes_zero f R' R) (e.functor ⋙ F) n
  simp only [equivalenceRightDerivedIso, Iso.trans_hom, Iso.symm_hom]
  erw [← assoc, h₁, assoc, ← h₂, ← assoc]

end InjectiveResolution

namespace Equivalence

variable (e : C ≌ D) [e.functor.Additive] (F : D ⥤ A) [F.Additive] (n : ℕ)

/-- Precomposition by an additive equivalence commutes with right-derived functors. -/
def rightDerivedIso :
    e.functor ⋙ F.rightDerived n ≅ (e.functor ⋙ F).rightDerived n :=
  NatIso.ofComponents
    (fun X => InjectiveResolution.equivalenceRightDerivedIso e F n (injectiveResolution X))
    (fun {X Y} f => InjectiveResolution.equivalenceRightDerivedIso_hom_naturality
      e F n (injectiveResolution X) (injectiveResolution Y) f)

@[simp]
lemma rightDerivedIso_hom_app (X : C) :
    (rightDerivedIso e F n).hom.app X =
      ((InjectiveResolution.mapEquivalence e (injectiveResolution X)).isoRightDerivedObj F n).hom ≫
        ((injectiveResolution X).isoRightDerivedObj (e.functor ⋙ F) n).inv := rfl

@[simp]
lemma rightDerivedIso_inv_app (X : C) :
    (rightDerivedIso e F n).inv.app X =
      ((injectiveResolution X).isoRightDerivedObj (e.functor ⋙ F) n).hom ≫
        ((InjectiveResolution.mapEquivalence e (injectiveResolution X)).isoRightDerivedObj F n).inv :=
  rfl

end Equivalence

end CategoryTheory
