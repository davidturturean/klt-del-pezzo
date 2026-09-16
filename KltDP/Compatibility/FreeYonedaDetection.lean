/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selective port of MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pullback.lean:853-867,1074-1095,
retaining AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Detecting natural isomorphisms on free representable module presheaves

The actual canonical free-representable presentation consists of coproducts
and a cokernel cofork. A natural transformation preserving these colimits
is invertible everywhere when it is invertible on free representables.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Colimit

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]

/-- Isomorphisms on a colimit diagram induce an isomorphism at its point. -/
lemma isIso_app_of_isColimit {F G : C₁ ⥤ C₂} (α : F ⟶ G) {J : Type u₃} [Category.{v₃} J]
    {K : J ⥤ C₁} {c : Cocone K}
    (h₁ : IsColimit (F.mapCocone c)) (h₂ : IsColimit (G.mapCocone c))
    [∀ j, IsIso (α.app (K.obj j))] : IsIso (α.app c.pt) := by
  let e : K ⋙ F ≅ K ⋙ G :=
    NatIso.ofComponents (fun j => asIso (α.app (K.obj j)))
      (fun {j j'} g => α.naturality (K.map g))
  let eColim := IsColimit.coconePointsIsoOfNatIso h₁ h₂ e
  have key : α.app c.pt = eColim.hom := by
    refine h₁.hom_ext (fun j => ?_)
    change F.map (c.ι.app j) ≫ α.app c.pt =
      F.map (c.ι.app j) ≫ eColim.hom
    exact (α.naturality (c.ι.app j)).trans
      (IsColimit.comp_coconePointsIsoOfNatIso_hom h₁ h₂ e j).symm
  rw [key]
  exact eColim.isIso_hom

end Colimit

section Presentation

variable {C : Type u} [SmallCategory C] {S : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The pinned free-representable presentation detects all components. -/
lemma isIso_app_of_isIso_app_freeYoneda {E : Type u₃} [Category.{v₃} E]
    {F₁ F₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat) ⥤ E} (α : F₁ ⟶ F₂)
    [PreservesColimitsOfSize.{u, u} F₁] [PreservesColimitsOfSize.{u, u} F₂]
    [PreservesColimitsOfShape WalkingParallelPair F₁]
    [PreservesColimitsOfShape WalkingParallelPair F₂]
    (hfree : ∀ X : C, IsIso (α.app
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj X))))
    (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (α.app M) := by
  have h₀ : ∀ (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)),
      IsIso (α.app N.freeYonedaCoproduct) := by
    intro N
    haveI : ∀ j, IsIso (α.app ((Discrete.functor
        (Elements.freeYoneda (M := N))).obj j)) := fun j => hfree _
    exact isIso_app_of_isColimit α
      (isColimitOfPreserves F₁ (colimit.isColimit _))
      (isColimitOfPreserves F₂ (colimit.isColimit _))
  haveI : ∀ j, IsIso (α.app ((parallelPair M.toFreeYonedaCoproduct 0).obj j)) := by
    rintro (_ | _) <;> exact h₀ _
  exact isIso_app_of_isColimit α
    (isColimitOfPreserves F₁ M.isColimitFreeYonedaCoproductsCokernelCofork)
    (isColimitOfPreserves F₂ M.isColimitFreeYonedaCoproductsCokernelCofork)

end Presentation

end PresheafOfModules
