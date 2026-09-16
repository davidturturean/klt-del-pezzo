/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten; Kim Morrison, Joël Riou (semilinear restriction adapter)
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Subpresheaf.Basic
import Mathlib.Algebra.Module.Submodule.Map

/-!
# Submodules of actual presheaves of modules

Reviewed port of `Mathlib/Algebra/Category/ModuleCat/Presheaf/Submodule.lean`
at commit `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0).
The source SHA256 is
`7bcd4b003af8ea63bb938688b63db7a69b3beccbe358b6ace9c45809325783e7`.

The original sectionwise submodules and restriction-stability condition are
unchanged. The pinned API calls type-valued subfunctors `Subpresheaf`, and
its `LinearMap.restrict` is not semilinear, so the restriction to submodules
is written explicitly. The missing `restrictₛₗ` adapter is also ported from
the same revision of `ModuleCat/Presheaf.lean`. The intersection proof uses
membership directly, avoiding the pinned `comap_iInf` lemma's unnecessary
surjectivity premise. No surjectivity of the ring restriction is assumed.
-/

noncomputable section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The actual restriction map, as a semilinear map over the ring restriction. -/
def restrictₛₗ (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.obj X →ₛₗ[(R.map f).hom] M.obj Y where
  toFun m := M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]
lemma restrictₛₗ_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (m : M.obj X) : M.restrictₛₗ f m = M.map f m := rfl

/-- A sectionwise submodule stable under the actual restriction maps. -/
structure Submodule (M : PresheafOfModules.{v} R) where
  obj (X : Cᵒᵖ) : _root_.Submodule (R.obj X) (M.obj X)
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ≤ (obj Y).comap (M.restrictₛₗ f)

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

lemma ext {N₁ N₂ : M.Submodule} (h : ∀ X, N₁.obj X = N₂.obj X) :
    N₁ = N₂ := by
  cases N₁; cases N₂; congr 1; ext X : 1; exact h X

lemma map_mem {X Y : Cᵒᵖ} (f : X ⟶ Y) {x : M.obj X} (hx : x ∈ N.obj X) :
    M.map f x ∈ N.obj Y := N.map f hx

/-- The restriction map on the actual submodules, bundled semilinearly. -/
def restrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    N.obj X →ₛₗ[(R.map f).hom] N.obj Y where
  toFun m := ⟨M.map f m.val, N.map_mem f m.prop⟩
  map_add' a b := Subtype.ext (map_add (M.map f).hom a.val b.val)
  map_smul' r m := Subtype.ext (M.map_smul f r m.val)

/-- The actual presheaf of modules defined by the stable submodules. -/
def toPresheafOfModules : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (N.obj X)
  map f := ModuleCat.semilinearMapAddEquiv _ _ _ (N.restrict f)
  map_id X := by
    refine ModuleCat.hom_ext
      -- Match the pinned pushforward construction's restriction-of-scalars instance diamond.
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun m => ?_))
    apply Subtype.ext
    exact congrArg (fun q : M.presheaf.obj X ⟶ M.presheaf.obj X => q m.val)
      (M.presheaf.map_id X)
  map_comp {X Y Z} f g := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun m => ?_))
    apply Subtype.ext
    exact congrArg (fun q : M.presheaf.obj X ⟶ M.presheaf.obj Z => q m.val)
      (M.presheaf.map_comp f g)

@[simp]
lemma toPresheafOfModules_obj (X : Cᵒᵖ) :
    N.toPresheafOfModules.obj X = ModuleCat.of (R.obj X) (N.obj X) := rfl

@[simp]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.obj X) :
    ((N.toPresheafOfModules).map f m).val = M.map f m.val := rfl

/-- The inclusion into the original presheaf of modules. -/
def ι : N.toPresheafOfModules ⟶ M :=
  homMk
    { app X := AddCommGrp.ofHom (N.obj X).subtype.toAddMonoidHom
      naturality := by intros; ext m; rfl }
    (by intros; rfl)

instance : Mono N.ι := mono_of_injective fun _ ↦ Subtype.val_injective

instance : PartialOrder M.Submodule :=
  PartialOrder.lift _ fun _ _ h ↦ ext (congrFun h)

lemma le_iff {N₁ N₂ : M.Submodule} : N₁ ≤ N₂ ↔ ∀ X, N₁.obj X ≤ N₂.obj X := Iff.rfl

/-- Inclusion between ordered submodules, on the actual sections. -/
def homOfLE {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) :
    N₁.toPresheafOfModules ⟶ N₂.toPresheafOfModules :=
  homMk
    { app X := AddCommGrp.ofHom (_root_.Submodule.inclusion (hle X)).toAddMonoidHom
      naturality := by intros; ext m; rfl }
    (by intros; rfl)

instance (N₁ N₂ : M.Submodule) (hle : N₁ ≤ N₂) : Mono (homOfLE hle) :=
  mono_of_injective fun _ ↦ _root_.Submodule.inclusion_injective (hle _)

@[simp]
lemma homOfLE_ι {N₁ N₂ : M.Submodule} (hle : N₁ ≤ N₂) : homOfLE hle ≫ N₂.ι = N₁.ι := rfl

/-- The underlying type-valued subpresheaf; the name follows the reviewed source. -/
def toSubfunctor : Subpresheaf (M.presheaf ⋙ CategoryTheory.forget AddCommGrp.{v}) where
  obj X := {r : M.obj X | r ∈ N.obj X}
  map := fun {_ _} f _ hr ↦ N.map_mem f hr

@[simp]
lemma mem_toSubfunctor_obj {X : Cᵒᵖ} (r : M.obj X) :
    r ∈ N.toSubfunctor.obj X ↔ r ∈ N.obj X := Iff.rfl

instance : CompleteLattice M.Submodule where
  sup F G :=
    { obj X := F.obj X ⊔ G.obj X
      map f := sup_le ((F.map f).trans (_root_.Submodule.comap_mono le_sup_left))
        ((G.map f).trans (_root_.Submodule.comap_mono le_sup_right)) }
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h₁ h₂ X := sup_le (h₁ X) (h₂ X)
  inf F G :=
    { obj X := F.obj X ⊓ G.obj X
      map f := le_inf (inf_le_left.trans (F.map f)) (inf_le_right.trans (G.map f)) }
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h₁ h₂ X := le_inf (h₁ X) (h₂ X)
  sSup s :=
    { obj X := ⨆ N ∈ s, N.obj X
      map f := iSup₂_le fun N hN ↦ (N.map f).trans
        (_root_.Submodule.comap_mono (le_iSup₂_of_le N hN le_rfl)) }
  le_sSup _ N hN _ := le_iSup₂_of_le N hN le_rfl
  sSup_le _ _ hb X := iSup₂_le fun N hN ↦ hb N hN X
  sInf s :=
    { obj X := ⨅ N ∈ s, N.obj X
      map {X Y} f := by
        intro m hm
        change (M.map f m : M.obj Y) ∈ ⨅ N ∈ s, N.obj Y
        simp only [_root_.Submodule.mem_iInf] at hm ⊢
        intro N hN
        exact N.map_mem f (hm N hN) }
  sInf_le _ N hN _ := iInf₂_le N hN
  le_sInf _ _ hb X := le_iInf₂ fun N hN ↦ hb N hN X
  bot.obj := ⊥
  bot.map _ := bot_le
  bot_le _ _ := bot_le
  top.obj := ⊤
  top.map _ := le_top
  le_top _ _ := le_top

@[simp]
lemma sup_obj (N₁ N₂ : M.Submodule) (X : Cᵒᵖ) :
    (N₁ ⊔ N₂).obj X = N₁.obj X ⊔ N₂.obj X := rfl

@[simp]
lemma inf_obj (N₁ N₂ : M.Submodule) (X : Cᵒᵖ) :
    (N₁ ⊓ N₂).obj X = N₁.obj X ⊓ N₂.obj X := rfl

@[simp]
lemma sSup_obj (s : Set M.Submodule) (X : Cᵒᵖ) :
    (sSup s).obj X = ⨆ N ∈ s, N.obj X := rfl

@[simp]
lemma sInf_obj (s : Set M.Submodule) (X : Cᵒᵖ) :
    (sInf s).obj X = ⨅ N ∈ s, N.obj X := rfl

@[simp]
lemma top_obj (X : Cᵒᵖ) : (⊤ : M.Submodule).obj X = ⊤ := rfl

@[simp]
lemma bot_obj (X : Cᵒᵖ) : (⊥ : M.Submodule).obj X = ⊥ := rfl

end Submodule

end PresheafOfModules
