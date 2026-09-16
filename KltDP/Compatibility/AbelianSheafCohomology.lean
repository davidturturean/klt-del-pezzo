/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Joël Riou

Adapted from official Mathlib commit
5aedf732b6987e8c26ab3c9ebc855314f82b045f,
CategoryTheory/Sites/SheafCohomology/Basic.lean, lines 94–169,
and Algebra/Category/Grp/ForgetCorepresentable.lean, lines 35–37 and 84–93.
The pinned Mathlib definition of Sheaf.H is retained. The ULift-integer
equivalence uses the pin's existing AddMonoidHom.fromULiftIntEquiv.
-/
import KltDP.Compatibility.AbelianGroupGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Functoriality and degree-zero evaluation of abelian sheaf cohomology

The cohomology groups below are the pin's Ext groups from the constant
integer sheaf. Postcomposition induces their coefficient maps, and the
constant-sheaf adjunction identifies degree zero with actual sections at
a terminal object. All universe and sheafification hypotheses are explicit.
-/

noncomputable section

universe w' w v u

open CategoryTheory

namespace AddCommGrp

/-- Evaluation at the lifted integer `1` identifies morphisms from the
lifted integers with elements of an abelian group. -/
def uliftZMultiplesAddEquiv (G : AddCommGrp.{w}) :
    (AddCommGrp.of (ULift.{w} ℤ) ⟶ G) ≃+ G :=
  AddCommGrp.homAddEquiv.trans
    (AddEquiv.mk' (AddMonoidHom.fromULiftIntEquiv G) (fun _ _ => rfl))

lemma uliftZMultiplesAddEquiv_apply (G : AddCommGrp.{w})
    (f : AddCommGrp.of (ULift.{w} ℤ) ⟶ G) :
    uliftZMultiplesAddEquiv G f = f (ULift.up 1) := rfl

end AddCommGrp

namespace CategoryTheory.Sheaf

open Abelian Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrp.{w}]

/-- The constant abelian sheaf functor is additive because its presheaf
functor is pointwise additive and sheafification is additive. -/
private instance constantSheaf_additive : (constantSheaf J AddCommGrp.{w}).Additive := by
  letI : (Functor.const Cᵒᵖ : AddCommGrp.{w} ⥤ Cᵒᵖ ⥤ AddCommGrp.{w}).Additive := by
    constructor
    intro X Y f g
    ext U
    rfl
  change ((Functor.const Cᵒᵖ : AddCommGrp.{w} ⥤ Cᵒᵖ ⥤ AddCommGrp.{w}) ⋙
    presheafToSheaf J AddCommGrp.{w}).Additive
  infer_instance

variable [HasExt.{w'} (Sheaf J AddCommGrp.{w})]

/-- Degree-zero cohomology is the group of sections at a terminal object. -/
def H.equiv₀ (F : Sheaf J AddCommGrp.{w}) {T : C} (hT : Limits.IsTerminal T) :
    H F 0 ≃+ F.val.obj (op T) :=
  AddEquiv.trans Ext.addEquiv₀ <|
    AddEquiv.trans ((constantSheafAdj J AddCommGrp.{w} hT).homAddEquiv
      (AddCommGrp.of (ULift.{w} ℤ)) F)
      (AddCommGrp.uliftZMultiplesAddEquiv _)

variable {F G : Sheaf J AddCommGrp.{w}}

/-- A coefficient morphism acts on cohomology by postcomposition in Ext. -/
def H.map (f : F ⟶ G) (n : ℕ) : H F n →+ H G n :=
  (Ext.mk₀ f).postcomp
    ((constantSheaf J AddCommGrp.{w}).obj (AddCommGrp.of (ULift.{w} ℤ))) (add_zero n)

lemma H.addEquiv₀_map (f : F ⟶ G) (x : H F 0) :
    Ext.addEquiv₀ (H.map f 0 x) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective _ G).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  rfl

/-- The degree-zero evaluation equivalence is natural in the coefficient sheaf. -/
theorem H.equiv₀_naturality {T : C} (hT : Limits.IsTerminal T)
    (f : F ⟶ G) (x : H F 0) :
    f.val.app (op T) (H.equiv₀ F hT x) = H.equiv₀ G hT (H.map f 0 x) := by
  have hExt := congrArg
    (fun z : (constantSheaf J AddCommGrp.{w}).obj
        (AddCommGrp.of (ULift.{w} ℤ)) ⟶ G =>
      ((constantSheafAdj J AddCommGrp.{w} hT).homEquiv
        (AddCommGrp.of (ULift.{w} ℤ)) G z) (ULift.up 1))
    (H.addEquiv₀_map f x)
  have hAdj := congrArg
    (fun z : AddCommGrp.of (ULift.{w} ℤ) ⟶ G.val.obj (op T) =>
      z (ULift.up 1))
    ((constantSheafAdj J AddCommGrp.{w} hT).homEquiv_naturality_right
      (Ext.addEquiv₀ x) f)
  exact hAdj.symm.trans hExt.symm

theorem H.equiv₀_symm_naturality {T : C} (hT : Limits.IsTerminal T)
    (f : F ⟶ G) (x : F.val.obj (op T)) :
    H.map f 0 ((H.equiv₀ F hT).symm x) =
      (H.equiv₀ G hT).symm (f.val.app (op T) x) := by
  apply (H.equiv₀ G hT).injective
  rw [← H.equiv₀_naturality hT f]
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

lemma H.map_apply (f : F ⟶ G) {n : ℕ} (x : H F n) :
    H.map f n x = x.comp (Ext.mk₀ f) (add_zero n) := rfl

lemma H.map_id_apply {n : ℕ} (x : H F n) : H.map (𝟙 F) n x = x := by
  exact Ext.comp_mk₀_id x

lemma H.map_comp_apply (f : F ⟶ G) {n : ℕ} {G' : Sheaf J AddCommGrp.{w}}
    (g : G ⟶ G') (x : H F n) :
    H.map (f ≫ g) n x = H.map g n (H.map f n x) := by
  simp only [H.map_apply, ← Ext.mk₀_comp_mk₀]
  symm
  apply Ext.comp_assoc
  omega

lemma H.map_add_apply {n : ℕ} (f g : F ⟶ G) (x : H F n) :
    H.map (f + g) n x = H.map f n x + H.map g n x := by
  simp only [H.map_apply, Ext.mk₀_add, Ext.comp_add]

variable (J) in
/-- Abelian sheaf cohomology as an additive-group-valued functor. -/
def functorH (n : ℕ) : Sheaf J AddCommGrp.{w} ⥤ AddCommGrp.{w'} where
  obj F := AddCommGrp.of (H F n)
  map f := AddCommGrp.ofHom (H.map f n)
  map_id F := by
    ext x
    exact H.map_id_apply x
  map_comp f g := by
    ext x
    exact H.map_comp_apply f g x

/-- The functor uses the original Ext cohomology group on objects. -/
lemma functorH_obj (n : ℕ) (F : Sheaf J AddCommGrp.{w}) :
    (functorH J n).obj F = AddCommGrp.of (H F n) := rfl

/-- The functor's underlying map is Ext postcomposition. -/
lemma functorH_map (n : ℕ) (f : F ⟶ G) :
    (functorH J n).map f = AddCommGrp.ofHom (H.map f n) := rfl

instance (n : ℕ) : (functorH J n).Additive where
  map_add {F G} {f g} := by
    ext x
    exact H.map_add_apply f g x

end CategoryTheory.Sheaf
