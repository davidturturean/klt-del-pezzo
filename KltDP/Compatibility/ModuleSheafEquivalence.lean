/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0; see
docs/reuse_sources/module_sheaf_equivalence/sources/LICENSE.
Authors of the adapted upstream construction: Joël Riou

Bounded adaptation of official Mathlib
5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:307–323,386–407.
The existing project adjunction and pinned Adjunction.toEquivalence replace
the newer general pushforward-composition infrastructure.
-/
import KltDP.Compatibility.ModulePushforwardAdjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Original module sheaves under an equivalence of ringed sites

The inverse ring map is constructed from the actual site counit and the
inverse of the given ring-sheaf isomorphism. Both compatibility equations
are proved from that inverse and its naturality. The original module
pushforwards are then an equivalence: after forgetting module structures,
the adjunction unit and counit are the original restrictions along site
isomorphisms. No equivalence or preservation conclusion is assumed.
-/

noncomputable section

open CategoryTheory Opposite

universe u u₁ v₁ u₂ v₂

namespace KltDP.SheafModuleEquivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (e : C ≌ D) {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} e.functor J K] [Functor.IsContinuous.{u} e.inverse K J]
  (φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [IsIso φ]

/-- The inverse scalar comparison uses the original counit restriction
and the inverse of the original ring-sheaf map. -/
def inverseRingSheafHom : R ⟶
    (e.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S where
  val := whiskerRight (NatTrans.op e.counit) R.val ≫
    whiskerLeft e.inverse.op (inv φ).val

/-- The first scalar compatibility equation is actual inverse cancellation. -/
theorem inverseRingSheafHom_condition₁ :
    whiskerRight (NatTrans.op e.counit) R.val =
      (inverseRingSheafHom e φ).val ≫ whiskerLeft e.inverse.op φ.val := by
  apply NatTrans.ext
  funext U
  have h : (inv φ).val.app (op (e.inverse.obj U.unop)) ≫
      φ.val.app (op (e.inverse.obj U.unop)) = 𝟙 _ :=
    congrArg (fun a => a.val.app (op (e.inverse.obj U.unop))) (IsIso.inv_hom_id φ)
  change R.val.map (e.counit.app U.unop).op =
    (R.val.map (e.counit.app U.unop).op ≫
      (inv φ).val.app (op (e.inverse.obj U.unop))) ≫
        φ.val.app (op (e.inverse.obj U.unop))
  simpa only [Category.assoc, h] using
    (Category.comp_id (R.val.map (e.counit.app U.unop).op)).symm

/-- Naturality of the inverse ring map and the actual site triangle
give the second scalar compatibility equation. -/
theorem inverseRingSheafHom_condition₂ :
    φ.val ≫ whiskerLeft e.functor.op (inverseRingSheafHom e φ).val ≫
      whiskerRight (NatTrans.op e.unit) S.val = 𝟙 S.val := by
  apply NatTrans.ext
  funext U
  have hn :
      R.val.map (e.functor.map (e.unit.app U.unop)).op ≫ (inv φ).val.app U =
        (inv φ).val.app (op (e.inverse.obj (e.functor.obj U.unop))) ≫
          S.val.map (e.unit.app U.unop).op :=
    (inv φ).val.naturality (e.unit.app U.unop).op
  have ht : R.val.map (e.counit.app (e.functor.obj U.unop)).op ≫
      R.val.map (e.functor.map (e.unit.app U.unop)).op = 𝟙 _ := by
    rw [← R.val.map_comp, ← op_comp, e.functor_unit_comp]
    change R.val.map (𝟙 (op (e.functor.obj U.unop))) = 𝟙 _
    exact R.val.map_id _
  change φ.val.app U ≫
      ((R.val.map (e.counit.app (e.functor.obj U.unop)).op ≫
        (inv φ).val.app (op (e.inverse.obj (e.functor.obj U.unop)))) ≫
          S.val.map (e.unit.app U.unop).op) = 𝟙 _
  rw [Category.assoc, ← hn,
    ← Category.assoc (R.val.map (e.counit.app (e.functor.obj U.unop)).op),
    ht, Category.id_comp]
  exact congrArg (fun a => a.val.app U) (IsIso.hom_inv_id φ)

/-- The original pushforward functors have their actual ring-compatible
adjunction, with no sheafification or preservation premise. -/
def pushforwardAdjunction :
    _root_.SheafOfModules.pushforward.{u} φ ⊣
      _root_.SheafOfModules.pushforward.{u} (inverseRingSheafHom e φ) :=
  KltDP.SheafModuleAdjunction.pushforwardPushforwardAdj e.toAdjunction φ
    (inverseRingSheafHom e φ) (inverseRingSheafHom_condition₁ e φ)
      (inverseRingSheafHom_condition₂ e φ)

/-- The actual unit is invertible because its underlying additive section
map is restriction along the original site counit isomorphism. -/
instance pushforwardAdjunction_unit_isIso (M : _root_.SheafOfModules.{u} R) :
    IsIso ((pushforwardAdjunction e φ).unit.app M) := by
  let F := _root_.SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.val
  haveI : IsIso (F.map ((pushforwardAdjunction e φ).unit.app M)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    change IsIso (M.val.presheaf.map (e.counit.app U.unop).op)
    infer_instance
  exact isIso_of_reflects_iso _ F

/-- The actual counit is invertible by the original site unit isomorphism. -/
instance pushforwardAdjunction_counit_isIso (M : _root_.SheafOfModules.{u} S) :
    IsIso ((pushforwardAdjunction e φ).counit.app M) := by
  let F := _root_.SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.val
  haveI : IsIso (F.map ((pushforwardAdjunction e φ).counit.app M)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    change IsIso (M.val.presheaf.map (e.unit.app U.unop).op)
    infer_instance
  exact isIso_of_reflects_iso _ F

/-- An actual ring-sheaf isomorphism over a site equivalence gives an
equivalence whose forward functor is the original module pushforward. -/
def pushforwardEquivalence :
    _root_.SheafOfModules.{u} R ≌ _root_.SheafOfModules.{u} S :=
  (pushforwardAdjunction e φ).toEquivalence

@[simp]
theorem pushforwardEquivalence_functor :
    (pushforwardEquivalence e φ).functor = _root_.SheafOfModules.pushforward.{u} φ := rfl

end KltDP.SheafModuleEquivalence
