/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunction of actual module-sheaf pushforwards

This is a bounded adaptation of the proved construction in official Mathlib
`Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`, revision
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`, lines 273–302. The upstream
file has SHA-256
`7cf97d91ffb6496aa5b7af60717a68fbdbe00e0bf16c3a00eeed47497de16404`.
The original Apache-2.0 attribution is retained above.

The pinned library already constructs both actual module pushforwards. We
build the unit and counit directly from the underlying additive presheaves,
using the site adjunction and the two exact compatibility equations for the
ring maps. These equations prove scalar linearity for the existing actions.
Naturality and both triangle identities use the original presheaf maps.
No new pullback, comparison isomorphism, or adjunction is assumed.
-/

noncomputable section

open CategoryTheory Opposite

universe v v₁ v₂ u₁ u₂ u

namespace KltDP.SheafModuleAdjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} {G : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous.{u} F J K] [Functor.IsContinuous.{v} F J K]
  [Functor.IsContinuous.{u} G K J] [Functor.IsContinuous.{v} G K J]
  (adj : F ⊣ G)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : whiskerRight (NatTrans.op adj.counit) R.val =
    ψ.val ≫ whiskerLeft G.op φ.val)
  (H₂ : φ.val ≫ whiskerLeft F.op ψ.val ≫
    whiskerRight (NatTrans.op adj.unit) S.val = 𝟙 S.val)

/-- The site counit induces the unit on actual module sheaves. -/
def pushforwardPushforwardUnit :
    𝟭 (_root_.SheafOfModules.{v} R) ⟶
      _root_.SheafOfModules.pushforward.{v} φ ⋙
        _root_.SheafOfModules.pushforward.{v} ψ where
  app M :=
    _root_.SheafOfModules.Hom.mk <|
      _root_.PresheafOfModules.homMk
        (whiskerRight (NatTrans.op adj.counit) M.val.presheaf) (by
          intro U r m
          change M.val.map (adj.counit.app U.unop).op (r • m) =
            φ.val.app (op (G.obj U.unop)) (ψ.val.app U r) •
              M.val.map (adj.counit.app U.unop).op m
          rw [M.val.map_smul]
          have hr := ConcreteCategory.congr_hom (NatTrans.congr_app H₁ U) r
          change R.val.map (adj.counit.app U.unop).op r =
            φ.val.app (op (G.obj U.unop)) (ψ.val.app U r) at hr
          rw [hr])
  naturality {M N} a := by
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (_root_.PresheafOfModules.naturality_apply a.val
      (adj.counit.app U.unop).op x).symm

/-- The site unit induces the counit on actual module sheaves. -/
def pushforwardPushforwardCounit :
    _root_.SheafOfModules.pushforward.{v} ψ ⋙
        _root_.SheafOfModules.pushforward.{v} φ ⟶
      𝟭 (_root_.SheafOfModules.{v} S) where
  app M :=
    _root_.SheafOfModules.Hom.mk <|
      _root_.PresheafOfModules.homMk
        (whiskerRight (NatTrans.op adj.unit) M.val.presheaf) (by
          intro U r m
          change M.val.map (adj.unit.app U.unop).op
              (ψ.val.app (op (F.obj U.unop)) (φ.val.app U r) •
                (show M.val.obj (op (G.obj (F.obj U.unop))) from m)) =
            r • M.val.map (adj.unit.app U.unop).op m
          rw [M.val.map_smul]
          have hr := ConcreteCategory.congr_hom (NatTrans.congr_app H₂ U) r
          change S.val.map (adj.unit.app U.unop).op
            (ψ.val.app (op (F.obj U.unop)) (φ.val.app U r)) = r at hr
          rw [hr])
  naturality {M N} a := by
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (_root_.PresheafOfModules.naturality_apply a.val
      (adj.unit.app U.unop).op x).symm

/-- Compatible ring maps lift a site adjunction to the existing actual
module-sheaf pushforward functors. -/
def pushforwardPushforwardAdj :
    _root_.SheafOfModules.pushforward.{v} φ ⊣
      _root_.SheafOfModules.pushforward.{v} ψ where
  unit := pushforwardPushforwardUnit adj φ ψ H₁
  counit := pushforwardPushforwardCounit adj φ ψ H₂
  left_triangle_components M := by
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (M.val.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      M.val.presheaf.map (F.map (adj.unit.app U.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components M := by
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (M.val.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      M.val.presheaf.map (adj.unit.app (G.obj U.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

/-- The unit uses the original module restriction along the site counit. -/
theorem pushforwardPushforwardAdj_unit_app_val_app
    (M : _root_.SheafOfModules.{v} R) (U : Dᵒᵖ) (x : M.val.obj U) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).val.app U x =
      M.val.map (adj.counit.app U.unop).op x := rfl

/-- The counit uses the original module restriction along the site unit. -/
theorem pushforwardPushforwardAdj_counit_app_val_app
    (M : _root_.SheafOfModules.{v} S) (U : Cᵒᵖ)
    (x : M.val.obj (op (G.obj (F.obj U.unop)))) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (adj.unit.app U.unop).op x := rfl

end KltDP.SheafModuleAdjunction
