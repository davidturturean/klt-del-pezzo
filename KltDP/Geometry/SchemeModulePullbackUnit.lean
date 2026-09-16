/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

The canonical adjoint map and its Yoneda proof are adapted from official
Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean:45-111.
The newer general theorem on sections of a final functor is replaced by
the explicit equivalence with sections at the top open of an actual scheme.
-/
import KltDP.Geometry.SchemeConormal
import Mathlib.CategoryTheory.Yoneda

/-!
# The actual structure-sheaf comparison for scheme module pullback

For every actual scheme morphism, the pullback of the target's unit module
is canonically the source's unit module. The map is the adjoint of the
original structural section map. Its invertibility is proved from the
pullback-pushforward adjunction and actual global sections, with no
flatness, open immersion, or local-freeness hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

/-- An actual section over the top open gives its compatible family of
restrictions to all opens. -/
def schemeModuleSectionOfTop (M : X.Modules) (s : M.val.obj (op ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
    (fun {U V} g => by
      exact (CategoryTheory.congr_fun
        (M.val.presheaf.map_comp (homOfLE (le_top : U.unop ≤ ⊤)).op g) s).symm)

/-- Global compatible families of module sections are exactly the actual
sections on the top open. -/
def schemeModuleSectionsEquivTop (M : X.Modules) :
    M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun := schemeModuleSectionOfTop M
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE (le_top : U.unop ≤ ⊤)).op
  right_inv s := by
    change M.val.presheaf.map (𝟙 (op (⊤ : X.Opens))) s = s
    exact ConcreteCategory.congr_hom (M.val.presheaf.map_id _) s

variable (f : X ⟶ Y)

/-- The actual pushforward sends a compatible family to the same family
evaluated on inverse-image opens. -/
def schemeModulePushforwardSections {M : X.Modules} (s : M.sections) :
    ((schemeModulePushforward f).obj M).sections where
  val U := s.val ((Opens.map f.base).op.obj U)
  property g := s.property ((Opens.map f.base).op.map g)

/-- Pushforward preserves actual global sections: both families are
determined by their value on the same top open of the source. -/
theorem schemeModulePushforwardSections_bijective (M : X.Modules) :
    Function.Bijective (schemeModulePushforwardSections f (M := M)) := by
  let e := schemeModuleSectionsEquivTop ((schemeModulePushforward f).obj M)
  apply (e.bijective.of_comp_iff' _).mp
  change Function.Bijective (fun s : M.sections => s.val (op (f ⁻¹ᵁ ⊤)))
  simpa only [Opens.map_top] using (schemeModuleSectionsEquivTop M).bijective

/-- Evaluation at one commutes with the original structural map and
pushforward of an actual module homomorphism. -/
theorem schemeModulePushforwardSections_unitHomEquiv {M : X.Modules}
    (g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    schemeModulePushforwardSections f (M.unitHomEquiv g) =
      ((schemeModulePushforward f).obj M).unitHomEquiv
        (structureToPushforwardUnit f ≫ (schemeModulePushforward f).map g) := by
  apply PresheafOfModules.sections_ext
  intro U
  change g.val.app ((Opens.map f.base).op.obj U) (1 : Γ(X, f ⁻¹ᵁ U.unop)) =
    g.val.app ((Opens.map f.base).op.obj U) (f.app U.unop (1 : Γ(Y, U.unop)))
  rw [(f.app U.unop).hom.map_one]

/-- The canonical comparison is the adjoint of the actual structure map. -/
def schemeModulePullbackUnitHom :
    (schemeModulePullback f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf :=
  ((_root_.SheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f)).homEquiv
    _ _).symm (structureToPushforwardUnit f)

/-- Under the original adjunction the canonical comparison recovers the
original structure map, fixing its normalization. -/
@[simp]
theorem schemeModulePullbackUnitHom_adjunction :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f)).homEquiv
      _ _ (schemeModulePullbackUnitHom f) = structureToPushforwardUnit f :=
  Equiv.apply_symm_apply _ _

instance schemeModulePullbackUnitHom_isIso : IsIso (schemeModulePullbackUnitHom f) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((_root_.SheafOfModules.pullbackPushforwardAdjunction
      (schemeRingSheafHom f)).homEquiv _ _).bijective.of_comp_iff',
    ← (_root_.SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert (schemeModulePushforwardSections_bijective f M).comp
    (_root_.SheafOfModules.unitHomEquiv _).bijective using 1
  ext g : 1
  dsimp
  rw [schemeModulePushforwardSections_unitHomEquiv]
  apply congrArg (((schemeModulePushforward f).obj M).unitHomEquiv)
  rw [Adjunction.homEquiv_naturality_right, schemeModulePullbackUnitHom_adjunction]
  rfl

/-- Pullback of the actual target structure module is canonically the
source structure module for every scheme morphism. -/
def schemeModulePullbackUnitIso :
    (schemeModulePullback f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ≅
      _root_.SheafOfModules.unit X.ringCatSheaf :=
  asIso (schemeModulePullbackUnitHom f)

end KltDP.Geometry
