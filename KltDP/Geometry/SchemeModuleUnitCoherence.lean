import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.ModuleOpenRestrictionTensor
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Canonical unit coherence for actual scheme module pullbacks

The previously constructed pullback composition and open-restriction
comparisons come from uniqueness of left adjoints. Their compatibility
with the canonical structure-module unit maps follows from the original
adjunctions and original scheme structure maps. No coherence equation is
added as data or assumed as a geometric hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem homEquiv_ofNatIsoRight_apply
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (e : G ≅ H)
    (M : C) (N : D) (h : F.obj M ⟶ N) :
    (a.ofNatIsoRight e).homEquiv M N h = a.homEquiv M N h ≫ e.hom.app N := by
  rw [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

variable {X Y Z : Scheme.{u}}

/-- The canonical unit comparison is normalized by the actual scheme adjunction. -/
theorem schemeModuleUnit_homEquiv (f : X ⟶ Y) :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv _ _
      (schemeModulePullbackUnitHom f) = structureToPushforwardUnit f :=
  schemeModulePullbackUnitHom_adjunction f

/-- Iterated actual structure maps are the actual composite structure map. -/
theorem structureToPushforwardUnit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureToPushforwardUnit (f ≫ g) =
      (structureToPushforwardUnit g ≫
        (schemeModulePushforward g).map (structureToPushforwardUnit f)) ≫
          (schemeModulePushforwardCompIso f g).hom.app
            (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rfl

/-- Pullback composition preserves the canonical structure-module unit map. -/
theorem schemeModulePullbackCompIso_unit (f : X ⟶ Y) (g : Y ⟶ Z) :
    (schemeModulePullbackCompIso f g).hom.app
        (_root_.SheafOfModules.unit Z.ringCatSheaf) ≫
      (schemeModulePullbackUnitIso (f ≫ g)).hom =
    (schemeModulePullback f).map (schemeModulePullbackUnitIso g).hom ≫
      (schemeModulePullbackUnitIso f).hom := by
  let a := ((schemeModulePullbackPushforwardAdjunction g).comp
    (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
      (schemeModulePushforwardCompIso f g)
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _
      ((Adjunction.leftAdjointUniq a
        (schemeModulePullbackPushforwardAdjunction (f ≫ g))).hom.app _ ≫
          schemeModulePullbackUnitHom (f ≫ g)) =
    a.homEquiv _ _ ((schemeModulePullback f).map (schemeModulePullbackUnitHom g) ≫
      schemeModulePullbackUnitHom f)
  rw [homEquiv_leftAdjointUniq_comp, schemeModuleUnit_homEquiv]
  change structureToPushforwardUnit (f ≫ g) =
    (((schemeModulePullbackPushforwardAdjunction g).comp
      (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g)).homEquiv _ _ _
  rw [homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change structureToPushforwardUnit (f ≫ g) =
    (schemeModulePullbackPushforwardAdjunction g).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _
        ((schemeModulePullback f).map (schemeModulePullbackUnitHom g) ≫
          schemeModulePullbackUnitHom f)) ≫
      (schemeModulePushforwardCompIso f g).hom.app
        (_root_.SheafOfModules.unit X.ringCatSheaf)
  rw [Adjunction.homEquiv_naturality_left, schemeModuleUnit_homEquiv,
    Adjunction.homEquiv_naturality_right, schemeModuleUnit_homEquiv]
  exact structureToPushforwardUnit_comp f g

/-- Equality of actual scheme morphisms preserves the normalized pullback-unit map. -/
theorem schemeModulePullbackUnit_eqToIso {f g : X ⟶ Y} (h : f = g) :
    (eqToIso (congrArg schemeModulePullback h)).hom.app
        (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
      (schemeModulePullbackUnitIso g).hom = (schemeModulePullbackUnitIso f).hom := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

namespace SchemeModuleRestriction

variable (f : X ⟶ Y) [IsOpenImmersion f]

/-- The original restriction-unit comparison is adjoint to the original
scheme structure map under the actual open-restriction adjunction. -/
theorem restrictionUnitIso_homEquiv :
    (restrictionAdjunction f).homEquiv _ _ (restrictionUnitIso f).hom =
      structureToPushforwardUnit f := by
  rw [Adjunction.homEquiv_unit]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (Y.presheaf.map
      (homOfLE (Set.image_preimage_subset f.base (U.unop : Set Y))).op ≫
        (f.appIso (f ⁻¹ᵁ U.unop)).hom) r = f.app U.unop r
  rw [← f.app_appIso_inv U.unop, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual open-restriction/pullback comparison respects the canonical unit. -/
theorem restrictionIsoPullback_unit :
    (restrictionIsoPullback f).hom.app (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
        (schemeModulePullbackUnitIso f).hom = (restrictionUnitIso f).hom := by
  apply ((restrictionAdjunction f).homEquiv _ _).injective
  change (restrictionAdjunction f).homEquiv _ _
      ((Adjunction.leftAdjointUniq (restrictionAdjunction f)
        (schemeModulePullbackPushforwardAdjunction f)).hom.app _ ≫
          schemeModulePullbackUnitHom f) = _
  rw [homEquiv_leftAdjointUniq_comp, schemeModuleUnit_homEquiv,
    restrictionUnitIso_homEquiv]

end SchemeModuleRestriction

end KltDP.Geometry
