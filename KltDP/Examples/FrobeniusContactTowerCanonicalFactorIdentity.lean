import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# The original identity pullback retains structure-module inclusions

The actual identity comparison is uniqueness of the original adjoint. Its
unit component is the original pullback-unit map, by their common adjunction
normalization. Naturality then retains every actual map into the structure
module. This is used for the newest exceptional total transform.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdentity

open KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem homEquiv_ofNatIsoRight_apply
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (a : F ⊣ G) (e : G ≅ H)
    (M : C) (N : D) (h : F.obj M ⟶ N) :
    (a.ofNatIsoRight e).homEquiv M N h = a.homEquiv M N h ≫ e.hom.app N := by
  rw [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem structureToPushforwardUnit_id (X : Scheme.{u}) :
    structureToPushforwardUnit (𝟙 X) ≫
        (schemeModulePushforwardIdIso X).hom.app (_root_.SheafOfModules.unit X.ringCatSheaf) =
      𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rfl

/-- The existing identity comparison has the existing normalized unit component. -/
theorem pullbackIdIso_unit (X : Scheme.{u}) :
    (schemeModulePullbackIdIso X).hom.app (_root_.SheafOfModules.unit X.ringCatSheaf) =
      (schemeModulePullbackUnitIso (𝟙 X)).hom := by
  let a := (schemeModulePullbackPushforwardAdjunction (𝟙 X)).ofNatIsoRight
    (schemeModulePushforwardIdIso X)
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _
      ((Adjunction.leftAdjointUniq a Adjunction.id).hom.app
        (_root_.SheafOfModules.unit X.ringCatSheaf)) =
    a.homEquiv _ _ (schemeModulePullbackUnitHom (𝟙 X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, homEquiv_ofNatIsoRight_apply,
    schemeModuleUnit_homEquiv]
  exact (structureToPushforwardUnit_id X).symm

/-- Naturality identifies the actual inclusion after the same identity pullback. -/
@[reassoc] theorem pullbackIdIso_inclusion {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (schemeModulePullbackIdIso X).hom.app I ≫ i =
      (schemeModulePullback (𝟙 X)).map i ≫ (schemeModulePullbackUnitIso (𝟙 X)).hom := by
  rw [← pullbackIdIso_unit]
  exact ((schemeModulePullbackIdIso X).hom.naturality i).symm

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdentity

