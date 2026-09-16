import KltDP.Geometry.SchemeModuleIso
import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Conormal comparison under an isomorphism of the source

Precomposing a scheme morphism by an isomorphism leaves its actual
structure-map kernel unchanged. The comparison preserves the original
ideal inclusion. Pullback composition then identifies the conormal of
the composite with the pullback of the original conormal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X' X Y : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ Y)

/-- The source isomorphism identifies the actual pushforward structure modules. -/
def schemeSourceIsoPushforwardUnitIso :
    (schemeModulePushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf) ≅
      (schemeModulePushforward (e.hom ≫ f)).obj
        (_root_.SheafOfModules.unit X'.ringCatSheaf) :=
  (schemeModulePushforward f).mapIso (schemeIsoUnitIso e) ≪≫
    (schemeModulePushforwardCompIso e.hom f).app
      (_root_.SheafOfModules.unit X'.ringCatSheaf)

/-- The comparison intertwines the original structure maps. -/
theorem schemeSourceIsoPushforwardUnitIso_structure :
    structureToPushforwardUnit f ≫ (schemeSourceIsoPushforwardUnitIso e f).hom =
      structureToPushforwardUnit (e.hom ≫ f) := by
  simpa only [schemeSourceIsoPushforwardUnitIso, Iso.trans_hom,
    Functor.mapIso_hom, schemeIsoUnitIso_hom, Category.assoc] using
      (structureToPushforwardUnit_comp e.hom f).symm

/-- Precomposition by the original source isomorphism preserves the kernel. -/
def schemeKernelPrecompIso :
    schemeKernelIdeal (e.hom ≫ f) ≅ schemeKernelIdeal f :=
  (kernel.mapIso (structureToPushforwardUnit f)
    (structureToPushforwardUnit (e.hom ≫ f)) (Iso.refl _)
    (schemeSourceIsoPushforwardUnitIso e f)
    (by simpa only [Iso.refl_hom, Category.id_comp] using
      schemeSourceIsoPushforwardUnitIso_structure e f)).symm

/-- The kernel isomorphism preserves the original ideal inclusion. -/
theorem schemeKernelPrecompIso_hom_ι :
    (schemeKernelPrecompIso e f).hom ≫ schemeKernelIdealι f =
      schemeKernelIdealι (e.hom ≫ f) := by
  simp only [schemeKernelPrecompIso, schemeKernelIdealι, Iso.symm_hom,
    kernel.mapIso_inv, kernel.map, kernel.lift_ι, Iso.refl_inv, Category.comp_id]

/-- The inverse also preserves the original ideal inclusion. -/
theorem schemeKernelPrecompIso_inv_ι :
    (schemeKernelPrecompIso e f).inv ≫ schemeKernelIdealι (e.hom ≫ f) =
      schemeKernelIdealι f := by
  simp only [schemeKernelPrecompIso, schemeKernelIdealι, Iso.symm_inv,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι, Iso.refl_hom, Category.comp_id]

/-- Conormal comparison through the actual pullback functors and kernel maps. -/
def schemeConormalSourceIso :
    (schemeModulePullback e.hom).obj (schemeConormalSheaf f) ≅
      schemeConormalSheaf (e.hom ≫ f) :=
  (schemeModulePullbackCompIso e.hom f).app (schemeKernelIdeal f) ≪≫
    (schemeModulePullback (e.hom ≫ f)).mapIso (schemeKernelPrecompIso e f).symm

/-- The conormal comparison commutes with pullback of the original ideal inclusion. -/
theorem schemeConormalSourceIso_hom_ι :
    (schemeConormalSourceIso e f).hom ≫
        (schemeModulePullback (e.hom ≫ f)).map (schemeKernelIdealι (e.hom ≫ f)) =
      (schemeModulePullbackCompIso e.hom f).hom.app (schemeKernelIdeal f) ≫
        (schemeModulePullback (e.hom ≫ f)).map (schemeKernelIdealι f) := by
  simp only [schemeConormalSourceIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← Functor.map_comp, schemeKernelPrecompIso_inv_ι]

end KltDP.Geometry
