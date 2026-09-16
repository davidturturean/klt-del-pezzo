/-
Original project adapter using the original scheme morphism and pinned
opens equivalence. Released under Apache 2.0; see
docs/reuse_sources/affine_open_kernel/sources/LICENSE.
-/
import KltDP.Compatibility.ModuleSheafEquivalence
import KltDP.Compatibility.SheafGeneratingSectionsMap
import KltDP.Geometry.SchemeConormal
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Actual module transport through a scheme isomorphism

The original inverse-image functor on opens is the forward functor of
the pinned `Opens.mapMapIso`. Original section-ring isomorphisms make the
scheme's existing scalar map invertible. Thus the existing module
pushforward is an equivalence, with actual free/unit/kernel comparisons.
No replacement module category or assumed comparison is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The original inverse-image functor on opens of a scheme isomorphism. -/
def schemeIsoOpensEquivalence : Y.Opens ≌ X.Opens :=
  Opens.mapMapIso (Scheme.forgetToTop.mapIso e)

local instance : Functor.IsContinuous.{u} (schemeIsoOpensEquivalence e).functor
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
  inferInstanceAs (Functor.IsContinuous.{u} (Opens.map e.hom.base)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X))

local instance : Functor.IsContinuous.{u} (schemeIsoOpensEquivalence e).inverse
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  inferInstanceAs (Functor.IsContinuous.{u} (Opens.map e.inv.base)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y))

/-- The scalar map is the original scheme structure map on every open. -/
instance schemeIsoRingSheafHom_isIso (f : X ⟶ Y) [IsIso f] :
    IsIso (schemeRingSheafHom f) := by
  haveI (V : Y.Opens) : IsIso (f.app V) :=
    Scheme.Hom.isIso_app f V (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  haveI (V : (Y.Opens)ᵒᵖ) : IsIso ((schemeRingSheafHom f).val.app V) := by
    change IsIso ((forget₂ CommRingCat RingCat).map (f.app V.unop))
    infer_instance
  haveI : IsIso ((sheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{u}).map
      (schemeRingSheafHom f)) := by
    change IsIso (schemeRingSheafHom f).val
    exact NatIso.isIso_of_isIso_app _
  exact (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{u}).isIso_of_isIso_map
    (schemeRingSheafHom f)

/-- The forward functor is the original pushforward along the actual
scheme-isomorphism morphism. -/
def schemeModuleIsoEquivalence : X.Modules ≌ Y.Modules := by
  letI : IsIso (schemeRingSheafHom e.hom) := schemeIsoRingSheafHom_isIso e.hom
  exact KltDP.SheafModuleEquivalence.pushforwardEquivalence (schemeIsoOpensEquivalence e)
    (schemeRingSheafHom e.hom)

@[simp]
theorem schemeModuleIsoEquivalence_functor :
    (schemeModuleIsoEquivalence e).functor = schemeModulePushforward e.hom := rfl

instance schemeIsoModulePushforward_isEquivalence (f : X ⟶ Y) [IsIso f] :
    (schemeModulePushforward f).IsEquivalence :=
  (schemeModuleIsoEquivalence (asIso f)).isEquivalence_functor

/-- The original structural module map is an isomorphism because its
underlying maps are the actual section-ring isomorphisms. -/
instance schemeIsoStructureToPushforwardUnit_isIso (f : X ⟶ Y) [IsIso f] :
    IsIso (structureToPushforwardUnit f) := by
  haveI (V : Y.Opens) : IsIso (f.app V) :=
    Scheme.Hom.isIso_app f V (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  let F := _root_.SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf Y.ringCatSheaf.val
  haveI : IsIso (F.map (structureToPushforwardUnit f)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (((forget₂ CommRingCat RingCat) ⋙
      forget₂ RingCat AddCommGrp).map (f.app V.unop))
    infer_instance
  exact isIso_of_reflects_iso _ F

/-- The unit comparison has exactly the original structural map as its hom. -/
def schemeIsoUnitIso : _root_.SheafOfModules.unit Y.ringCatSheaf ≅
    (schemeModulePushforward e.hom).obj (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  asIso (structureToPushforwardUnit e.hom)

@[simp]
theorem schemeIsoUnitIso_hom : (schemeIsoUnitIso e).hom =
    structureToPushforwardUnit e.hom := rfl

/-- The comparison of original coproduct free sheaves. -/
def schemeIsoFreeIso (I : Type u) :
    _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ≅
      (schemeModulePushforward e.hom).obj
        (_root_.SheafOfModules.free (R := X.ringCatSheaf) I) :=
  _root_.SheafOfModules.mapFreeIso (schemeModulePushforward e.hom) I (schemeIsoUnitIso e)

local instance (f : X ⟶ Y) : (schemeModulePushforward f).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

variable (I : Type u)

/-- Recover every original free-to-unit morphism, without a surjectivity premise. -/
def schemeIsoFreeToUnitPreimage
    (φ : _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit Y.ringCatSheaf) :
    _root_.SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf :=
  (schemeModulePushforward e.hom).preimage
    ((schemeIsoFreeIso e I).inv ≫ φ ≫ (schemeIsoUnitIso e).hom)

@[simp]
theorem schemeIsoFreeToUnitPreimage_map
    (φ : _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeModulePushforward e.hom).map (schemeIsoFreeToUnitPreimage e I φ) =
      (schemeIsoFreeIso e I).inv ≫ φ ≫ (schemeIsoUnitIso e).hom :=
  (schemeModulePushforward e.hom).map_preimage _

/-- The actual recovered map has the original kernel after transport. -/
def schemeIsoFreeToUnitKernelIso
    (φ : _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeModulePushforward e.hom).obj (kernel (schemeIsoFreeToUnitPreimage e I φ)) ≅
      kernel φ :=
  PreservesKernel.iso (schemeModulePushforward e.hom) (schemeIsoFreeToUnitPreimage e I φ) ≪≫
    kernel.mapIso ((schemeModulePushforward e.hom).map (schemeIsoFreeToUnitPreimage e I φ)) φ
      (schemeIsoFreeIso e I).symm (schemeIsoUnitIso e).symm (by
        simp only [Iso.symm_hom, schemeIsoFreeToUnitPreimage_map, Category.assoc,
          Iso.hom_inv_id, Category.comp_id])

/-- The kernel comparison retains the original inclusion and free coordinates. -/
theorem schemeIsoFreeToUnitKernelIso_hom_ι
    (φ : _root_.SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeIsoFreeToUnitKernelIso e I φ).hom ≫ kernel.ι φ =
      (schemeModulePushforward e.hom).map
        (kernel.ι (schemeIsoFreeToUnitPreimage e I φ)) ≫ (schemeIsoFreeIso e I).inv := by
  simp only [schemeIsoFreeToUnitKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.lift_ι, Iso.symm_hom, PreservesKernel.iso_hom]
  rw [← Category.assoc, kernelComparison_comp_ι]

end KltDP.Geometry
