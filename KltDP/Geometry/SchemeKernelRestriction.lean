import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.ModuleRestrictionPullback
import KltDP.Geometry.ModuleOpenRestrictionTensor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual restriction of scheme kernel and conormal sheaves

The actual open restriction of the structure-map kernel is the kernel
of the actual restricted scheme morphism. The proof constructs the
section-ring comparison for the pushforward structure module, then uses
preservation of kernels and the original structural maps.

The conormal comparison follows from that kernel isomorphism and the
already constructed pullback composition and open-restriction comparisons.
No flatness, quasi-compactness, or closed-immersion hypothesis is needed
for these functorial comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

local instance : U.ι.opensFunctor.IsContinuous
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology Y) :=
  U.ι.isOpenEmbedding.functor_isContinuous

/-- The actual section-ring comparison for restricting a pushforward
structure module to the target open. -/
def restrictionPushforwardUnitRingIso :
    U.ι.opensFunctor.op ⋙ (Opens.map f.base).op ⋙ X.presheaf ≅
      (Opens.map (f ∣_ U).base).op ⋙ (f ⁻¹ᵁ U).toScheme.presheaf :=
  NatIso.ofComponents
    (fun V => X.presheaf.mapIso
      (eqToIso (image_morphismRestrict_preimage f U V.unop)).op)
    (fun {V W} i => by
      simp only [Functor.comp_map, Functor.op_map, Functor.mapIso_hom,
        Iso.op_hom, eqToIso.hom, Scheme.Opens.toScheme_presheaf_map,
        ← Functor.map_comp]
      rfl)

/-- The ring comparison is linear for the actual structure-map scalar
actions on both pushforward module sheaves. -/
def restrictionPushforwardUnitLinearEquiv (V : U.toScheme.Opens) :
    ((SchemeModuleRestriction.restriction U.ι).obj
      ((schemeModulePushforward f).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf))).val.obj (op V) ≃ₗ[Γ(U.toScheme, V)]
      ((schemeModulePushforward (f ∣_ U)).obj
        (_root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf)).val.obj (op V) :=
  { ((restrictionPushforwardUnitRingIso f U).app (op V)).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := fun r s => by
      let s' : Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V)) := s
      let e : Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V)) ≃+*
          Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V) :=
        ((restrictionPushforwardUnitRingIso f U).app (op V)).commRingCatIsoToRingEquiv
      change e (f.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv r) * s') =
        (f ∣_ U).app V r * e s'
      rw [Scheme.Opens.ι_appIso]
      change e (f.app (U.ι ''ᵁ V) r * s') = _
      rw [e.map_mul]
      congr 1
      change ((restrictionPushforwardUnitRingIso f U).app (op V)).hom
        (f.app (U.ι ''ᵁ V) r) = (f ∣_ U).app V r
      exact (ConcreteCategory.congr_hom (morphismRestrict_app f U V) r).symm }

/-- The actual pushforward structure modules agree under open
restriction, through the canonical section-ring comparisons. -/
def restrictionPushforwardUnitIso :
    (SchemeModuleRestriction.restriction U.ι).obj
      ((schemeModulePushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) ≅
    (schemeModulePushforward (f ∣_ U)).obj
      (_root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  (_root_.SheafOfModules.fullyFaithfulForget U.toScheme.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (restrictionPushforwardUnitLinearEquiv f U V.unop).toModuleIso)
      (fun {V W} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom
          ((restrictionPushforwardUnitRingIso f U).hom.naturality i) s))

/-- These isomorphisms commute with the original structure maps. -/
theorem restriction_structureToPushforwardUnit :
    (SchemeModuleRestriction.restriction U.ι).map (structureToPushforwardUnit f) ≫
        (restrictionPushforwardUnitIso f U).hom =
      (SchemeModuleRestriction.restrictionUnitIso U.ι).hom ≫
        structureToPushforwardUnit (f ∣_ U) := by
  apply (_root_.SheafOfModules.forget U.toScheme.ringCatSheaf).map_injective
  ext V r
  change ((restrictionPushforwardUnitRingIso f U).app V).hom
      (f.app (U.ι ''ᵁ V.unop) r) =
    (f ∣_ U).app V.unop ((U.ι.appIso V.unop).hom r)
  rw [Scheme.Opens.ι_appIso]
  exact (ConcreteCategory.congr_hom (morphismRestrict_app f U V.unop) r).symm

local instance : (SchemeModuleRestriction.restriction U.ι).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

local instance : (SchemeModuleRestriction.restriction U.ι).IsRightAdjoint := by
  change (_root_.SheafOfModules.pushforward
    (SchemeModuleRestriction.restrictionRingSheafHom U.ι)).IsRightAdjoint
  infer_instance

/-- The actual restriction of the global structure-map kernel is the
actual kernel of the restricted scheme morphism. -/
def schemeKernelRestrictionIso :
    (SchemeModuleRestriction.restriction U.ι).obj (schemeKernelIdeal f) ≅
      schemeKernelIdeal (f ∣_ U) :=
  PreservesKernel.iso (SchemeModuleRestriction.restriction U.ι)
      (structureToPushforwardUnit f) ≪≫
    kernel.mapIso
      ((SchemeModuleRestriction.restriction U.ι).map (structureToPushforwardUnit f))
      (structureToPushforwardUnit (f ∣_ U))
      (SchemeModuleRestriction.restrictionUnitIso U.ι)
      (restrictionPushforwardUnitIso f U)
      (restriction_structureToPushforwardUnit f U)

/-- The kernel comparison commutes with the actual ideal inclusions. -/
theorem schemeKernelRestrictionIso_hom_ι :
    (schemeKernelRestrictionIso f U).hom ≫ schemeKernelIdealι (f ∣_ U) =
      (SchemeModuleRestriction.restriction U.ι).map (schemeKernelIdealι f) ≫
        (SchemeModuleRestriction.restrictionUnitIso U.ι).hom := by
  simp only [schemeKernelRestrictionIso, schemeKernelIdealι, Iso.trans_hom,
    kernel.mapIso_hom, kernel.map, Category.assoc, kernel.lift_ι,
    PreservesKernel.iso_hom, kernelComparison_comp_ι_assoc]

/-- The actual restriction of the global pullback-of-kernel conormal is
the conormal of the actual restricted scheme morphism. -/
def schemeConormalRestrictionIso :
    (SchemeModuleRestriction.restriction (f ⁻¹ᵁ U).ι).obj (schemeConormalSheaf f) ≅
      schemeConormalSheaf (f ∣_ U) :=
  (SchemeModuleRestriction.restrictionIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).app _ ≪≫
    (eqToIso (congrArg schemeModulePullback (morphismRestrict_ι f U).symm)).app _ ≪≫
    ((schemeModulePullbackCompIso (f ∣_ U) U.ι).app _).symm ≪≫
    (schemeModulePullback (f ∣_ U)).mapIso
      ((SchemeModuleRestriction.restrictionIsoPullback U.ι).app _).symm ≪≫
    (schemeModulePullback (f ∣_ U)).mapIso (schemeKernelRestrictionIso f U)

end KltDP.Geometry
