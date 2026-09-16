import KltDP.Geometry.SchemeKernelRestriction
import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Conormal comparison after a target open immersion

Image-open restriction of the original composite structural map is
identified with the structural map before the open immersion. The section
comparison uses the pinned inverse-image equality and the actual `appIso`.
Preservation of kernels and the original pullback comparisons then give
the kernel and conormal isomorphisms, with the kernel inclusion normalized.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ Z) [IsOpenImmersion a]

local instance : a.opensFunctor.IsContinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z) :=
  a.isOpenEmbedding.functor_isContinuous

private def postcompOpenPushforwardRingIso :
    a.opensFunctor.op ⋙ (Opens.map (f ≫ a).base).op ⋙ X.presheaf ≅
      (Opens.map f.base).op ⋙ X.presheaf :=
  NatIso.ofComponents
    (fun V => X.presheaf.mapIso
      (eqToIso (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
        f a (f ≫ a) rfl V.unop)).op)
    (fun {V W} i => by
      simp only [Functor.comp_map, Functor.op_map, Functor.mapIso_hom,
        Iso.op_hom, eqToIso.hom, ← Functor.map_comp]
      rfl)

private theorem postcompOpen_structure_app (V : Y.Opens) :
    (a.appIso V).inv ≫ (f ≫ a).app (a ''ᵁ V) ≫
        ((postcompOpenPushforwardRingIso f a).app (op V)).hom = f.app V :=
  (IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq f a (f ≫ a) rfl V).symm

private def postcompOpenPushforwardUnitLinearEquiv (V : Y.Opens) :
    ((restriction a).obj
      ((schemeModulePushforward (f ≫ a)).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf))).val.obj (op V) ≃ₗ[Γ(Y, V)]
      ((schemeModulePushforward f).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf)).val.obj (op V) :=
  { ((postcompOpenPushforwardRingIso f a).app (op V)).commRingCatIsoToRingEquiv.toAddEquiv with
    map_smul' := fun r s => by
      let s' : Γ(X, (f ≫ a) ⁻¹ᵁ (a ''ᵁ V)) := s
      let e : Γ(X, (f ≫ a) ⁻¹ᵁ (a ''ᵁ V)) ≃+* Γ(X, f ⁻¹ᵁ V) :=
        ((postcompOpenPushforwardRingIso f a).app (op V)).commRingCatIsoToRingEquiv
      change e ((f ≫ a).app (a ''ᵁ V) ((a.appIso V).inv r) * s') =
        f.app V r * e s'
      rw [e.map_mul]
      congr 1
      exact ConcreteCategory.congr_hom (postcompOpen_structure_app f a V) r }

private def postcompOpenPushforwardUnitIso :
    (restriction a).obj
      ((schemeModulePushforward (f ≫ a)).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf)) ≅
      (schemeModulePushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  (_root_.SheafOfModules.fullyFaithfulForget Y.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (postcompOpenPushforwardUnitLinearEquiv f a V.unop).toModuleIso)
      (fun {V W} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom
          ((postcompOpenPushforwardRingIso f a).hom.naturality i) s))

private theorem postcompOpen_structureToPushforwardUnit :
    (restriction a).map (structureToPushforwardUnit (f ≫ a)) ≫
        (postcompOpenPushforwardUnitIso f a).hom =
      (restrictionUnitIso a).hom ≫ structureToPushforwardUnit f := by
  apply (_root_.SheafOfModules.forget Y.ringCatSheaf).map_injective
  ext V r
  change ((postcompOpenPushforwardRingIso f a).app V).hom
      ((f ≫ a).app (a ''ᵁ V.unop) r) = f.app V.unop ((a.appIso V.unop).hom r)
  have h := congrArg ((a.appIso V.unop).hom ≫ ·)
    (postcompOpen_structure_app f a V.unop)
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    CommRingCat.comp_apply] using CategoryTheory.congr_fun h r

local instance : (restriction a).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩

local instance : (restriction a).IsRightAdjoint := by
  change (_root_.SheafOfModules.pushforward
    (restrictionRingSheafHom a)).IsRightAdjoint
  infer_instance

/-- Image-open restriction recovers the original kernel before the target
open immersion, using the actual structural section maps. -/
def schemeKernelPostcompRestrictionIso :
    (restriction a).obj (schemeKernelIdeal (f ≫ a)) ≅ schemeKernelIdeal f :=
  PreservesKernel.iso (restriction a) (structureToPushforwardUnit (f ≫ a)) ≪≫
    kernel.mapIso ((restriction a).map (structureToPushforwardUnit (f ≫ a)))
      (structureToPushforwardUnit f) (restrictionUnitIso a)
      (postcompOpenPushforwardUnitIso f a) (postcompOpen_structureToPushforwardUnit f a)

/-- The restriction comparison preserves the original kernel inclusion. -/
theorem schemeKernelPostcompRestrictionIso_hom_ι :
    (schemeKernelPostcompRestrictionIso f a).hom ≫ schemeKernelIdealι f =
      (restriction a).map (schemeKernelIdealι (f ≫ a)) ≫ (restrictionUnitIso a).hom := by
  simp only [schemeKernelPostcompRestrictionIso, schemeKernelIdealι, Iso.trans_hom,
    kernel.mapIso_hom, kernel.map, Category.assoc, kernel.lift_ι,
    PreservesKernel.iso_hom, kernelComparison_comp_ι_assoc]

/-- Pullback along the original target open immersion recovers the kernel
of the original morphism into that open. -/
def schemeKernelPostcompOpenIso :
    (schemeModulePullback a).obj (schemeKernelIdeal (f ≫ a)) ≅ schemeKernelIdeal f :=
  ((restrictionIsoPullback a).app (schemeKernelIdeal (f ≫ a))).symm ≪≫
    schemeKernelPostcompRestrictionIso f a

/-- The pullback comparison is normalized by the original structure-module
unit comparison and the original kernel inclusions. -/
theorem schemeKernelPostcompOpenIso_hom_ι :
    (schemeKernelPostcompOpenIso f a).hom ≫ schemeKernelIdealι f =
      (schemeModulePullback a).map (schemeKernelIdealι (f ≫ a)) ≫
        (schemeModulePullbackUnitIso a).hom := by
  simp only [schemeKernelPostcompOpenIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc, schemeKernelPostcompRestrictionIso_hom_ι]
  rw [← Category.assoc, ← (restrictionIsoPullback a).inv.naturality,
    Category.assoc, ← restrictionIsoPullback_unit a,
    ← Category.assoc ((restrictionIsoPullback a).inv.app
      (_root_.SheafOfModules.unit Z.ringCatSheaf)),
    Iso.inv_hom_id_app, Category.id_comp]

/-- Postcomposition by an arbitrary target open immersion preserves the
actual conormal module on the unchanged source scheme. -/
def schemeConormalPostcompOpenIso :
    schemeConormalSheaf (f ≫ a) ≅ schemeConormalSheaf f :=
  ((schemeModulePullbackCompIso f a).app (schemeKernelIdeal (f ≫ a))).symm ≪≫
    (schemeModulePullback f).mapIso (schemeKernelPostcompOpenIso f a)

end KltDP.Geometry
