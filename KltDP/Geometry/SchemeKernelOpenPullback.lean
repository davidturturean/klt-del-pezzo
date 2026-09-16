import KltDP.Geometry.AffineBlowupConormalChartFrames
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Original kernel equations on a common ambient pullback

An actual open pullback of the original kernel inclusion remains a
monomorphism. The canonical comparison from the kernel of an open
restriction is normalized by that inclusion, so its local equation map
still multiplies by the original local equation. Further actual pullback
preserves this normalization. Equality can consequently be checked in
the actual structure module on a common ambient open.

There is no assumed equality of frames, transition coefficient, or
conormal identification. Closed-immersion pullback is not asserted to
preserve the kernel inclusion as a monomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

variable {X Y Z W : Scheme.{u}}

/-- The actual inverse-image functor along an open immersion preserves
monomorphisms, through its existing isomorphism with actual restriction. -/
theorem schemeModulePullback_preservesMonomorphisms_of_openImmersion
    (i : Z ⟶ Y) [IsOpenImmersion i] :
    (schemeModulePullback i).PreservesMonomorphisms := by
  letI : i.opensFunctor.IsContinuous
      (_root_.Opens.grothendieckTopology Z)
      (_root_.Opens.grothendieckTopology Y) :=
    i.isOpenEmbedding.functor_isContinuous
  letI : (restriction i).IsRightAdjoint := by
    change (_root_.SheafOfModules.pushforward.{u}
      (F := i.opensFunctor) (restrictionRingSheafHom i)).IsRightAdjoint
    infer_instance
  exact Functor.preservesMonomorphisms.of_iso (restrictionIsoPullback i)

/-- The original kernel inclusion pulled to an actual ambient scheme,
then followed by the original unit comparison. -/
def pulledKernelInclusion (f : X ⟶ Y) (i : Z ⟶ Y) :
    (schemeModulePullback i).obj (schemeKernelIdeal f) ⟶
      _root_.SheafOfModules.unit Z.ringCatSheaf :=
  (schemeModulePullback i).map (schemeKernelIdealι f) ≫
    (schemeModulePullbackUnitIso i).hom

/-- It remains an inclusion over an actual open immersion. -/
theorem pulledKernelInclusion_mono (f : X ⟶ Y) (i : Z ⟶ Y) [IsOpenImmersion i] :
    Mono (pulledKernelInclusion f i) := by
  letI := schemeModulePullback_preservesMonomorphisms_of_openImmersion i
  unfold pulledKernelInclusion schemeKernelIdealι
  infer_instance

/-- Kernel maps on a common ambient open are determined by the original
inclusion into that open's actual structure module. -/
theorem pulledKernelInclusion_cancel (f : X ⟶ Y) (i : Z ⟶ Y) [IsOpenImmersion i]
    {M : Z.Modules} (s t : M ⟶ (schemeModulePullback i).obj (schemeKernelIdeal f)) :
    s ≫ pulledKernelInclusion f i = t ≫ pulledKernelInclusion f i ↔ s = t := by
  letI := pulledKernelInclusion_mono f i
  exact cancel_mono (pulledKernelInclusion f i)

/-- The actual local kernel is compared with the global kernel pulled
back along this original open inclusion. -/
def localKernelToGlobalPullbackIso (f : X ⟶ Y) (U : Y.Opens) :
    schemeKernelIdeal (f ∣_ U) ≅
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f) :=
  (schemeKernelRestrictionIso f U).symm ≪≫
    (restrictionIsoPullback U.ι).app (schemeKernelIdeal f)

/-- This comparison preserves the original inclusion, including the
canonical normalization of the structure module. -/
theorem localKernelToGlobalPullbackIso_inclusion (f : X ⟶ Y) (U : Y.Opens) :
    (localKernelToGlobalPullbackIso f U).hom ≫ pulledKernelInclusion f U.ι =
      schemeKernelIdealι (f ∣_ U) := by
  simp only [localKernelToGlobalPullbackIso, pulledKernelInclusion, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← Category.assoc ((restrictionIsoPullback U.ι).hom.app (schemeKernelIdeal f)),
    ← (restrictionIsoPullback U.ι).hom.naturality (schemeKernelIdealι f),
    Category.assoc, restrictionIsoPullback_unit]
  rw [← schemeKernelRestrictionIso_hom_ι, Iso.inv_hom_id_assoc]

/-- An actual equation of the restricted morphism gives a map into the
pullback of the same original global kernel. -/
def localKernelGlobalEquation (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (schemeModulePullback U.ι).obj (schemeKernelIdeal f) :=
  schemeKernelGenerator (f ∣_ U) d hd ≫ (localKernelToGlobalPullbackIso f U).hom

/-- Its original inclusion is precisely multiplication by that equation. -/
theorem localKernelGlobalEquation_inclusion (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0) :
    localKernelGlobalEquation f U d hd ≫ pulledKernelInclusion f U.ι =
      schemeScalarEnd d := by
  rw [localKernelGlobalEquation, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, schemeKernelGenerator_comp_ι]

/-- Transport an actual map into a kernel pullback to the pullback along
the actual composite ambient morphism. -/
def kernelFrameRefinement (f : X ⟶ Y) (i : Z ⟶ Y) (g : W ⟶ Z)
    (s : _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback i).obj (schemeKernelIdeal f)) :
    _root_.SheafOfModules.unit W.ringCatSheaf ⟶
      (schemeModulePullback (g ≫ i)).obj (schemeKernelIdeal f) :=
  schemeModulePullbackFrame g s ≫ (schemeModulePullbackCompIso g i).hom.app _

/-- The common ambient inclusion is compatible with refinement, using
naturality and the original unit-composition normalization. -/
theorem kernelFrameRefinement_inclusion (f : X ⟶ Y) (i : Z ⟶ Y) (g : W ⟶ Z)
    (s : _root_.SheafOfModules.unit Z.ringCatSheaf ⟶
      (schemeModulePullback i).obj (schemeKernelIdeal f)) :
    kernelFrameRefinement f i g s ≫ pulledKernelInclusion f (g ≫ i) =
      schemeModulePullbackFrame g (s ≫ pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso g).hom := by
  simp only [kernelFrameRefinement, pulledKernelInclusion, Category.assoc]
  rw [← Category.assoc ((schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f)),
    ← (schemeModulePullbackCompIso g i).hom.naturality (schemeKernelIdealι f),
    Category.assoc, schemeModulePullbackCompIso_unit]
  simp only [schemeModulePullbackFrame, Functor.map_comp, Functor.comp_map, Category.assoc]

/-- Refinement of the original local equation map multiplies by the
actual pullback of its original coefficient. -/
theorem localKernelGlobalEquation_refinement_inclusion (f : X ⟶ Y) (U : Y.Opens)
    (d : Γ(U.toScheme, ⊤)) (hd : (f ∣_ U).appTop d = 0)
    (g : Z ⟶ U.toScheme) :
    kernelFrameRefinement f U.ι g (localKernelGlobalEquation f U d hd) ≫
        pulledKernelInclusion f (g ≫ U.ι) = schemeScalarEnd (g.appTop d) := by
  rw [kernelFrameRefinement_inclusion, localKernelGlobalEquation_inclusion]
  change ((schemeModulePullbackUnitIso g).inv ≫
    (schemeModulePullback g).map (schemeScalarEnd d)) ≫
      (schemeModulePullbackUnitIso g).hom = _
  rw [schemeModulePullbackUnitIso_inv_scalar, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Equal actual ambient morphisms induce the same normalized kernel
inclusion under the canonical equality transport. -/
theorem pulledKernelInclusion_congr (f : X ⟶ Y) {i j : Z ⟶ Y} (h : i = j) :
    (eqToIso (congrArg schemeModulePullback h)).hom.app (schemeKernelIdeal f) ≫
        pulledKernelInclusion f j = pulledKernelInclusion f i := by
  subst j
  simp

end KltDP.Geometry
