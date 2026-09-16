import KltDP.Geometry.SchemeKernelTensorInclusion
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SchemeModulePullbackTensorNaturality
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.InvertibleTensorExact
import KltDP.Geometry.RationalTreePicardPulledSectionTransport

/-!
# Actual vanishing of a tensor ideal inclusion after pullback

The adjunction sends the original pulled-back kernel inclusion, followed
by the canonical structure-module comparison, to the original kernel
condition. Hence that original pulled-back map is zero. The naturality
of the accepted tensor comparison carries this equation to the original
line-bundle tensor inclusion. Its actual image sections therefore pull
back to zero, including on the residue-field scheme of a chosen point.

No section-existence, coherence, flatness, or local-epi witness is assumed.
The section producer and its later effective-Cartier degree comparison
are separate consumers of these actual morphism equations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.SchemeKernelTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}}

local instance (Z : Scheme.{u}) : MonoidalCategory Z.Modules :=
  Scheme.Modules.monoidalCategory Z

local instance (Z : Scheme.{u}) : SymmetricCategory Z.Modules :=
  Scheme.Modules.symmetricCategory Z

/-- The actual kernel inclusion becomes the zero morphism after pullback
along the same original scheme morphism. -/
theorem pullback_kernelIdealι_eq_zero (f : X ⟶ Y) :
    (schemeModulePullback f).map (schemeKernelIdealι f) = 0 := by
  apply (cancel_mono (schemeModulePullbackUnitIso f).hom).1
  rw [zero_comp]
  change (schemeModulePullback f).map (schemeKernelIdealι f) ≫
    schemeModulePullbackUnitHom f = 0
  apply ((_root_.SheafOfModules.pullbackPushforwardAdjunction
    (schemeRingSheafHom f)).homEquiv _ _).injective
  have hn : (_root_.SheafOfModules.pullbackPushforwardAdjunction
        (schemeRingSheafHom f)).homEquiv _ _
      ((schemeModulePullback f).map (schemeKernelIdealι f) ≫
        schemeModulePullbackUnitHom f) =
      schemeKernelIdealι f ≫
        (_root_.SheafOfModules.pullbackPushforwardAdjunction
          (schemeRingSheafHom f)).homEquiv _ _ (schemeModulePullbackUnitHom f) :=
    (_root_.SheafOfModules.pullbackPushforwardAdjunction
      (schemeRingSheafHom f)).homEquiv_naturality_left
        (schemeKernelIdealι f) (schemeModulePullbackUnitHom f)
  rw [hn, schemeModulePullbackUnitHom_adjunction, schemeKernelIdealι_comp,
    Adjunction.homEquiv_unit, CategoryTheory.Functor.map_zero, comp_zero]

/-- Left tensoring by an actual invertible sheaf preserves zero maps,
using the accepted inverse and the original symmetric braiding. -/
theorem tensorLeft_preservesZeroMorphisms (L : InvertibleSheaf Y) :
    (tensorLeft L.obj).PreservesZeroMorphisms := by
  letI := L.tensorRight_preservesZeroMorphisms
  exact CategoryTheory.Functor.preservesZeroMorphisms_of_iso
    (BraidedCategory.tensorLeftIsoTensorRight L.obj).symm

set_option maxHeartbeats 800000 in
/-- Pullback kills the original line-bundle tensor ideal inclusion. -/
theorem pullback_inclusion_eq_zero (f : X ⟶ Y) (L : InvertibleSheaf Y) :
    (schemeModulePullback f).map (inclusion f L.obj) = 0 := by
  letI : (tensorLeft ((schemeModulePullback f).obj L.obj)).PreservesZeroMorphisms :=
    tensorLeft_preservesZeroMorphisms (pullbackInvertibleSheaf f L)
  have hz : (𝟙 ((schemeModulePullback f).obj L.obj) ⊗
      (0 : (schemeModulePullback f).obj (schemeKernelIdeal f) ⟶
        (schemeModulePullback f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf))) = 0 := by
    rw [id_tensorHom]
    exact (tensorLeft ((schemeModulePullback f).obj L.obj)).map_zero _ _
  have hn := schemeModulePullbackTensorIso_natural f (𝟙 L.obj) (schemeKernelIdealι f)
  rw [CategoryTheory.Functor.map_id, pullback_kernelIdealι_eq_zero, hz, comp_zero] at hn
  have ht : (schemeModulePullback f).map (𝟙 L.obj ⊗ schemeKernelIdealι f) = 0 := by
    apply (cancel_mono (schemeModulePullbackTensorIso f L.obj
      (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom).1
    simpa only [zero_comp] using hn
  change (schemeModulePullback f).map
    ((𝟙 L.obj ⊗ schemeKernelIdealι f) ≫ (actualUnitRightIso L.obj).hom) = 0
  rw [CategoryTheory.Functor.map_comp, ht, zero_comp]

/-- Every original image section pulls back to zero, as an actual section
of the original pulled-back line bundle on the original preimage open. -/
theorem pulledSection_inclusion_eq_zero (f : X ⟶ Y) (L : InvertibleSheaf Y)
    (U : Y.Opens) (s : (L.obj ⊗ schemeKernelIdeal f).val.obj (op U)) :
    RationalTreePicard.pulledSection f L.obj U
      ((inclusion f L.obj).val.app (op U) s) = 0 := by
  rw [← RationalTreePicard.pullback_map_val_app_pulledSection,
    pullback_inclusion_eq_zero]
  rfl

end KltDP.Geometry.SchemeKernelTensor
