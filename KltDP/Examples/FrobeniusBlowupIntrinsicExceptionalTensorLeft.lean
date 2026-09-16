import KltDP.Examples.FrobeniusBlowupDifferentialIntrinsicLeft
import KltDP.Geometry.AffineDifferentialExteriorTildeIso
import KltDP.Geometry.IdealTensorFrameNormalization
import KltDP.Geometry.SchemeModuleStructureUnit

/-!
# The original intrinsic first-chart differential factors through the exceptional tensor

Use the proved inverses of the original native-to-intrinsic wedge maps. The
whole original determinant factorization then identifies the pullback of the
plane top-differential sheaf with the original exceptional ideal tensored with
the intrinsic top-differential sheaf on the original first Rees chart. Its
composite with the tensor of the actual ideal inclusion is the actual
intrinsic differential map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusBlowupIntrinsicExceptionalTensorLeft

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialMap FrobeniusBlowupDifferentialPullback
open FrobeniusBlowupDifferentialPullbackComp FrobeniusCoordinateDifferentialFrame
open FrobeniusReesChartDifferentialFrame FrobeniusBlowupDifferentialExceptionalSheaf
open FrobeniusBlowupIntrinsicDifferentialPullback FrobeniusBlowupDifferentialIntrinsicLeft

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartBaseAlgebra
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra
local instance chartMonoidal :
    MonoidalCategory (Spec (CommRingCat.of (reesChartRing k))).Modules :=
  Scheme.Modules.monoidalCategory _

/-- The original plane wedge map is invertible by its proved standard smoothness. -/
def planeNativeIso : (planeNativeModule k).tilde ≅ planeExterior (k := k) := by
  letI := FrobeniusCoordinateDifferentialFrame.plane_standardSmooth (k := k)
  exact AffineDifferentialExteriorTildeMap.standardSmoothIso k (planeRing k)

theorem planeNativeIso_hom : (planeNativeIso (k := k)).hom = planeNativeMap (k := k) := rfl

/-- The original Rees wedge map is invertible by the actual chart presentation. -/
def leftNativeIso : (leftNativeModule k).tilde ≅ leftExterior (k := k) := by
  letI := FrobeniusReesChartDifferentialFrame.chart_standardSmooth (k := k)
  exact AffineDifferentialExteriorTildeMap.standardSmoothIso k (reesChartRing k)

theorem leftNativeIso_hom : (leftNativeIso (k := k)).hom = leftNativeMap (k := k) := rfl

/-- The proved determinant identifies the actual intrinsic source with the original ideal. -/
def intrinsicExceptionalIso :
    (schemeModulePullback (planeChartMap (k := k))).obj (planeExterior (k := k)) ≅
      (exceptionalIdealModule k).tilde :=
  (schemeModulePullback (planeChartMap (k := k))).mapIso (planeNativeIso (k := k)).symm ≪≫
    planeChartExceptionalSheafIso (k := k)

def idealToIntrinsic : (exceptionalIdealModule k).tilde ⟶ leftExterior (k := k) :=
  exceptionalIdealTopSheafMap (k := k) ≫ leftNativeMap (k := k)

/-- The original whole intrinsic differential map factors through the actual ideal. -/
theorem intrinsicExceptionalIso_factor :
    (intrinsicExceptionalIso (k := k)).hom ≫ idealToIntrinsic (k := k) =
      leftMap (k := k) := by
  let F := schemeModulePullback (planeChartMap (k := k))
  change (F.map (planeNativeIso (k := k)).inv ≫
      (planeChartExceptionalSheafIso (k := k)).hom) ≫
        (exceptionalIdealTopSheafMap (k := k) ≫ leftNativeMap (k := k)) = _
  rw [Category.assoc, ← Category.assoc (planeChartExceptionalSheafIso (k := k)).hom,
    planeChartDifferentialSheafMap_factor, ← native_intrinsic_square]
  change F.map (planeNativeIso (k := k)).inv ≫
    F.map (planeNativeIso (k := k)).hom ≫ leftMap (k := k) = _
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- The actual ideal inclusion in the original Rees ring. -/
def idealInclusion :
    exceptionalIdealModule k ⟶ ModuleCat.of (reesChartRing k) (reesChartRing k) :=
  @ModuleCat.ofHom (reesChartRing k) _
    (exceptionalIdealModule k) (ModuleCat.of (reesChartRing k) (reesChartRing k))
    (exceptionalIdealModule k).isAddCommGroup (exceptionalIdealModule k).isModule
    (ModuleCat.of (reesChartRing k) (reesChartRing k)).isAddCommGroup
    (ModuleCat.of (reesChartRing k) (reesChartRing k)).isModule
    (FrobeniusBlowupDifferentialExceptionalImage.exceptionalIdeal k).subtype

/-- The inverse native frame cancels before taking tilde sheaves. -/
theorem exceptionalIdealToNative_frame :
    exceptionalIdealToNative (k := k) ≫
        (chartTopDifferentialEquiv (k := k)).toModuleIso.hom =
      idealInclusion (k := k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change chartTopDifferentialEquiv (k := k)
    ((chartTopDifferentialEquiv (k := k)).symm (r : reesChartRing k)) =
      (r : reesChartRing k)
  exact (chartTopDifferentialEquiv (k := k)).apply_symm_apply _

/-- The original structure module and the actual monoidal unit are compared by the accepted counit. -/
def structureUnitIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (reesChartRing k))).ringCatSheaf ≅
      𝟙_ (Spec (CommRingCat.of (reesChartRing k))).Modules :=
  SchemeModuleStructureUnit.iso (Spec (CommRingCat.of (reesChartRing k)))

/-- The original native coordinate frame with that same actual unit comparison. -/
def nativeFrameIso :
    (leftNativeModule k).tilde ≅ 𝟙_ (Spec (CommRingCat.of (reesChartRing k))).Modules :=
  chartTopDifferentialSheafIso (k := k) ≪≫ structureUnitIso (k := k)

/-- The original tilde ideal inclusion, with its original structure-sheaf unit. -/
def idealInclusionSheaf :
    (exceptionalIdealModule k).tilde ⟶ 𝟙_ (Spec (CommRingCat.of (reesChartRing k))).Modules :=
  AffineModuleTilde.map (idealInclusion (k := k)) ≫
    (AffineModuleTilde.unitIso (reesChartRing k)).hom ≫ (structureUnitIso (k := k)).hom

theorem exceptionalIdealTopSheafMap_structureFrame :
    exceptionalIdealTopSheafMap (k := k) ≫ (chartTopDifferentialSheafIso (k := k)).hom =
      AffineModuleTilde.map (idealInclusion (k := k)) ≫
        (AffineModuleTilde.unitIso (reesChartRing k)).hom := by
  change AffineModuleTilde.map (exceptionalIdealToNative (k := k)) ≫
    (AffineModuleTilde.map (chartTopDifferentialEquiv (k := k)).toModuleIso.hom ≫
      (AffineModuleTilde.unitIso (reesChartRing k)).hom) = _
  rw [← Category.assoc, ← AffineModuleTilde.map_comp, exceptionalIdealToNative_frame]

theorem exceptionalIdealTopSheafMap_frame :
    exceptionalIdealTopSheafMap (k := k) ≫ (nativeFrameIso (k := k)).hom =
      idealInclusionSheaf (k := k) := by
  change exceptionalIdealTopSheafMap (k := k) ≫
    ((chartTopDifferentialSheafIso (k := k)).hom ≫ (structureUnitIso (k := k)).hom) = _
  rw [← Category.assoc, exceptionalIdealTopSheafMap_structureFrame]
  rfl

/-- The intrinsic frame retains the original native coordinate wedge. -/
def intrinsicFrame :
    leftExterior (k := k) ≅ 𝟙_ (Spec (CommRingCat.of (reesChartRing k))).Modules :=
  (leftNativeIso (k := k)).symm ≪≫ nativeFrameIso (k := k)

theorem idealToIntrinsic_frame :
    idealToIntrinsic (k := k) ≫ (intrinsicFrame (k := k)).hom =
      idealInclusionSheaf (k := k) := by
  change (exceptionalIdealTopSheafMap (k := k) ≫ (leftNativeIso (k := k)).hom) ≫
    ((leftNativeIso (k := k)).inv ≫ (nativeFrameIso (k := k)).hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact exceptionalIdealTopSheafMap_frame (k := k)

theorem idealToIntrinsic_eq :
    idealToIntrinsic (k := k) =
      idealInclusionSheaf (k := k) ≫ (intrinsicFrame (k := k)).inv := by
  calc
    idealToIntrinsic (k := k) =
        (idealToIntrinsic (k := k) ≫ (intrinsicFrame (k := k)).hom) ≫
          (intrinsicFrame (k := k)).inv := by simp only [Category.assoc, Iso.hom_inv_id,
            Category.comp_id]
    _ = _ := by rw [idealToIntrinsic_frame]

/-- The actual original ideal inclusion tensored with the intrinsic top sheaf. -/
def exceptionalTensorInclusion :
    (exceptionalIdealModule k).tilde ⊗ leftExterior (k := k) ⟶ leftExterior (k := k) :=
  (idealInclusionSheaf (k := k) ▷ leftExterior (k := k)) ≫ (λ_ (leftExterior (k := k))).hom

/-- The normalized original determinant gives the actual local canonical tensor isomorphism. -/
def intrinsicExceptionalTensorIso :
    (schemeModulePullback (planeChartMap (k := k))).obj (planeExterior (k := k)) ≅
      (exceptionalIdealModule k).tilde ⊗ leftExterior (k := k) :=
  intrinsicExceptionalIso (k := k) ≪≫
    (IdealTensorFrameNormalization.frameIso
      (exceptionalIdealModule k).tilde (intrinsicFrame (k := k))).symm

/-- Equality of the entire original maps supplies the normalized chart input for global descent. -/
theorem intrinsicExceptionalTensorIso_factor :
    (intrinsicExceptionalTensorIso (k := k)).hom ≫ exceptionalTensorInclusion (k := k) =
      leftMap (k := k) := by
  change ((intrinsicExceptionalIso (k := k)).hom ≫
    (IdealTensorFrameNormalization.frameIso
      (exceptionalIdealModule k).tilde (intrinsicFrame (k := k))).inv) ≫
      ((idealInclusionSheaf (k := k) ▷ leftExterior (k := k)) ≫
        (λ_ (leftExterior (k := k))).hom) = _
  rw [Category.assoc, IdealTensorFrameNormalization.frameIso_inv_inclusion,
    ← idealToIntrinsic_eq]
  exact intrinsicExceptionalIso_factor (k := k)

end KltDP.Examples.FrobeniusBlowupIntrinsicExceptionalTensorLeft
