import KltDP.Examples.FrobeniusBlowupDifferentialIntrinsicRight
import KltDP.Geometry.AffineDifferentialExteriorTildeIso
import KltDP.Geometry.IdealTensorFrameNormalization
import KltDP.Geometry.SchemeModuleStructureUnit

/-!
# The original intrinsic complementary-chart differential factors through the exceptional tensor

Use the proved inverses of the original native-to-intrinsic wedge maps. The
whole original determinant factorization then identifies the pullback of the
plane top-differential sheaf with the original exceptional ideal tensored with
the intrinsic top-differential sheaf on the original complementary Rees chart. Its
composite with the tensor of the actual ideal inclusion is the actual
intrinsic differential map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusBlowupIntrinsicExceptionalTensorRight

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialRightMap FrobeniusBlowupDifferentialPullback
open FrobeniusBlowupDifferentialPullbackComp FrobeniusCoordinateDifferentialFrame
open FrobeniusBlowupDifferentialRightFrame FrobeniusBlowupDifferentialRightExceptionalSheaf
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialOverlapFrame
open FrobeniusBlowupIntrinsicDifferentialRightPullback FrobeniusBlowupDifferentialIntrinsicRight

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (rightChartRing k) :=
  FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra
local instance chartMonoidal :
    MonoidalCategory (Spec (CommRingCat.of (rightChartRing k))).Modules :=
  Scheme.Modules.monoidalCategory _

/-- The original plane wedge map is invertible by its proved standard smoothness. -/
def planeNativeIso : (planeNativeModule k).tilde ≅ planeExterior (k := k) := by
  letI := FrobeniusCoordinateDifferentialFrame.plane_standardSmooth (k := k)
  exact AffineDifferentialExteriorTildeMap.standardSmoothIso k (planeRing k)

theorem planeNativeIso_hom : (planeNativeIso (k := k)).hom = planeNativeMap (k := k) := rfl

/-- The original Rees wedge map is invertible by the actual chart presentation. -/
def rightNativeIso : (rightNativeModule k).tilde ≅ rightExterior (k := k) := by
  letI := FrobeniusBlowupDifferentialOverlapFrame.rightChart_standardSmooth (k := k)
  exact AffineDifferentialExteriorTildeMap.standardSmoothIso k (rightChartRing k)

theorem rightNativeIso_hom : (rightNativeIso (k := k)).hom = rightNativeMap (k := k) := rfl

/-- The proved determinant identifies the actual intrinsic source with the original ideal. -/
def intrinsicExceptionalIso :
    (schemeModulePullback (planeRightMap (k := k))).obj (planeExterior (k := k)) ≅
      (rightExceptionalIdealModule k).tilde :=
  (schemeModulePullback (planeRightMap (k := k))).mapIso (planeNativeIso (k := k)).symm ≪≫
    planeRightExceptionalSheafIso (k := k)

def idealToIntrinsic : (rightExceptionalIdealModule k).tilde ⟶ rightExterior (k := k) :=
  rightExceptionalIdealTopSheafMap (k := k) ≫ rightNativeMap (k := k)

/-- The original whole intrinsic differential map factors through the actual ideal. -/
theorem intrinsicExceptionalIso_factor :
    (intrinsicExceptionalIso (k := k)).hom ≫ idealToIntrinsic (k := k) =
      rightMap (k := k) := by
  let F := schemeModulePullback (planeRightMap (k := k))
  change (F.map (planeNativeIso (k := k)).inv ≫
      (planeRightExceptionalSheafIso (k := k)).hom) ≫
        (rightExceptionalIdealTopSheafMap (k := k) ≫ rightNativeMap (k := k)) = _
  rw [Category.assoc, ← Category.assoc (planeRightExceptionalSheafIso (k := k)).hom,
    planeRightDifferentialSheafMap_factor, ← native_intrinsic_square]
  change F.map (planeNativeIso (k := k)).inv ≫
    F.map (planeNativeIso (k := k)).hom ≫ rightMap (k := k) = _
  rw [← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- The actual ideal inclusion in the original Rees ring. -/
def idealInclusion :
    rightExceptionalIdealModule k ⟶ ModuleCat.of (rightChartRing k) (rightChartRing k) :=
  @ModuleCat.ofHom (rightChartRing k) _
    (rightExceptionalIdealModule k) (ModuleCat.of (rightChartRing k) (rightChartRing k))
    (rightExceptionalIdealModule k).isAddCommGroup (rightExceptionalIdealModule k).isModule
    (ModuleCat.of (rightChartRing k) (rightChartRing k)).isAddCommGroup
    (ModuleCat.of (rightChartRing k) (rightChartRing k)).isModule
    (FrobeniusBlowupDifferentialRightExceptionalImage.rightExceptionalIdeal k).subtype

/-- The inverse native frame cancels before taking tilde sheaves. -/
theorem rightExceptionalIdealToNative_frame :
    rightExceptionalIdealToNative (k := k) ≫
        (rightTopDifferentialEquiv (k := k)).toModuleIso.hom =
      idealInclusion (k := k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change rightTopDifferentialEquiv (k := k)
    ((rightTopDifferentialEquiv (k := k)).symm (r : rightChartRing k)) =
      (r : rightChartRing k)
  exact (rightTopDifferentialEquiv (k := k)).apply_symm_apply _

/-- The original structure module and the actual monoidal unit are compared by the accepted counit. -/
def structureUnitIso :
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (rightChartRing k))).ringCatSheaf ≅
      𝟙_ (Spec (CommRingCat.of (rightChartRing k))).Modules :=
  SchemeModuleStructureUnit.iso (Spec (CommRingCat.of (rightChartRing k)))

/-- The original native coordinate frame with that same actual unit comparison. -/
def nativeFrameIso :
    (rightNativeModule k).tilde ≅ 𝟙_ (Spec (CommRingCat.of (rightChartRing k))).Modules :=
  rightTopDifferentialSheafIso (k := k) ≪≫ structureUnitIso (k := k)

/-- The original tilde ideal inclusion, with its original structure-sheaf unit. -/
def idealInclusionSheaf :
    (rightExceptionalIdealModule k).tilde ⟶ 𝟙_ (Spec (CommRingCat.of (rightChartRing k))).Modules :=
  AffineModuleTilde.map (idealInclusion (k := k)) ≫
    (AffineModuleTilde.unitIso (rightChartRing k)).hom ≫ (structureUnitIso (k := k)).hom

theorem rightExceptionalIdealTopSheafMap_structureFrame :
    rightExceptionalIdealTopSheafMap (k := k) ≫ (rightTopDifferentialSheafIso (k := k)).hom =
      AffineModuleTilde.map (idealInclusion (k := k)) ≫
        (AffineModuleTilde.unitIso (rightChartRing k)).hom := by
  change AffineModuleTilde.map (rightExceptionalIdealToNative (k := k)) ≫
    (AffineModuleTilde.map (rightTopDifferentialEquiv (k := k)).toModuleIso.hom ≫
      (AffineModuleTilde.unitIso (rightChartRing k)).hom) = _
  rw [← Category.assoc, ← AffineModuleTilde.map_comp, rightExceptionalIdealToNative_frame]

theorem rightExceptionalIdealTopSheafMap_frame :
    rightExceptionalIdealTopSheafMap (k := k) ≫ (nativeFrameIso (k := k)).hom =
      idealInclusionSheaf (k := k) := by
  change rightExceptionalIdealTopSheafMap (k := k) ≫
    ((rightTopDifferentialSheafIso (k := k)).hom ≫ (structureUnitIso (k := k)).hom) = _
  rw [← Category.assoc, rightExceptionalIdealTopSheafMap_structureFrame]
  rfl

/-- The intrinsic frame retains the original native coordinate wedge. -/
def intrinsicFrame :
    rightExterior (k := k) ≅ 𝟙_ (Spec (CommRingCat.of (rightChartRing k))).Modules :=
  (rightNativeIso (k := k)).symm ≪≫ nativeFrameIso (k := k)

theorem idealToIntrinsic_frame :
    idealToIntrinsic (k := k) ≫ (intrinsicFrame (k := k)).hom =
      idealInclusionSheaf (k := k) := by
  change (rightExceptionalIdealTopSheafMap (k := k) ≫ (rightNativeIso (k := k)).hom) ≫
    ((rightNativeIso (k := k)).inv ≫ (nativeFrameIso (k := k)).hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact rightExceptionalIdealTopSheafMap_frame (k := k)

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
    (rightExceptionalIdealModule k).tilde ⊗ rightExterior (k := k) ⟶ rightExterior (k := k) :=
  (idealInclusionSheaf (k := k) ▷ rightExterior (k := k)) ≫ (λ_ (rightExterior (k := k))).hom

/-- The normalized original determinant gives the actual local canonical tensor isomorphism. -/
def intrinsicExceptionalTensorIso :
    (schemeModulePullback (planeRightMap (k := k))).obj (planeExterior (k := k)) ≅
      (rightExceptionalIdealModule k).tilde ⊗ rightExterior (k := k) :=
  intrinsicExceptionalIso (k := k) ≪≫
    (IdealTensorFrameNormalization.frameIso
      (rightExceptionalIdealModule k).tilde (intrinsicFrame (k := k))).symm

/-- Equality of the entire original maps supplies the normalized chart input for global descent. -/
theorem intrinsicExceptionalTensorIso_factor :
    (intrinsicExceptionalTensorIso (k := k)).hom ≫ exceptionalTensorInclusion (k := k) =
      rightMap (k := k) := by
  change ((intrinsicExceptionalIso (k := k)).hom ≫
    (IdealTensorFrameNormalization.frameIso
      (rightExceptionalIdealModule k).tilde (intrinsicFrame (k := k))).inv) ≫
      ((idealInclusionSheaf (k := k) ▷ rightExterior (k := k)) ≫
        (λ_ (rightExterior (k := k))).hom) = _
  rw [Category.assoc, IdealTensorFrameNormalization.frameIso_inv_inclusion,
    ← idealToIntrinsic_eq]
  exact intrinsicExceptionalIso_factor (k := k)

end KltDP.Examples.FrobeniusBlowupIntrinsicExceptionalTensorRight
