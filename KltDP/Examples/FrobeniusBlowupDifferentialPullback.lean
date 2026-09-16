import KltDP.Examples.FrobeniusBlowupDifferentialRestriction
import KltDP.Geometry.AffineModuleTildePullback
import KltDP.Geometry.ModuleRestrictionPullback

/-!
# Original differential maps as actual Rees-overlap restrictions

The original overlap ring maps define the actual two affine overlap
projections. Their proved localization properties make them open
immersions. The original named algebra structures are precisely the
toAlgebra structures of these maps, so the proved affine tilde/pullback
comparison applies to the original tensor modules without changing any
scalar action.

The resulting actual pullback and image-open restriction isomorphisms
retain the entire original top differential maps. Their transition
recovers the original overlap transition, including its coefficient on
canonical sections of every overlap open. No global glued differential
sheaf, canonical divisor, or numerical order is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialPullback

open FrobeniusBlowupContact FrobeniusBlowupDifferential FrobeniusBlowupDifferentialMap
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialOverlapFrame
open FrobeniusBlowupDifferentialRestriction
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra
local instance : Algebra k (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra
local instance : Algebra (reesChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra
local instance : Algebra (rightChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra
local instance :
    @IsScalarTower k (reesChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftTower (k := k)
local instance :
    @IsScalarTower k (rightChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapRightAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapRightTower (k := k)

/-- The original first affine overlap projection. -/
abbrev leftOverlapMap : Spec (CommRingCat.of (overlapRing k)) ⟶
    Spec (CommRingCat.of (reesChartRing k)) :=
  Spec.map (CommRingCat.ofHom (overlapLeft (k := k)))

/-- The original second affine overlap projection. -/
abbrev rightOverlapMap : Spec (CommRingCat.of (overlapRing k)) ⟶
    Spec (CommRingCat.of (rightChartRing k)) :=
  Spec.map (CommRingCat.ofHom (overlapRight (k := k)))

theorem leftOverlapMap_projection :
    (conormalOverlapIso (centerIdeal (k := k)) centerU centerV).hom ≫
      leftOverlapMap (k := k) =
        Limits.pullback.fst (chartι (centerIdeal (k := k)) centerU)
          (chartι (centerIdeal (k := k)) centerV) :=
  conormalOverlapIso_hom_left (centerIdeal (k := k)) centerU centerV

theorem rightOverlapMap_projection :
    (conormalOverlapIso (centerIdeal (k := k)) centerU centerV).hom ≫
      rightOverlapMap (k := k) =
        Limits.pullback.snd (chartι (centerIdeal (k := k)) centerU)
          (chartι (centerIdeal (k := k)) centerV) :=
  conormalOverlapIso_hom_right (centerIdeal (k := k)) centerU centerV

instance leftOverlapMap_isOpenImmersion : IsOpenImmersion (leftOverlapMap (k := k)) := by
  letI : IsLocalization.Away (chartFraction (centerIdeal (k := k)) centerU centerV)
      (overlapRing k) := conormalOverlapLeft_isLocalization (centerIdeal (k := k)) centerU centerV
  exact IsOpenImmersion.of_isLocalization (chartFraction (centerIdeal (k := k)) centerU centerV)

instance rightOverlapMap_isOpenImmersion : IsOpenImmersion (rightOverlapMap (k := k)) := by
  letI : IsLocalization.Away (chartFraction (centerIdeal (k := k)) centerV centerU)
      (overlapRing k) := conormalOverlapRight_isLocalization (centerIdeal (k := k)) centerU centerV
  exact IsOpenImmersion.of_isLocalization (chartFraction (centerIdeal (k := k)) centerV centerU)

/-- The first native top-differential module, before any scalar extension. -/
abbrev leftNativeModule (k : Type u) [Field k] : ModuleCat (reesChartRing k) :=
  ModuleCat.of (reesChartRing k) (⋀[reesChartRing k]^2 (ChartDifferential k))

/-- The second native top-differential module, before any scalar extension. -/
abbrev rightNativeModule (k : Type u) [Field k] : ModuleCat (rightChartRing k) :=
  ModuleCat.of (rightChartRing k) (⋀[rightChartRing k]^2 (RightDifferential k))

/-- The affine comparison uses exactly the original first overlap algebra. -/
def leftPullbackScalarIso :
    (schemeModulePullback (leftOverlapMap (k := k))).obj (leftNativeModule k).tilde ≅
      (leftModule k).tilde :=
  AffineModuleTilde.pullbackIso (overlapLeft (k := k)) (leftNativeModule k)

/-- The affine comparison uses exactly the original second overlap algebra. -/
def rightPullbackScalarIso :
    (schemeModulePullback (rightOverlapMap (k := k))).obj (rightNativeModule k).tilde ≅
      (rightModule k).tilde :=
  AffineModuleTilde.pullbackIso (overlapRight (k := k)) (rightNativeModule k)

/-- Actual first-chart pullback followed by the original differential localization. -/
def leftPullbackTopIso :
    (schemeModulePullback (leftOverlapMap (k := k))).obj (leftNativeModule k).tilde ≅
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).tilde :=
  leftPullbackScalarIso (k := k) ≪≫ leftTopSheafIso (k := k)

/-- Actual second-chart pullback followed by the original differential localization. -/
def rightPullbackTopIso :
    (schemeModulePullback (rightOverlapMap (k := k))).obj (rightNativeModule k).tilde ≅
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).tilde :=
  rightPullbackScalarIso (k := k) ≪≫ rightTopSheafIso (k := k)

/-- The first comparison recovers the entire original differential map. -/
theorem leftPullbackTopIso_recover :
    (leftPullbackScalarIso (k := k)).inv ≫ (leftPullbackTopIso (k := k)).hom =
      AffineModuleTilde.map (M := leftModule k)
        (N := FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
        (@ModuleCat.ofHom (overlapRing k) _ (leftModule k)
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
          (leftModule k).isAddCommGroup (leftModule k).isModule
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
          (leftTopMap (k := k))) := by
  simp only [leftPullbackTopIso, Iso.trans_hom, Iso.inv_hom_id_assoc, leftTopSheafIso_hom]

/-- The second comparison recovers the entire original differential map. -/
theorem rightPullbackTopIso_recover :
    (rightPullbackScalarIso (k := k)).inv ≫ (rightPullbackTopIso (k := k)).hom =
      AffineModuleTilde.map (M := rightModule k)
        (N := FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
        (@ModuleCat.ofHom (overlapRing k) _ (rightModule k)
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
          (rightModule k).isAddCommGroup (rightModule k).isModule
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
          (rightTopMap (k := k))) := by
  simp only [rightPullbackTopIso, Iso.trans_hom, Iso.inv_hom_id_assoc, rightTopSheafIso_hom]

/-- Actual image-open restriction, compared with the original first tensor module. -/
def leftRestrictionScalarIso :
    (SchemeModuleRestriction.restriction (leftOverlapMap (k := k))).obj
        (leftNativeModule k).tilde ≅ (leftModule k).tilde :=
  (SchemeModuleRestriction.restrictionIsoPullback (leftOverlapMap (k := k))).app
    (leftNativeModule k).tilde ≪≫ leftPullbackScalarIso (k := k)

/-- Actual image-open restriction, compared with the original second tensor module. -/
def rightRestrictionScalarIso :
    (SchemeModuleRestriction.restriction (rightOverlapMap (k := k))).obj
        (rightNativeModule k).tilde ≅ (rightModule k).tilde :=
  (SchemeModuleRestriction.restrictionIsoPullback (rightOverlapMap (k := k))).app
    (rightNativeModule k).tilde ≪≫ rightPullbackScalarIso (k := k)

/-- Restriction of the first native differential sheaf is the native overlap sheaf. -/
def leftRestrictionTopIso :
    (SchemeModuleRestriction.restriction (leftOverlapMap (k := k))).obj
        (leftNativeModule k).tilde ≅
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).tilde :=
  leftRestrictionScalarIso (k := k) ≪≫ leftTopSheafIso (k := k)

/-- Restriction of the second native differential sheaf is the same overlap sheaf. -/
def rightRestrictionTopIso :
    (SchemeModuleRestriction.restriction (rightOverlapMap (k := k))).obj
        (rightNativeModule k).tilde ≅
      (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).tilde :=
  rightRestrictionScalarIso (k := k) ≪≫ rightTopSheafIso (k := k)

theorem leftRestrictionTopIso_recover :
    (leftRestrictionScalarIso (k := k)).inv ≫ (leftRestrictionTopIso (k := k)).hom =
      AffineModuleTilde.map (M := leftModule k)
        (N := FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
        (@ModuleCat.ofHom (overlapRing k) _ (leftModule k)
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
          (leftModule k).isAddCommGroup (leftModule k).isModule
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
          (leftTopMap (k := k))) := by
  simp only [leftRestrictionTopIso, Iso.trans_hom, Iso.inv_hom_id_assoc, leftTopSheafIso_hom]

theorem rightRestrictionTopIso_recover :
    (rightRestrictionScalarIso (k := k)).inv ≫ (rightRestrictionTopIso (k := k)).hom =
      AffineModuleTilde.map (M := rightModule k)
        (N := FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
        (@ModuleCat.ofHom (overlapRing k) _ (rightModule k)
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k)
          (rightModule k).isAddCommGroup (rightModule k).isModule
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isAddCommGroup
          (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).isModule
          (rightTopMap (k := k))) := by
  simp only [rightRestrictionTopIso, Iso.trans_hom, Iso.inv_hom_id_assoc, rightTopSheafIso_hom]

/-- The transition between the two actual restricted differential sheaves. -/
def restrictionTransition :
    (SchemeModuleRestriction.restriction (leftOverlapMap (k := k))).obj
        (leftNativeModule k).tilde ≅
      (SchemeModuleRestriction.restriction (rightOverlapMap (k := k))).obj
        (rightNativeModule k).tilde :=
  leftRestrictionTopIso (k := k) ≪≫ (rightRestrictionTopIso (k := k)).symm

theorem restrictionTransition_right :
    (restrictionTransition (k := k)).hom ≫ (rightRestrictionTopIso (k := k)).hom =
      (leftRestrictionTopIso (k := k)).hom := by
  simp only [restrictionTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Under the explicit affine comparisons, the actual restriction transition
is the entire original tilde transition, rather than only a frame equality. -/
theorem restrictionTransition_comparison :
    (leftRestrictionScalarIso (k := k)).inv ≫ (restrictionTransition (k := k)).hom ≫
        (rightRestrictionScalarIso (k := k)).hom =
      (chartTransitionSheafIso (k := k)).hom := by
  apply (cancel_mono (rightTopSheafIso (k := k)).hom).mp
  calc
    ((leftRestrictionScalarIso (k := k)).inv ≫ (restrictionTransition (k := k)).hom ≫
        (rightRestrictionScalarIso (k := k)).hom) ≫ (rightTopSheafIso (k := k)).hom =
      (leftRestrictionScalarIso (k := k)).inv ≫
        ((restrictionTransition (k := k)).hom ≫ (rightRestrictionTopIso (k := k)).hom) := by
          simp only [rightRestrictionTopIso, Iso.trans_hom, Category.assoc]
    _ = (leftRestrictionScalarIso (k := k)).inv ≫ (leftRestrictionTopIso (k := k)).hom :=
      congrArg (fun f => (leftRestrictionScalarIso (k := k)).inv ≫ f)
        (restrictionTransition_right (k := k))
    _ = (leftTopSheafIso (k := k)).hom := by
      simp only [leftRestrictionTopIso, Iso.trans_hom, Iso.inv_hom_id_assoc]
    _ = (chartTransitionSheafIso (k := k)).hom ≫ (rightTopSheafIso (k := k)).hom :=
      (chartTransitionSheafIso_hom_right (k := k)).symm

/-- On every actual overlap open, the compared restriction transition
retains the original coefficient minus T. -/
theorem restrictionTransition_coordinate (U : Opens (PrimeSpectrum (overlapRing k))) :
    ((leftRestrictionScalarIso (k := k)).inv ≫ (restrictionTransition (k := k)).hom ≫
        (rightRestrictionScalarIso (k := k)).hom).val.app (op U)
      (ModuleCat.Tilde.toOpen (leftModule k) U
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))) =
      ModuleCat.Tilde.toOpen (rightModule k) U
        ((-overlapT (k := k)) • (1 ⊗ₜ[rightChartRing k] rightChartForm (k := k))) := by
  exact (congrArg
    (fun f : (leftModule k).tilde ⟶ (rightModule k).tilde =>
      f.val.app (op U) (ModuleCat.Tilde.toOpen (leftModule k) U
        (1 ⊗ₜ[reesChartRing k] chartCoordinateTopForm (k := k))))
    (restrictionTransition_comparison (k := k))).trans
      (chartTransitionSheafIso_coordinate (k := k) U)

end KltDP.Examples.FrobeniusBlowupDifferentialPullback
