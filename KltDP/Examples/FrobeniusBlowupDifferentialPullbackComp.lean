import KltDP.Examples.FrobeniusBlowupDifferentialPullback
import KltDP.Geometry.AffineModuleTildePullbackComp

/-!
# The original plane-chart-overlap differential pullback square

The two Rees structure maps compose to the original overlap structure
map by the proved homogeneous-localization formula. Their equality is
used explicitly to transport scalar extension and actual scheme pullback.
The pinned extension-composition map is then identified with the original
tensor cancellation inverse on the whole module.

The final square uses the original chart differential and the original
overlap top-differential map. No replacement algebra action, determinant
comparison premise, or global differential descent is used.

Reuse: pinned ModuleCat.ChangeOfRings supplies extendScalarsComp,
extendScalarsComp_hom_app_one_tmul and ExtendScalars.hom_ext. The original
cancelBaseChange inverse is pinned TensorProduct/Tower.lean:419-437.
The generic affine comparison coherence is the already proved project
AffineModuleTildePullbackComp. Tiny equality transports below are proved
by equality elimination, retaining both explicitly indexed tensors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Examples.FrobeniusBlowupDifferentialPullbackComp

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A C : Type u} [CommRing A] [CommRing C]

private theorem extendScalars_eqToIso_inv_tmul {f g : A →+* C} (h : f = g)
    (M : ModuleCat.{u} A) (c : C) (m : M) :
    (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M) h)).inv
        (c ⊗ₜ[A,g] m) = c ⊗ₜ[A,f] m := by
  subst g
  rfl

private theorem pullbackIso_ringEq_inv {f g : A →+* C} (h : f = g)
    (M : ModuleCat.{u} A) :
    (eqToIso (congrArg (fun q : A →+* C =>
      (KltDP.Geometry.schemeModulePullback (Spec.map (CommRingCat.ofHom q))).obj M.tilde)
        h)).hom ≫
      (KltDP.Geometry.AffineModuleTilde.pullbackIso g M).hom ≫
      KltDP.Geometry.AffineModuleTilde.map
        (eqToIso (congrArg (fun q => (ModuleCat.extendScalars q).obj M) h)).inv =
      (KltDP.Geometry.AffineModuleTilde.pullbackIso f M).hom := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, KltDP.Geometry.AffineModuleTilde.map_id, Category.comp_id]

open FrobeniusBlowupContact FrobeniusBlowupDifferential FrobeniusBlowupDifferentialMap
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialOverlapFrame
open FrobeniusBlowupDifferentialRestriction FrobeniusBlowupDifferentialPullback
open KltDP.Geometry KltDP.Geometry.AffineBlowup

/-- Transport the existing affine composition comparison along equality of
ring maps before specializing any actual chart or differential module. -/
private theorem pullbackIso_comp_ringEq {B : Type u} [CommRing B]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (M : ModuleCat.{u} A) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map
        (AffineModuleTilde.pullbackIso φ M).hom ≫
      (AffineModuleTilde.pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom =
    ((schemeModulePullbackCompIso
        (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))).app M.tilde ≪≫
      eqToIso (congrArg (fun f => (schemeModulePullback f).obj M.tilde)
        (AffineModuleTilde.specMap_comp_eq φ ψ)) ≪≫
      eqToIso (congrArg (fun q : A →+* C =>
        (schemeModulePullback (Spec.map (CommRingCat.ofHom q))).obj M.tilde) h)).hom ≫
      (AffineModuleTilde.pullbackIso χ M).hom ≫
      AffineModuleTilde.map
        ((eqToIso (congrArg (fun q : A →+* C =>
            (ModuleCat.extendScalars q).obj M) h)).symm ≪≫
          (ModuleCat.extendScalarsComp φ ψ).app M).hom := by
  subst χ
  simpa only [eqToIso_refl, Iso.trans_hom, Iso.symm_hom,
    Iso.refl_hom, Iso.refl_inv, Iso.app_hom, Category.id_comp, Category.comp_id,
    Category.assoc] using
    AffineModuleTilde.pullbackIso_comp φ ψ M

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartBaseAlgebra
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra
local instance : Algebra (planeRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra
local instance : Algebra k (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra
local instance : Algebra (reesChartRing k) (overlapRing k) :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra
local instance :
    @IsScalarTower k (planeRing k) (reesChartRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialMap.chartBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialMap.chartFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialMap.chartScalarTower (k := k)
local instance :
    @IsScalarTower k (planeRing k) (overlapRing k)
      (inferInstance : SMul k (planeRing k))
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapPlaneTower (k := k)
local instance :
    @IsScalarTower k (reesChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialOverlap.leftFieldAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapFieldAlgebra (k := k)).toSMul :=
  FrobeniusBlowupDifferentialOverlap.overlapLeftTower (k := k)
local instance :
    @IsScalarTower (planeRing k) (reesChartRing k) (overlapRing k)
      (FrobeniusBlowupDifferentialMap.chartBaseAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k)).toSMul
      (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)).toSMul :=
  @IsScalarTower.of_algebraMap_eq (planeRing k) (reesChartRing k) (overlapRing k)
    _ _ _ (FrobeniusBlowupDifferentialMap.chartBaseAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.overlapLeftAlgebra (k := k))
    (FrobeniusBlowupDifferentialOverlap.overlapPlaneAlgebra (k := k)) fun r =>
      (conormalOverlapLeft_baseMap (centerIdeal (k := k)) centerU centerV r).symm

/-- The composite is equal to the original overlap map, by its actual
homogeneous-localization restriction formula. -/
theorem left_comp_baseMap :
    (overlapLeft (k := k)).comp (baseMap (k := k)) = overlapBaseMap (k := k) :=
  RingHom.ext (conormalOverlapLeft_baseMap (centerIdeal (k := k)) centerU centerV)

/-- The original top-differential module on the polynomial plane. -/
abbrev planeNativeModule (k : Type u) [Field k] : ModuleCat (planeRing k) :=
  ModuleCat.of (planeRing k) (⋀[planeRing k]^2 (PlaneDifferential k))

/-- Original scalar extension of the plane module to the first Rees chart. -/
abbrev planeChartModule (k : Type u) [Field k] : ModuleCat (reesChartRing k) :=
  ModuleCat.of (reesChartRing k)
    (reesChartRing k ⊗[planeRing k] (⋀[planeRing k]^2 (PlaneDifferential k)))

/-- The iterated extension retains the original plane and chart actions. -/
abbrev iteratedPlaneModule (k : Type u) [Field k] : ModuleCat (overlapRing k) :=
  (ModuleCat.extendScalars (overlapLeft (k := k))).obj (planeChartModule k)

/-- Transport from the original overlap algebra, then use the pinned
composition isomorphism for the original two ring maps. -/
def originalExtensionCompIso : baseModule k ≅ iteratedPlaneModule k :=
  (eqToIso (congrArg
    (fun q : planeRing k →+* overlapRing k =>
      (ModuleCat.extendScalars q).obj (planeNativeModule k)) left_comp_baseMap)).symm ≪≫
    (ModuleCat.extendScalarsComp (baseMap (k := k)) (overlapLeft (k := k))).app
      (planeNativeModule k)

/-- The entire canonical extension comparison is the original tensor
cancellation inverse, with its original algebra tower. -/
theorem originalExtensionCompIso_hom_cancel :
    (originalExtensionCompIso (k := k)).hom =
      @ModuleCat.ofHom (overlapRing k) _ (baseModule k) (iteratedPlaneModule k)
        (baseModule k).isAddCommGroup (baseModule k).isModule
        (iteratedPlaneModule k).isAddCommGroup (iteratedPlaneModule k).isModule
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          (planeRing k) (reesChartRing k) (overlapRing k) (overlapRing k)
          (⋀[planeRing k]^2 (PlaneDifferential k))).symm.toLinearMap := by
  apply ModuleCat.ExtendScalars.hom_ext (f := overlapBaseMap (k := k))
    (M := planeNativeModule k)
  intro ω
  have ht := extendScalars_eqToIso_inv_tmul left_comp_baseMap (planeNativeModule k) 1 ω
  have hc := ModuleCat.extendScalarsComp_hom_app_one_tmul (baseMap (k := k))
    (overlapLeft (k := k)) (planeNativeModule k) ω
  exact (congrArg
    (fun z : (ModuleCat.extendScalars
        ((overlapLeft (k := k)).comp (baseMap (k := k)))).obj (planeNativeModule k) =>
      ((ModuleCat.extendScalarsComp (baseMap (k := k))
        (overlapLeft (k := k))).hom.app (planeNativeModule k)).hom z) ht).trans hc

/-- The actual extended chart differential is precisely the previously
defined original plane-to-chart-to-overlap map on the whole module. -/
theorem originalExtensionCompIso_differential :
    (originalExtensionCompIso (k := k)).hom ≫
      (ModuleCat.extendScalars (overlapLeft (k := k))).map
        (@ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
          (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
          (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
          (planeChartTopMap (k := k)) : planeChartModule k ⟶ leftNativeModule k) =
      (@ModuleCat.ofHom (overlapRing k) _ (baseModule k) (leftModule k)
        (baseModule k).isAddCommGroup (baseModule k).isModule
        (leftModule k).isAddCommGroup (leftModule k).isModule
        (planeChartOverlapMap (k := k)) : baseModule k ⟶ leftModule k) := by
  calc
    _ = @ModuleCat.ofHom (overlapRing k) _ (baseModule k) (iteratedPlaneModule k)
          (baseModule k).isAddCommGroup (baseModule k).isModule
          (iteratedPlaneModule k).isAddCommGroup (iteratedPlaneModule k).isModule
          (TensorProduct.AlgebraTensorModule.cancelBaseChange
            (planeRing k) (reesChartRing k) (overlapRing k) (overlapRing k)
            (⋀[planeRing k]^2 (PlaneDifferential k))).symm.toLinearMap ≫
        (ModuleCat.extendScalars (overlapLeft (k := k))).map
          (@ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
          (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
          (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
          (planeChartTopMap (k := k)) : planeChartModule k ⟶ leftNativeModule k) :=
      congrArg (fun f : baseModule k ⟶ iteratedPlaneModule k => f ≫ _)
        originalExtensionCompIso_hom_cancel
    _ = _ := rfl

/-- The original affine chart-to-plane scheme morphism. -/
abbrev planeChartMap : Spec (CommRingCat.of (reesChartRing k)) ⟶
    Spec (CommRingCat.of (planeRing k)) := Spec.map (CommRingCat.ofHom (baseMap (k := k)))

/-- The original overlap-to-plane scheme morphism. -/
abbrev planeOverlapMap : Spec (CommRingCat.of (overlapRing k)) ⟶
    Spec (CommRingCat.of (planeRing k)) :=
  Spec.map (CommRingCat.ofHom (overlapBaseMap (k := k)))

def planePullbackScalarIso :
    (schemeModulePullback (planeChartMap (k := k))).obj (planeNativeModule k).tilde ≅
      (planeChartModule k).tilde :=
  AffineModuleTilde.pullbackIso (baseMap (k := k)) (planeNativeModule k)

def overlapPlanePullbackScalarIso :
    (schemeModulePullback (planeOverlapMap (k := k))).obj (planeNativeModule k).tilde ≅
      (baseModule k).tilde :=
  AffineModuleTilde.pullbackIso (overlapBaseMap (k := k)) (planeNativeModule k)

/-- The actual scheme composition, with both Spec composition and the
proved equality of the original ring maps transported explicitly. -/
def originalPlanePullbackCompIso :
    (schemeModulePullback (leftOverlapMap (k := k))).obj
      ((schemeModulePullback (planeChartMap (k := k))).obj (planeNativeModule k).tilde) ≅
    (schemeModulePullback (planeOverlapMap (k := k))).obj (planeNativeModule k).tilde :=
  (schemeModulePullbackCompIso (leftOverlapMap (k := k)) (planeChartMap (k := k))).app
      (planeNativeModule k).tilde ≪≫
    eqToIso (congrArg (fun f => (schemeModulePullback f).obj (planeNativeModule k).tilde)
      (AffineModuleTilde.specMap_comp_eq (baseMap (k := k)) (overlapLeft (k := k)))) ≪≫
    eqToIso (congrArg (fun q : planeRing k →+* overlapRing k =>
      (schemeModulePullback (Spec.map (CommRingCat.ofHom q))).obj (planeNativeModule k).tilde)
      left_comp_baseMap)

/-- Seal the original comparison at the Iso level before projecting its hom. -/
private theorem planePullbackScalarIso_as_pullbackIso :
    planePullbackScalarIso (k := k) =
      AffineModuleTilde.pullbackIso (baseMap (k := k)) (planeNativeModule k) := by
  rfl

private theorem overlapPlanePullbackScalarIso_as_pullbackIso :
    overlapPlanePullbackScalarIso (k := k) =
      AffineModuleTilde.pullbackIso (overlapBaseMap (k := k)) (planeNativeModule k) := by
  rfl

private theorem chartPullbackIso_as_extendScalars :
    AffineModuleTilde.pullbackIso (overlapLeft (k := k)) (planeChartModule k) =
      AffineModuleTilde.pullbackIso (overlapLeft (k := k))
        ((ModuleCat.extendScalars (baseMap (k := k))).obj (planeNativeModule k)) := by
  rfl

private theorem originalExtensionCompIso_as_extendScalarsComp :
    originalExtensionCompIso (k := k) =
      (eqToIso (congrArg
        (fun q : planeRing k →+* overlapRing k =>
          (ModuleCat.extendScalars q).obj (planeNativeModule k)) left_comp_baseMap)).symm ≪≫
        (ModuleCat.extendScalarsComp (baseMap (k := k)) (overlapLeft (k := k))).app
          (planeNativeModule k) := by
  rfl

private theorem originalPlanePullbackCompIso_as_schemeModulePullbackCompIso :
    originalPlanePullbackCompIso (k := k) =
      (schemeModulePullbackCompIso (leftOverlapMap (k := k)) (planeChartMap (k := k))).app
          (planeNativeModule k).tilde ≪≫
        eqToIso (congrArg (fun f => (schemeModulePullback f).obj (planeNativeModule k).tilde)
          (AffineModuleTilde.specMap_comp_eq (baseMap (k := k)) (overlapLeft (k := k)))) ≪≫
        eqToIso (congrArg (fun q : planeRing k →+* overlapRing k =>
          (schemeModulePullback (Spec.map (CommRingCat.ofHom q))).obj (planeNativeModule k).tilde)
          left_comp_baseMap) := by
  rfl

set_option maxHeartbeats 800000 in
set_option profiler true in
set_option profiler.threshold 10000 in
/-- The fixed generic affine comparison commutes with this actual Rees
composition and its explicitly transported original scalar comparison. -/
theorem originalPlanePullbackCompIso_scalar :
    (schemeModulePullback (leftOverlapMap (k := k))).map
        (planePullbackScalarIso (k := k)).hom ≫
      (AffineModuleTilde.pullbackIso (overlapLeft (k := k)) (planeChartModule k)).hom =
    (originalPlanePullbackCompIso (k := k)).hom ≫
      (overlapPlanePullbackScalarIso (k := k)).hom ≫
        AffineModuleTilde.map (originalExtensionCompIso (k := k)).hom := by
  have hL := congrArg₂
    (fun (i : (schemeModulePullback (planeChartMap (k := k))).obj
          (planeNativeModule k).tilde ≅ (planeChartModule k).tilde)
        (j : (schemeModulePullback (leftOverlapMap (k := k))).obj
          (planeChartModule k).tilde ≅ (iteratedPlaneModule k).tilde) =>
      (schemeModulePullback (leftOverlapMap (k := k))).map i.hom ≫ j.hom)
    (planePullbackScalarIso_as_pullbackIso (k := k))
    (chartPullbackIso_as_extendScalars (k := k))
  have hR := congrArg₂
    (fun (i : (schemeModulePullback (leftOverlapMap (k := k))).obj
          ((schemeModulePullback (planeChartMap (k := k))).obj (planeNativeModule k).tilde) ≅
          (schemeModulePullback (planeOverlapMap (k := k))).obj (planeNativeModule k).tilde)
        (f : (schemeModulePullback (planeOverlapMap (k := k))).obj
          (planeNativeModule k).tilde ⟶ (iteratedPlaneModule k).tilde) => i.hom ≫ f)
    (originalPlanePullbackCompIso_as_schemeModulePullbackCompIso (k := k))
    (congrArg₂
      (fun (i : (schemeModulePullback (planeOverlapMap (k := k))).obj
            (planeNativeModule k).tilde ≅ (baseModule k).tilde)
          (j : baseModule k ≅ iteratedPlaneModule k) =>
        i.hom ≫ AffineModuleTilde.map j.hom)
      (overlapPlanePullbackScalarIso_as_pullbackIso (k := k))
      (originalExtensionCompIso_as_extendScalarsComp (k := k)))
  exact hL.trans ((pullbackIso_comp_ringEq
    (baseMap (k := k)) (overlapLeft (k := k)) (overlapBaseMap (k := k))
    left_comp_baseMap (planeNativeModule k)).trans hR.symm)

/-- The original chart differential, now as an actual scheme-module
pullback map through the proved original affine comparison. -/
def planeChartDifferentialSheafMap :
    (schemeModulePullback (planeChartMap (k := k))).obj (planeNativeModule k).tilde ⟶
      (leftNativeModule k).tilde :=
  (planePullbackScalarIso (k := k)).hom ≫
    AffineModuleTilde.map
      (@ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
          (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
          (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
          (planeChartTopMap (k := k)) : planeChartModule k ⟶ leftNativeModule k)

set_option maxHeartbeats 800000 in
set_option profiler true in
set_option profiler.threshold 10000 in
/-- The actual iterated scheme pullback differential recovers the entire
original plane-chart-overlap scalar-extension map. -/
theorem plane_chart_overlap_square :
    (schemeModulePullback (leftOverlapMap (k := k))).map
        (planeChartDifferentialSheafMap (k := k)) ≫
      (leftPullbackScalarIso (k := k)).hom =
    (originalPlanePullbackCompIso (k := k)).hom ≫
      (overlapPlanePullbackScalarIso (k := k)).hom ≫
        planeChartOverlapSheafMap (k := k) := by
  let a : planeChartModule k ⟶ leftNativeModule k :=
    @ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
      (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
      (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
      (planeChartTopMap (k := k))
  let F := schemeModulePullback (leftOverlapMap (k := k))
  let p := (planePullbackScalarIso (k := k)).hom
  let q := (AffineModuleTilde.pullbackIso (overlapLeft (k := k)) (planeChartModule k)).hom
  let b := AffineModuleTilde.map ((ModuleCat.extendScalars (overlapLeft (k := k))).map a)
  let c := (originalPlanePullbackCompIso (k := k)).hom
  let r := (overlapPlanePullbackScalarIso (k := k)).hom
  let z := (originalExtensionCompIso (k := k)).hom
  let α := AffineModuleTilde.pullbackTildeIso (overlapLeft (k := k))
  have hα := α.hom.naturality a
  have hF : (AffineModuleTilde.functor (reesChartRing k) ⋙ F).map a =
      F.map (AffineModuleTilde.map a) := Functor.comp_map _ _ a
  have hB : (ModuleCat.extendScalars (overlapLeft (k := k)) ⋙
      AffineModuleTilde.functor (overlapRing k)).map a = b := Functor.comp_map _ _ a
  have hL : α.hom.app (leftNativeModule k) = (leftPullbackScalarIso (k := k)).hom := by
    simp only [α, leftPullbackScalarIso, AffineModuleTilde.pullbackIso, Iso.app_hom]
  have hQ : α.hom.app (planeChartModule k) = q := by
    simp only [α, q, AffineModuleTilde.pullbackIso, Iso.app_hom]
  have hn : F.map (AffineModuleTilde.map a) ≫ (leftPullbackScalarIso (k := k)).hom = q ≫ b :=
    (congrArg₂
      (fun (f : F.obj (planeChartModule k).tilde ⟶ F.obj (leftNativeModule k).tilde)
        (g : F.obj (leftNativeModule k).tilde ⟶ (leftModule k).tilde) => f ≫ g) hF hL).symm.trans
      (hα.trans (congrArg₂
        (fun (f : F.obj (planeChartModule k).tilde ⟶ (iteratedPlaneModule k).tilde)
          (g : (iteratedPlaneModule k).tilde ⟶ (leftModule k).tilde) => f ≫ g) hQ hB))
  have hc : F.map p ≫ q = c ≫ r ≫ AffineModuleTilde.map z :=
    originalPlanePullbackCompIso_scalar (k := k)
  have hd : planeChartDifferentialSheafMap (k := k) = p ≫ AffineModuleTilde.map a := rfl
  calc
    _ = F.map (p ≫ AffineModuleTilde.map a) ≫ (leftPullbackScalarIso (k := k)).hom :=
      congrArg
        (fun d : (schemeModulePullback (planeChartMap (k := k))).obj
            (planeNativeModule k).tilde ⟶ (leftNativeModule k).tilde =>
          F.map d ≫ (leftPullbackScalarIso (k := k)).hom) hd
    _ = (F.map p ≫ F.map (AffineModuleTilde.map a)) ≫
        (leftPullbackScalarIso (k := k)).hom :=
      congrArg
        (fun f : F.obj ((schemeModulePullback (planeChartMap (k := k))).obj
              (planeNativeModule k).tilde) ⟶ F.obj (leftNativeModule k).tilde =>
          f ≫ (leftPullbackScalarIso (k := k)).hom)
        (F.map_comp p (AffineModuleTilde.map a))
    _ = F.map p ≫ (F.map (AffineModuleTilde.map a) ≫
        (leftPullbackScalarIso (k := k)).hom) := Category.assoc _ _ _
    _ = F.map p ≫ (q ≫ b) :=
      congrArg (fun f : F.obj (planeChartModule k).tilde ⟶ (leftModule k).tilde =>
        F.map p ≫ f) hn
    _ = (F.map p ≫ q) ≫ b := (Category.assoc _ _ _).symm
    _ = (c ≫ r ≫ AffineModuleTilde.map z) ≫ b :=
      congrArg
        (fun f : F.obj ((schemeModulePullback (planeChartMap (k := k))).obj
              (planeNativeModule k).tilde) ⟶ (iteratedPlaneModule k).tilde => f ≫ b) hc
    _ = c ≫ r ≫ (AffineModuleTilde.map z ≫ b) := by simp only [Category.assoc]
    _ = c ≫ r ≫ AffineModuleTilde.map
        (z ≫ (ModuleCat.extendScalars (overlapLeft (k := k))).map a) :=
      congrArg (fun f : (baseModule k).tilde ⟶ (leftModule k).tilde => c ≫ r ≫ f)
        (AffineModuleTilde.map_comp z
          ((ModuleCat.extendScalars (overlapLeft (k := k))).map a)).symm
    _ = _ :=
      congrArg (fun f : baseModule k ⟶ leftModule k => c ≫ r ≫ AffineModuleTilde.map f)
        (originalExtensionCompIso_differential (k := k))

/-- The whole actual pullback square lands in the native overlap
top-differential sheaf by its original comparison map. -/
theorem plane_overlap_top_square :
    (schemeModulePullback (leftOverlapMap (k := k))).map
        (planeChartDifferentialSheafMap (k := k)) ≫
      (leftPullbackTopIso (k := k)).hom =
    (originalPlanePullbackCompIso (k := k)).hom ≫
      (overlapPlanePullbackScalarIso (k := k)).hom ≫
        FrobeniusBlowupDifferentialOverlapSheaf.baseTopSheafMap (k := k) := by
  change (schemeModulePullback (leftOverlapMap (k := k))).map
      (planeChartDifferentialSheafMap (k := k)) ≫
        ((leftPullbackScalarIso (k := k)).hom ≫ (leftTopSheafIso (k := k)).hom) = _
  calc
    _ = ((schemeModulePullback (leftOverlapMap (k := k))).map
          (planeChartDifferentialSheafMap (k := k)) ≫
        (leftPullbackScalarIso (k := k)).hom) ≫ (leftTopSheafIso (k := k)).hom :=
      (Category.assoc _ _ _).symm
    _ = ((originalPlanePullbackCompIso (k := k)).hom ≫
        (overlapPlanePullbackScalarIso (k := k)).hom ≫
        planeChartOverlapSheafMap (k := k)) ≫ (leftTopSheafIso (k := k)).hom :=
      congrArg
        (fun f : (schemeModulePullback (leftOverlapMap (k := k))).obj
            ((schemeModulePullback (planeChartMap (k := k))).obj
              (planeNativeModule k).tilde) ⟶ (leftModule k).tilde =>
          f ≫ (leftTopSheafIso (k := k)).hom)
        (plane_chart_overlap_square (k := k))
    _ = (originalPlanePullbackCompIso (k := k)).hom ≫
        (overlapPlanePullbackScalarIso (k := k)).hom ≫
        (planeChartOverlapSheafMap (k := k) ≫ (leftTopSheafIso (k := k)).hom) := by
      simp only [Category.assoc]
    _ = _ :=
      congrArg
        (fun f : (baseModule k).tilde ⟶
            (FrobeniusBlowupDifferentialOverlapSheaf.targetModule k).tilde =>
          (originalPlanePullbackCompIso (k := k)).hom ≫
            (overlapPlanePullbackScalarIso (k := k)).hom ≫ f)
        (planeChartOverlapSheafMap_comp (k := k))

end KltDP.Examples.FrobeniusBlowupDifferentialPullbackComp
