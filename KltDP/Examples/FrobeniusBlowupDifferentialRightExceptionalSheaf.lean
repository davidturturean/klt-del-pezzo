import KltDP.Examples.FrobeniusBlowupDifferentialRightExceptionalImage

/-!
# Complementary-chart differential sheaf factorization

Use the existing affine pullback comparison and tilde functor on the original
second Rees chart. Its actual top-differential map factors through the tilde
of the original extended center ideal by the proved determinant equivalence.
The source plane wedge maps to minus the original exceptional equation, as
required by the existing native wedge order `(v,u/v)`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialRightExceptionalSheaf

open FrobeniusBlowupContact FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialOverlap FrobeniusBlowupDifferentialPullback
open FrobeniusBlowupDifferentialPullbackComp FrobeniusBlowupDifferentialRightMap
open FrobeniusBlowupDifferentialRightFrame FrobeniusBlowupDifferentialRightExceptionalImage
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

private theorem linearEquiv_map_toOpen {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (e : M ≃ₗ[R] N)
    (U : Opens (PrimeSpectrum R)) (m : M) :
    (AffineModuleTilde.map (R := R) (M := M) (N := N) e.toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen M U m) = ModuleCat.Tilde.toOpen N U (e m) :=
  AffineModuleTilde.map_app_toOpen (R := R) (M := M) (N := N) e.toModuleIso.hom U m

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (rightChartRing k) :=
  FrobeniusBlowupDifferentialRightMap.rightBaseAlgebra
local instance : Algebra k (rightChartRing k) :=
  FrobeniusBlowupDifferentialOverlap.rightFieldAlgebra

abbrev rightExceptionalIdealModule (k : Type u) [Field k] : ModuleCat (rightChartRing k) :=
  ModuleCat.of (rightChartRing k) (rightExceptionalIdeal k)

def rightExceptionalIdealToNative : rightExceptionalIdealModule k ⟶ rightNativeModule k :=
  @ModuleCat.ofHom (rightChartRing k) _ (rightExceptionalIdealModule k) (rightNativeModule k)
    (rightExceptionalIdealModule k).isAddCommGroup (rightExceptionalIdealModule k).isModule
    (rightNativeModule k).isAddCommGroup (rightNativeModule k).isModule
    ((rightTopDifferentialEquiv (k := k)).symm.toLinearMap.comp
      (rightExceptionalIdeal k).subtype)

theorem rightExceptionalIdealToNative_apply (r : rightExceptionalIdealModule k) :
    rightExceptionalIdealToNative (k := k) r =
      (r : rightChartRing k) • rightChartForm (k := k) :=
  rightTopDifferentialEquiv_symm_apply (r : rightChartRing k)

theorem planeRightExceptionalEquiv_factor :
    (planeRightExceptionalEquiv (k := k)).toModuleIso.hom ≫
        rightExceptionalIdealToNative (k := k) =
      (@ModuleCat.ofHom (rightChartRing k) _ (planeRightModule k) (rightNativeModule k)
        (planeRightModule k).isAddCommGroup (planeRightModule k).isModule
        (rightNativeModule k).isAddCommGroup (rightNativeModule k).isModule
        (planeRightTopMap (k := k)) : planeRightModule k ⟶ rightNativeModule k) := by
  apply ModuleCat.hom_ext
  exact planeRightTopMap_factor (k := k)

/-- The original complementary-chart blowdown map, before any quotient. -/
abbrev planeRightMap : Spec (CommRingCat.of (rightChartRing k)) ⟶
    Spec (CommRingCat.of (planeRing k)) :=
  Spec.map (CommRingCat.ofHom (rightBaseMap (k := k)))

def planeRightPullbackScalarIso :
    (schemeModulePullback (planeRightMap (k := k))).obj (planeNativeModule k).tilde ≅
      (planeRightModule k).tilde :=
  AffineModuleTilde.pullbackIso (rightBaseMap (k := k)) (planeNativeModule k)

/-- Actual affine pullback followed by the actual original exterior differential. -/
def planeRightDifferentialSheafMap :
    (schemeModulePullback (planeRightMap (k := k))).obj (planeNativeModule k).tilde ⟶
      (rightNativeModule k).tilde :=
  (planeRightPullbackScalarIso (k := k)).hom ≫
    AffineModuleTilde.map
      (@ModuleCat.ofHom (rightChartRing k) _ (planeRightModule k) (rightNativeModule k)
        (planeRightModule k).isAddCommGroup (planeRightModule k).isModule
        (rightNativeModule k).isAddCommGroup (rightNativeModule k).isModule
        (planeRightTopMap (k := k)) : planeRightModule k ⟶ rightNativeModule k)

def planeRightExceptionalSheafIso :
    (schemeModulePullback (planeRightMap (k := k))).obj (planeNativeModule k).tilde ≅
      (rightExceptionalIdealModule k).tilde :=
  planeRightPullbackScalarIso (k := k) ≪≫
    AffineModuleTilde.linearEquivIso
      (M := planeRightModule k) (N := rightExceptionalIdealModule k)
      (planeRightExceptionalEquiv (k := k))

def rightExceptionalIdealTopSheafMap :
    (rightExceptionalIdealModule k).tilde ⟶ (rightNativeModule k).tilde :=
  AffineModuleTilde.map (rightExceptionalIdealToNative (k := k))

/-- Equality of actual sheaf morphisms on the entire original chart. -/
theorem planeRightDifferentialSheafMap_factor :
    (planeRightExceptionalSheafIso (k := k)).hom ≫
        rightExceptionalIdealTopSheafMap (k := k) =
      planeRightDifferentialSheafMap (k := k) := by
  change ((planeRightPullbackScalarIso (k := k)).hom ≫
      AffineModuleTilde.map (planeRightExceptionalEquiv (k := k)).toModuleIso.hom) ≫
        AffineModuleTilde.map (rightExceptionalIdealToNative (k := k)) =
    (planeRightPullbackScalarIso (k := k)).hom ≫
      AffineModuleTilde.map
        (@ModuleCat.ofHom (rightChartRing k) _ (planeRightModule k) (rightNativeModule k)
          (planeRightModule k).isAddCommGroup (planeRightModule k).isModule
          (rightNativeModule k).isAddCommGroup (rightNativeModule k).isModule
          (planeRightTopMap (k := k)) : planeRightModule k ⟶ rightNativeModule k)
  rw [Category.assoc, ← AffineModuleTilde.map_comp, planeRightExceptionalEquiv_factor]

theorem rightExceptionalIdealTopSheafMap_toOpen
    (U : Opens (PrimeSpectrum (rightChartRing k))) (r : rightExceptionalIdealModule k) :
    (rightExceptionalIdealTopSheafMap (k := k)).val.app (op U)
        (ModuleCat.Tilde.toOpen (rightExceptionalIdealModule k) U r) =
      ModuleCat.Tilde.toOpen (rightNativeModule k) U
        ((r : rightChartRing k) • rightChartForm (k := k)) :=
  (AffineModuleTilde.map_app_toOpen (rightExceptionalIdealToNative (k := k)) U r).trans
    (congrArg (ModuleCat.Tilde.toOpen (rightNativeModule k) U)
      (rightExceptionalIdealToNative_apply r))

theorem planeRightExceptionalTilde_toOpen
    (U : Opens (PrimeSpectrum (rightChartRing k))) (ω : planeRightModule k) :
    (AffineModuleTilde.map (R := rightChartRing k)
      (M := planeRightModule k) (N := rightExceptionalIdealModule k)
      (planeRightExceptionalEquiv (k := k)).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen (planeRightModule k) U ω) =
      ModuleCat.Tilde.toOpen (rightExceptionalIdealModule k) U
        (planeRightExceptionalEquiv (k := k) ω) :=
  linearEquiv_map_toOpen (R := rightChartRing k)
    (M := planeRightModule k) (N := rightExceptionalIdealModule k)
    (planeRightExceptionalEquiv (k := k)) U ω

theorem planeRightExceptionalTilde_coordinate
    (U : Opens (PrimeSpectrum (rightChartRing k))) :
    (AffineModuleTilde.map (R := rightChartRing k)
      (M := planeRightModule k) (N := rightExceptionalIdealModule k)
      (planeRightExceptionalEquiv (k := k)).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen (planeRightModule k) U
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) =
      ModuleCat.Tilde.toOpen (rightExceptionalIdealModule k) U
        (-chartCenterEquation (centerIdeal (k := k)) (centerV (k := k))) :=
  (planeRightExceptionalTilde_toOpen U
    (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))).trans
      (congrArg (ModuleCat.Tilde.toOpen (rightExceptionalIdealModule k) U)
        (planeRightExceptionalEquiv_coordinate (k := k)))

/-- The determinant equivalence retains its original negative exceptional
generator when evaluated on canonical sections of the source wedge. -/
theorem planeRightExceptionalSheafIso_coordinate
    (U : Opens (PrimeSpectrum (rightChartRing k))) :
    (planeRightExceptionalSheafIso (k := k)).hom.val.app (op U)
        ((planeRightPullbackScalarIso (k := k)).inv.val.app (op U)
          (ModuleCat.Tilde.toOpen (planeRightModule k) U
            (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)))) =
      ModuleCat.Tilde.toOpen (rightExceptionalIdealModule k) U
        (-chartCenterEquation (centerIdeal (k := k)) (centerV (k := k))) := by
  have hcancel :
      (planeRightPullbackScalarIso (k := k)).inv ≫
          (planeRightExceptionalSheafIso (k := k)).hom =
        AffineModuleTilde.map (planeRightExceptionalEquiv (k := k)).toModuleIso.hom := by
    change (planeRightPullbackScalarIso (k := k)).inv ≫
        ((planeRightPullbackScalarIso (k := k)).hom ≫
          AffineModuleTilde.map (planeRightExceptionalEquiv (k := k)).toModuleIso.hom) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hsection := congrArg
    (fun f : (planeRightModule k).tilde ⟶ (rightExceptionalIdealModule k).tilde =>
      f.val.app (op U)
        (ModuleCat.Tilde.toOpen (planeRightModule k) U
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)))) hcancel
  exact hsection.trans (planeRightExceptionalTilde_coordinate (k := k) U)

end KltDP.Examples.FrobeniusBlowupDifferentialRightExceptionalSheaf
