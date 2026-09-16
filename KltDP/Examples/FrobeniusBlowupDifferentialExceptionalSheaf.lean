import KltDP.Examples.FrobeniusBlowupDifferentialExceptionalImage

/-!
# Original differential sheaf factorization through the exceptional ideal

Lift the proved whole-module determinant factorization by the existing affine
tilde functor and the original affine pullback comparison. The source is the
actual scheme pullback of the original plane top-differential tilde sheaf; the
target is the original native Rees-chart top-differential tilde sheaf.

The intervening ideal is the original extended center ideal. Its inclusion
followed by the inverse native frame recovers the already constructed actual
scheme differential map, on all sections. Canonical sections retain the
original exceptional equation and original native coordinate wedge.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace KltDP.Examples.FrobeniusBlowupDifferentialExceptionalSheaf

open FrobeniusBlowupContact FrobeniusBlowupDifferential
open FrobeniusBlowupDifferentialMap FrobeniusBlowupDifferentialRestriction
open FrobeniusBlowupDifferentialPullback FrobeniusBlowupDifferentialPullbackComp
open FrobeniusReesChartDifferentialFrame FrobeniusBlowupDifferentialExceptionalImage
open KltDP.Geometry KltDP.Geometry.AffineBlowup

universe u

private theorem linearEquiv_map_toOpen {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (e : M ≃ₗ[R] N)
    (U : Opens (PrimeSpectrum R)) (m : M) :
    (AffineModuleTilde.map (R := R) (M := M) (N := N) e.toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen M U m) = ModuleCat.Tilde.toOpen N U (e m) :=
  AffineModuleTilde.map_app_toOpen (R := R) (M := M) (N := N) e.toModuleIso.hom U m

variable {k : Type u} [Field k]

local instance : Algebra (planeRing k) (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartBaseAlgebra
local instance : Algebra k (reesChartRing k) :=
  FrobeniusBlowupDifferentialMap.chartFieldAlgebra

/-- The original extended center ideal, regarded as an actual chart module. -/
abbrev exceptionalIdealModule (k : Type u) [Field k] : ModuleCat (reesChartRing k) :=
  ModuleCat.of (reesChartRing k)
    (FrobeniusBlowupDifferentialExceptionalImage.exceptionalIdeal k)

/-- Include the actual exceptional ideal, then use the inverse native frame. -/
def exceptionalIdealToNative : exceptionalIdealModule k ⟶ leftNativeModule k :=
  @ModuleCat.ofHom (reesChartRing k) _ (exceptionalIdealModule k) (leftNativeModule k)
    (exceptionalIdealModule k).isAddCommGroup (exceptionalIdealModule k).isModule
    (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
    ((chartTopDifferentialEquiv (k := k)).symm.toLinearMap.comp
      (FrobeniusBlowupDifferentialExceptionalImage.exceptionalIdeal k).subtype)

theorem exceptionalIdealToNative_apply (r : exceptionalIdealModule k) :
    exceptionalIdealToNative (k := k) r =
      (r : reesChartRing k) • chartCoordinateTopForm (k := k) :=
  chartTopDifferentialEquiv_symm_apply (r : reesChartRing k)

/-- The whole-module factorization expressed in the original module category. -/
theorem planeChartExceptionalEquiv_factor :
    (planeChartExceptionalEquiv (k := k)).toModuleIso.hom ≫
        exceptionalIdealToNative (k := k) =
      (@ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
        (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
        (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
        (planeChartTopMap (k := k)) : planeChartModule k ⟶ leftNativeModule k) := by
  apply ModuleCat.hom_ext
  exact planeChartTopMap_factor (k := k)

/-- The actual scheme pullback of the original plane top module is identified
with the tilde of the original exceptional ideal by its actual determinant. -/
def planeChartExceptionalSheafIso :
    (schemeModulePullback (planeChartMap (k := k))).obj (planeNativeModule k).tilde ≅
      (exceptionalIdealModule k).tilde :=
  (planePullbackScalarIso (k := k)) ≪≫
    AffineModuleTilde.linearEquivIso
      (M := planeChartModule k) (N := exceptionalIdealModule k)
      (planeChartExceptionalEquiv (k := k))

/-- The actual ideal inclusion and native frame act on the original tilde sheaves. -/
def exceptionalIdealTopSheafMap :
    (exceptionalIdealModule k).tilde ⟶ (leftNativeModule k).tilde :=
  AffineModuleTilde.map (exceptionalIdealToNative (k := k))

/-- Factorization of the entire already constructed scheme differential map. -/
theorem planeChartDifferentialSheafMap_factor :
    (planeChartExceptionalSheafIso (k := k)).hom ≫
        exceptionalIdealTopSheafMap (k := k) =
      planeChartDifferentialSheafMap (k := k) := by
  change ((planePullbackScalarIso (k := k)).hom ≫
      AffineModuleTilde.map (planeChartExceptionalEquiv (k := k)).toModuleIso.hom) ≫
        AffineModuleTilde.map (exceptionalIdealToNative (k := k)) =
    (planePullbackScalarIso (k := k)).hom ≫
      AffineModuleTilde.map
        (@ModuleCat.ofHom (reesChartRing k) _ (planeChartModule k) (leftNativeModule k)
          (planeChartModule k).isAddCommGroup (planeChartModule k).isModule
          (leftNativeModule k).isAddCommGroup (leftNativeModule k).isModule
          (planeChartTopMap (k := k)) : planeChartModule k ⟶ leftNativeModule k)
  rw [Category.assoc, ← AffineModuleTilde.map_comp, planeChartExceptionalEquiv_factor]

/-- Canonical ideal sections map to the same coefficient times the original
native wedge on every open of the actual Rees chart. -/
theorem exceptionalIdealTopSheafMap_toOpen
    (U : Opens (PrimeSpectrum (reesChartRing k))) (r : exceptionalIdealModule k) :
    (exceptionalIdealTopSheafMap (k := k)).val.app (op U)
        (ModuleCat.Tilde.toOpen (exceptionalIdealModule k) U r) =
      ModuleCat.Tilde.toOpen (leftNativeModule k) U
        ((r : reesChartRing k) • chartCoordinateTopForm (k := k)) :=
  (AffineModuleTilde.map_app_toOpen (exceptionalIdealToNative (k := k)) U r).trans
    (congrArg (ModuleCat.Tilde.toOpen (leftNativeModule k) U)
      (exceptionalIdealToNative_apply r))

/-- The extended plane coordinate wedge maps to the actual exceptional
equation as an element of the original ideal. -/
theorem planeChartExceptionalEquiv_coordinate :
    planeChartExceptionalEquiv (k := k)
        (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) =
      chartCenterEquation (centerIdeal (k := k)) (centerU (k := k)) := by
  apply Subtype.ext
  change planeChartDeterminant (k := k)
    (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)) = chartU (k := k)
  rw [planeChartDeterminant_apply, planeChartFrameEquiv_coordinate, one_mul]

/-- Specialize the existing tilde naturality theorem with all original
module objects fixed before using it in the pullback normalization. -/
theorem planeChartExceptionalTilde_toOpen
    (U : Opens (PrimeSpectrum (reesChartRing k))) (ω : planeChartModule k) :
    (AffineModuleTilde.map (R := reesChartRing k)
      (M := planeChartModule k) (N := exceptionalIdealModule k)
      (planeChartExceptionalEquiv (k := k)).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen (planeChartModule k) U ω) =
      ModuleCat.Tilde.toOpen (exceptionalIdealModule k) U
        (planeChartExceptionalEquiv (k := k) ω) :=
  linearEquiv_map_toOpen (R := reesChartRing k)
    (M := planeChartModule k) (N := exceptionalIdealModule k)
    (planeChartExceptionalEquiv (k := k)) U ω

theorem planeChartExceptionalTilde_coordinate
    (U : Opens (PrimeSpectrum (reesChartRing k))) :
    (AffineModuleTilde.map (R := reesChartRing k)
      (M := planeChartModule k) (N := exceptionalIdealModule k)
      (planeChartExceptionalEquiv (k := k)).toModuleIso.hom).val.app (op U)
        (ModuleCat.Tilde.toOpen (planeChartModule k) U
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))) =
      ModuleCat.Tilde.toOpen (exceptionalIdealModule k) U
        (chartCenterEquation (centerIdeal (k := k)) (centerU (k := k))) :=
  (planeChartExceptionalTilde_toOpen U
    (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k))).trans
      (congrArg (ModuleCat.Tilde.toOpen (exceptionalIdealModule k) U)
        (planeChartExceptionalEquiv_coordinate (k := k)))

/-- The original determinant isomorphism preserves its exceptional equation
normalization after passing to canonical sections on every chart open. -/
theorem planeChartExceptionalSheafIso_coordinate
    (U : Opens (PrimeSpectrum (reesChartRing k))) :
    (planeChartExceptionalSheafIso (k := k)).hom.val.app (op U)
        ((planePullbackScalarIso (k := k)).inv.val.app (op U)
          (ModuleCat.Tilde.toOpen (planeChartModule k) U
            (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)))) =
      ModuleCat.Tilde.toOpen (exceptionalIdealModule k) U
        (chartCenterEquation (centerIdeal (k := k)) (centerU (k := k))) := by
  have hcancel :
      (planePullbackScalarIso (k := k)).inv ≫
          (planeChartExceptionalSheafIso (k := k)).hom =
        AffineModuleTilde.map (planeChartExceptionalEquiv (k := k)).toModuleIso.hom := by
    change (planePullbackScalarIso (k := k)).inv ≫
        ((planePullbackScalarIso (k := k)).hom ≫
          AffineModuleTilde.map (planeChartExceptionalEquiv (k := k)).toModuleIso.hom) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hsection := congrArg
    (fun f : (planeChartModule k).tilde ⟶ (exceptionalIdealModule k).tilde =>
      f.val.app (op U)
        (ModuleCat.Tilde.toOpen (planeChartModule k) U
          (1 ⊗ₜ[planeRing k] coordinateTopForm (k := k)))) hcancel
  exact hsection.trans (planeChartExceptionalTilde_coordinate (k := k) U)

end KltDP.Examples.FrobeniusBlowupDifferentialExceptionalSheaf
