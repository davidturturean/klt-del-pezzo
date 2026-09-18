import KltDP.Geometry.GluedNormalTwistedAdjunctionGlobalChart
import KltDP.Geometry.AffineDifferentialExteriorTildeIso
import KltDP.Geometry.SchemeKaehlerExteriorOpenRestriction
import KltDP.Geometry.SchemeModulePullbackSquareCoherence

/-!
# The original ambient adjunction factor on a quotient chart

The native top differential tilde is compared with the original intrinsic
exterior sheaf by the proved affine exterior map. The actual open-immersion
comparison and the original quotient-chart square then identify its pullback
with the chart pullback of the global ambient exterior factor.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAmbientChart

open SchemeKaehlerSheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData) (U : X.affineOpens)

/-- The actual global ambient top differential sheaf pulled to the closed subscheme. -/
abbrev globalAmbientSheaf : I.glueData.glued.Modules :=
  (schemeModulePullback I.gluedTo).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)

/-- The original affine chart structure map for its induced algebra. -/
theorem affineBaseMap_comp :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    U.2.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U.1))) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  exact (Spec_map_baseToAffineSectionsMap f U.2).symm

/-- Restricting the original global exterior sheaf gives the actual native top-form tilde. -/
def affineIso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      (schemeModulePullback U.2.fromSpec).obj
          (SchemeExteriorPower.sheaf (baseRingSheaf f) 2) ≅
        (ModuleCat.of Γ(X, U.1)
          (⋀[Γ(X, U.1)]^2 (KaehlerDifferential R Γ(X, U.1)))).tilde := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _
  exact SchemeKaehlerExteriorOpenRestriction.pullbackIso f U.2.fromSpec 2 ≪≫
    eqToIso (congrArg (fun g => SchemeExteriorPower.sheaf (baseRingSheaf g) 2)
      (affineBaseMap_comp f U)) ≪≫
    (AffineDifferentialExteriorTildeMap.standardSmoothIso R Γ(X, U.1)).symm

/-- The original quotient-chart square commutes with the actual global closed immersion. -/
theorem chartMap_square :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec =
      I.glueData.ι U ≫ I.gluedTo :=
  ((I.ι_gluedTo U).trans (I.glueDataObjι_ι U)).symm

/-- The original native ambient factor is the chart pullback of the actual global factor. -/
def iso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      GluedNormalTwistedAdjunctionChart.ambientSheaf I U R ≅
        (schemeModulePullback (I.glueData.ι U)).obj (globalAmbientSheaf f I) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _
  exact (schemeModulePullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))).mapIso
        (affineIso f U).symm ≪≫
    SchemeModulePullbackSquareCoherence.squareIso I.gluedTo U.2.fromSpec
      (I.glueData.ι U) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
      (chartMap_square I U) (SchemeExteriorPower.sheaf (baseRingSheaf f) 2)

end KltDP.Geometry.GluedAdjunctionAmbientChart
