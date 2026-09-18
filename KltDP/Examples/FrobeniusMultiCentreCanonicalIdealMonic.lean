import KltDP.Examples.FrobeniusMultiCentreCanonicalIdealFamily
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorGenericPoint
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorMono
import KltDP.Examples.FrobeniusGlobalBlowupCanonicalTarget
import KltDP.Examples.FrobeniusMultiCentreGenericPoint
import KltDP.Geometry.CartierPullbackKernelInclusion
import KltDP.Geometry.CartierDivisorPullbackComp
import KltDP.Geometry.PointBlowupExceptionalCartier

/-!
# Monicity of the actual finite-centre exceptional ideal tensor

Each original exceptional Cartier divisor has the actual creation-stage fiber
as its ideal data. The actual tower and between-stage projections preserve
generic points. The normalized Cartier pullback theorem thus proves monicity
of each original pulled inclusion, and the original tensor equivalence proves
monicity of their ordered double product.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalIdealMonic

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupCanonicalTarget
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusExceptionalFinalConfiguration
open FrobeniusTowerFunctionField.PlaneChartedScheme FrobeniusMultiCentreSurface
open FrobeniusMultiCentreIntegral FrobeniusMultiCentreGenericPoint
open FrobeniusContactTowerCanonicalFactorGenericPoint FrobeniusContactTowerCanonicalFactorMono
open FrobeniusContactTowerCanonicalFactorLocalIdeals FrobeniusMultiCentreCanonicalIdealFamily

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance idealMonicOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

private theorem wholeExceptionalPulledInclusion_mono (A : PlaneChartedScheme k)
    [IsIntegral A.nextScheme] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ A.nextScheme) [GenericPointPreserving f] :
    Mono ((schemeModulePullback f).map (wholeExceptionalInclusion A) ≫
      (schemeModulePullbackUnitIso f).hom) := by
  letI := PointBlowupGluing.globalCenterFiberIdeal_isInvertible A.chart originPoint A.center_closed
  exact CartierPullbackComparison.pulledKernelInclusion_mono_of_regularCartier_kernel f
    (PointBlowupExceptionalCartier.exceptionalCartierDivisor A.chart originPoint A.center_closed)
    (PointBlowupExceptionalCartier.exceptionalCartierDivisor_hasRegularEquations
      A.chart originPoint A.center_closed)
    (PointBlowupGluing.globalCenterFiberι A.chart originPoint A.center_closed)
    (PointBlowupExceptionalCartier.exceptionalCartierDivisor_idealData A.chart originPoint A.center_closed)

variable [IsAlgClosed k]

/-- Each actual pulled total exceptional inclusion is monic on the original whole surface. -/
theorem multiTotalExceptionalInclusion_mono (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) (j : Fin (q + 1)) :
    Mono (multiTotalExceptionalInclusion (q + 1) n a i j) := by
  let A := translatedInitial (q + 1) (a i)
  letI : IsIntegral A.carrier := FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsIntegral (selectedStage (q + 1) (a i) (q + 1)) := instStageIsIntegral A (q + 1)
  letI : IsIntegral (A.stage j.val).nextScheme := instStageIsIntegral A (j.val + 1)
  let b : selectedStage (q + 1) (a i) (q + 1) ⟶ (A.stage j.val).nextScheme :=
    between A j.isLt
  let t := towerProjection (q + 1) n a i
  letI : GenericPointPreserving b :=
    between_genericPointPreserving A (j.val + 1) (q + 1) j.isLt
  letI : GenericPointPreserving t := towerProjection_genericPointPreserving q n a ha i
  letI : Mono ((schemeModulePullback (t ≫ b)).map (wholeExceptionalInclusion (A.stage j.val)) ≫
      (schemeModulePullbackUnitIso (t ≫ b)).hom) :=
    wholeExceptionalPulledInclusion_mono (A.stage j.val) (t ≫ b)
  exact iteratedPulledInclusion_mono b t (wholeExceptionalInclusion (A.stage j.val))

/-- The product of the actual inclusions for one original cluster is monic. -/
theorem clusterIdealInclusion_mono (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (i : Fin n) : Mono (clusterIdealInclusion (q + 1) n a i) :=
  familyInclusion_mono (q + 1) _ (multiTotalExceptionalInclusion (q + 1) n a i)
    (multiTotalExceptionalInclusion_mono q n a ha i)

/-- The full original double product inclusion is monic. -/
theorem multiIdealInclusion_mono (q n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) : Mono (multiIdealInclusion (q + 1) n a) :=
  familyInclusion_mono n (clusterIdealLine (q + 1) n a) (clusterIdealInclusion (q + 1) n a)
    (clusterIdealInclusion_mono q n a ha)

end KltDP.Examples.FrobeniusMultiCentreCanonicalIdealMonic
