import KltDP.Examples.FrobeniusBlowupGlobalTensorCharts
import KltDP.Examples.FrobeniusBlowupIntrinsicExceptionalTensorLeft
import KltDP.Examples.FrobeniusBlowupIntrinsicExceptionalTensorRight

/-!
# The actual canonical factor on the two original Rees charts

The two proved determinant factorizations use the same native ideals and
intrinsic top sheaves as the global tensor comparison. Composing their
original source and target isomorphisms gives actual isomorphisms between
the pullbacks of the original global source and exceptional tensor target.
Their whole-map compatibility is proved, rather than an input to descent.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusBlowupCanonicalFactorCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusBlowupGlobalDifferentialCharts FrobeniusBlowupGlobalExteriorCharts
open FrobeniusBlowupGlobalCanonicalTarget FrobeniusBlowupGlobalTensorCharts

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

local instance factorChartRing (a : centerIdeal (k := k)) :
    CommRing (chartRing (centerIdeal (k := k)) a) :=
  inferInstanceAs (CommRing (HomogeneousLocalization.Away
    (ReesGrading.component (centerIdeal (k := k)))
    (degreeOne (centerIdeal (k := k)) a)))

/-- The actual first native ideal inclusion is the same original tensor inclusion. -/
theorem chartIdealTopInclusion_centerU :
    chartIdealTopInclusion (centerU (k := k)) =
      FrobeniusBlowupIntrinsicExceptionalTensorLeft.exceptionalTensorInclusion (k := k) := by
  simp only [chartIdealTopInclusion, schemeStructureTensorInclusion,
    chartIdealTildeInclusion, AffinePrincipalIdealTildeFrame.inclusion,
    FrobeniusBlowupIntrinsicExceptionalTensorLeft.exceptionalTensorInclusion,
    FrobeniusBlowupIntrinsicExceptionalTensorLeft.idealInclusionSheaf,
    FrobeniusBlowupIntrinsicExceptionalTensorLeft.structureUnitIso,
    FrobeniusBlowupIntrinsicExceptionalTensorLeft.idealInclusion,
    chartTop, FrobeniusBlowupIntrinsicDifferentialPullback.leftExterior,
    FrobeniusBlowupIntrinsicDifferentialWedge.leftStructure, chartStructure,
    Category.assoc]

/-- The actual second native ideal inclusion uses exactly the same original unit. -/
theorem chartIdealTopInclusion_centerV :
    chartIdealTopInclusion (centerV (k := k)) =
      FrobeniusBlowupIntrinsicExceptionalTensorRight.exceptionalTensorInclusion (k := k) := by
  simp only [chartIdealTopInclusion, schemeStructureTensorInclusion,
    chartIdealTildeInclusion, AffinePrincipalIdealTildeFrame.inclusion,
    FrobeniusBlowupIntrinsicExceptionalTensorRight.exceptionalTensorInclusion,
    FrobeniusBlowupIntrinsicExceptionalTensorRight.idealInclusionSheaf,
    FrobeniusBlowupIntrinsicExceptionalTensorRight.structureUnitIso,
    FrobeniusBlowupIntrinsicExceptionalTensorRight.idealInclusion,
    chartTop, FrobeniusBlowupIntrinsicDifferentialRightPullback.rightExterior,
    FrobeniusBlowupIntrinsicDifferentialWedge.rightStructure, chartStructure,
    Category.assoc]

/-- Select the proved original determinant isomorphism on each original generator chart. -/
def nativeChartFactorIso (i : Bool) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom
        (chartBaseMap centerIdeal (centerGenerator (k := k) i))))).obj (planeTop (k := k)) ≅
      (chartIdealModule centerIdeal (centerGenerator (k := k) i)).tilde ⊗
        chartTop (centerGenerator (k := k) i) := by
  cases i
  · exact FrobeniusBlowupIntrinsicExceptionalTensorLeft.intrinsicExceptionalTensorIso (k := k)
  · exact FrobeniusBlowupIntrinsicExceptionalTensorRight.intrinsicExceptionalTensorIso (k := k)

/-- The chosen two local isomorphisms factor the actual whole chart differential maps. -/
theorem nativeChartFactorIso_factor (i : Bool) :
    (nativeChartFactorIso (k := k) i).hom ≫ chartIdealTopInclusion (centerGenerator (k := k) i) =
      chartBlowdownMap (centerGenerator (k := k) i) := by
  cases i
  · simpa only [nativeChartFactorIso, centerGenerator, chartIdealTopInclusion_centerU,
      chartBlowdownMap_centerU] using
      FrobeniusBlowupIntrinsicExceptionalTensorLeft.intrinsicExceptionalTensorIso_factor (k := k)
  · simpa only [nativeChartFactorIso, centerGenerator, chartIdealTopInclusion_centerV,
      chartBlowdownMap_centerV] using
      FrobeniusBlowupIntrinsicExceptionalTensorRight.intrinsicExceptionalTensorIso_factor (k := k)

/-- The original global source and target become isomorphic on each actual affine chart. -/
def chartCanonicalFactorIso (i : Bool) :
    (schemeModulePullback (chartι centerIdeal (centerGenerator (k := k) i))).obj
        ((schemeModulePullback (toSpec centerIdeal)).obj (planeTop (k := k))) ≅
      (schemeModulePullback (chartι centerIdeal (centerGenerator (k := k) i))).obj
        (exceptionalCanonicalTensor (k := k)) :=
  chartSourceIso (centerGenerator (k := k) i) ≪≫ nativeChartFactorIso i ≪≫
    (chartExceptionalTensorIso (centerGenerator (k := k) i)).symm

/-- These actual chart isomorphisms preserve the original global differential and inclusion. -/
theorem chartCanonicalFactorIso_factor (i : Bool) :
    (chartCanonicalFactorIso (k := k) i).hom ≫
        (schemeModulePullback (chartι centerIdeal (centerGenerator (k := k) i))).map
          (exceptionalCanonicalInclusion (k := k)) =
      (schemeModulePullback (chartι centerIdeal (centerGenerator (k := k) i))).map
        (blowdownMap (k := k)) := by
  apply (cancel_mono (chartGlobalIso (centerGenerator (k := k) i)).hom).mp
  rw [Category.assoc, ← chartExceptionalTensorIso_inclusion]
  simp only [chartCanonicalFactorIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [nativeChartFactorIso_factor, blowdownMap_chartIso]

end KltDP.Examples.FrobeniusBlowupCanonicalFactorCharts
