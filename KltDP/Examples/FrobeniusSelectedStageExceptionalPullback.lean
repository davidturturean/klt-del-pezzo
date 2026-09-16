import KltDP.Examples.FrobeniusSelectedStageSurface
import KltDP.Geometry.GluedIdealSheafLift
import KltDP.Geometry.SchematicImageDenseOpen
import KltDP.Geometry.PrimeCurveRestrictionDegree
import KltDP.Geometry.AffinePIDInvertibleTrivial
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit

/-!
# `E · π^*L = 0` on the stage surface of any charted plane (in particular on lane F's towers)

The argument of `FrobeniusStageExceptionalPullback` restated for an arbitrary charted plane `A`
(integral carrier, proper structure morphism, normal carrier of dimension two): on the surface
`stageSurfaceOf A hA h0 (n+1) hproj` the exceptional prime curve `E = exceptionalPrimeCurveOf A n …`
has `E.toScheme ≅` the centre fibre (`exceptionalLiftOf`), `E.inclusion ≫ π` factors through the
closed centre, and the restriction degree of `π^*L` to `E` vanishes for every invertible sheaf `L` on
stage `n` (`restrictionDegree_pullback_stepProjectionOf`). Specialised to `translatedInitial p a`
this is `E · π^*L = 0` on every tower stage `selectedStage p a (n+1)` (`selected_restrictionDegree_pullback_stepProjection`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusSelectedStageExceptionalPullback

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalExceptionalNormal FrobeniusStageNormal FrobeniusStageDimension
open FrobeniusSelectedStageSurface FrobeniusSelectedStageSurface.PlaneChartedScheme
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint FrobeniusProjectivePoints

variable {k : Type u} [Field k] [IsAlgClosed k] (A : PlaneChartedScheme k)
  [IsIntegral A.carrier] [IsProper A.structureMap] (n : ℕ) (hA : IsNormalScheme A.carrier)
  (h0 : topologicalKrullDim A.carrier = 2)
  (hproj : IsProjectiveOverField (A.stage (n + 1)).structureMap)

local instance selectedPullbackOriginIdealMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The support of the kernel of the exceptional closed immersion is the curve `E`. -/
theorem globalExceptionalInclusion_ker_support :
    (globalExceptionalInclusion (A.stage n)).ker.support =
      (exceptionalPrimeCurveOf A n hA h0 hproj).closedSubset := by
  apply TopologicalSpace.Closeds.ext
  rw [Scheme.Hom.support_ker]
  exact (range_globalExceptionalInclusion_isClosed A n).closure_eq

/-- The kernel of the exceptional closed immersion is the vanishing ideal of `E`. -/
theorem globalExceptionalInclusion_ker :
    (globalExceptionalInclusion (A.stage n)).ker =
      (exceptionalPrimeCurveOf A n hA h0 hproj).vanishingIdeal := by
  rw [← SchematicImageDenseOpen.ker_radical (globalExceptionalInclusion (A.stage n)),
    ← Scheme.IdealSheafData.vanishingIdeal_support, globalExceptionalInclusion_ker_support]
  rfl

/-- The centre fibre factors through the prime-curve scheme of `E`. -/
def exceptionalLiftOf :
    globalExceptionalScheme (A.stage n) ⟶ (exceptionalPrimeCurveOf A n hA h0 hproj).toScheme :=
  GluedIdealSheafLift.liftGlued (exceptionalPrimeCurveOf A n hA h0 hproj).vanishingIdeal
    (globalExceptionalInclusion (A.stage n)) (globalExceptionalInclusion_ker A n hA h0 hproj).ge

@[reassoc] theorem exceptionalLiftOf_inclusion :
    exceptionalLiftOf A n hA h0 hproj ≫ (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion =
      globalExceptionalInclusion (A.stage n) :=
  GluedIdealSheafLift.liftGlued_gluedTo _ _ _

instance exceptionalLiftOf_isClosedImmersion :
    IsClosedImmersion (exceptionalLiftOf A n hA h0 hproj) := by
  haveI : IsClosedImmersion
      (exceptionalLiftOf A n hA h0 hproj ≫ (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion) := by
    rw [exceptionalLiftOf_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion

instance exceptionalLiftOf_surjective : Surjective (exceptionalLiftOf A n hA h0 hproj) := by
  refine ⟨fun y => ?_⟩
  have hy : (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion.base y ∈
      (exceptionalPrimeCurveOf A n hA h0 hproj :
        Set (stageSurfaceOf A hA h0 (n + 1) hproj).toScheme) := by
    rw [← PrimeCurve.range_inclusion]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion.isClosedEmbedding.injective ?_⟩
  rw [← hz, ← exceptionalLiftOf_inclusion A n hA h0 hproj, Scheme.comp_base_apply]
  rfl

instance exceptionalLiftOf_isIso : IsIso (exceptionalLiftOf A n hA h0 hproj) :=
  isIso_of_isClosedImmersion_of_surjective _

theorem inclusion_eq_inv_exceptionalLiftOf :
    (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion =
      inv (exceptionalLiftOf A n hA h0 hproj) ≫ globalExceptionalInclusion (A.stage n) := by
  rw [← exceptionalLiftOf_inclusion A n hA h0 hproj, IsIso.inv_hom_id_assoc]

/-- The prime curve `E` maps to the closed centre `Spec (k[u][v]/m)`. -/
def exceptionalToCentreOf :
    (exceptionalPrimeCurveOf A n hA h0 hproj).toScheme ⟶
      Spec (CommRingCat.of (planeRing k ⧸ (originPoint (k := k)).asIdeal)) :=
  inv (exceptionalLiftOf A n hA h0 hproj) ≫
    PointBlowupGluing.globalCenterFiberToCenter (A.stage n).chart (originPoint (k := k))
      (A.stage n).center_closed

/-- `E` followed by the step projection factors through the closed centre. -/
theorem inclusion_comp_stepProjection_of :
    (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion ≫ A.stepProjection n =
      exceptionalToCentreOf A n hA h0 hproj ≫
        PointBlowupGluing.closedCenterInclusion (A.stage n).chart (originPoint (k := k)) := by
  rw [inclusion_eq_inv_exceptionalLiftOf, exceptionalToCentreOf, Category.assoc, Category.assoc]
  congr 1
  exact pullback.condition

/-- **`E · π^*L = 0`** on the stage surface of any charted plane. -/
theorem restrictionDegree_pullback_stepProjectionOf (L : InvertibleSheaf (A.stage n).carrier) :
    (exceptionalPrimeCurveOf A n hA h0 hproj).restrictionDegree
      (pullbackInvertibleSheaf (A.stepProjection n) L) = 0 := by
  letI : Field (planeRing k ⧸ (originPoint (k := k)).asIdeal) := Ideal.Quotient.field _
  unfold PrimeCurve.restrictionDegree
  apply (exceptionalPrimeCurveOf A n hA h0 hproj).lineDegree_eq_zero_of_iso_unit
  refine ((schemeModulePullbackCompIso (exceptionalPrimeCurveOf A n hA h0 hproj).inclusion
    (A.stepProjection n)).app L.obj) ≪≫ ?_
  rw [inclusion_comp_stepProjection_of]
  refine ((schemeModulePullbackCompIso (exceptionalToCentreOf A n hA h0 hproj)
    (PointBlowupGluing.closedCenterInclusion (A.stage n).chart (originPoint (k := k)))).symm.app
      L.obj) ≪≫ ?_
  refine (schemeModulePullback (exceptionalToCentreOf A n hA h0 hproj)).mapIso
    (AffineModuleTilde.pidInvertibleUnitIso (pullbackInvertibleSheaf
      (PointBlowupGluing.closedCenterInclusion (A.stage n).chart (originPoint (k := k))) L)) ≪≫ ?_
  exact schemeModulePullbackUnitIso (exceptionalToCentreOf A n hA h0 hproj)

end KltDP.Examples.FrobeniusSelectedStageExceptionalPullback

namespace KltDP.Examples.FrobeniusSelectedStageExceptionalPullback

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface FrobeniusGlobalBlowupStages
open FrobeniusStageNormal FrobeniusStageDimension FrobeniusSelectedStageSurface
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance selectedPullbackInitialIsIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial (k := k) p a).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **`E · π^*L = 0` on every stage of the translated tower at `(a, a^p)`**: the exceptional prime
curve `selectedExceptionalPrimeCurve p a n hproj` of `selectedStage p a (n+1)` meets pulled-back line
bundles trivially. -/
theorem selected_restrictionDegree_pullback_stepProjection (p : ℕ) (a : k) (n : ℕ)
    (hproj : IsProjectiveOverField ((translatedInitial (k := k) p a).stage (n + 1)).structureMap)
    (L : InvertibleSheaf (selectedStage (k := k) p a n)) :
    (selectedExceptionalPrimeCurve p a n hproj).restrictionDegree
      (pullbackInvertibleSheaf ((translatedInitial (k := k) p a).stepProjection n) L) = 0 :=
  restrictionDegree_pullback_stepProjectionOf (translatedInitial p a) n
    projectiveProduct_isNormalScheme projectiveProduct_topologicalKrullDim hproj L

end KltDP.Examples.FrobeniusSelectedStageExceptionalPullback
