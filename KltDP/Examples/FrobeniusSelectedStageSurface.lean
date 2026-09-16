import KltDP.Examples.FrobeniusStageSurface
import KltDP.Examples.FrobeniusContactTowerSelectedPoint

/-!
# Stage surfaces of an arbitrary charted plane, and of the translated towers `selectedStage p a n`

The normality proof of `FrobeniusStageNormal` is already stated for any `A : PlaneChartedScheme k`
with normal carrier. Here the dimension induction is stated for any `A` with integral carrier and
proper structure morphism (`PlaneChartedScheme.stage_topologicalKrullDim`), the surface constructor
for any such `A` with normal carrier of dimension two (`PlaneChartedScheme.stageSurfaceOf`), and the
exceptional curve of the `(n+1)`-st blowup as a prime curve of that surface
(`PlaneChartedScheme.exceptionalPrimeCurveOf`). Applied to lane F's translated initial data
`translatedInitial p a` (carrier `P¹ ×_k P¹`, blowing up the graph point `(a, a^p)`), this gives every
tower stage `selectedStage p a n` of the multi-centre construction as a normal projective surface
(`selectedStageSurface`), under the same explicit projectivity hypothesis `hproj` and `IsAlgClosed k`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusSelectedStageSurface

open KltDP.Geometry
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusProjectivePoints
open FrobeniusStageComplement FrobeniusStageComplement.PlaneChartedScheme
open FrobeniusGlobalExceptionalNormal FrobeniusGlobalExceptionalBase
open FrobeniusStageNormal FrobeniusStageDimension FrobeniusStageSurface
open FrobeniusTowerFunctionField.PlaneChartedScheme
open FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint

variable {k : Type u} [Field k]

namespace PlaneChartedScheme

variable (A : PlaneChartedScheme k)

section exceptionalRange

local instance selectedStageOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

local instance selectedStageProjectiveLineIsIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

variable (n : ℕ)

instance globalExceptionalScheme_nonempty' : Nonempty (globalExceptionalScheme (A.stage n)) :=
  ⟨(globalExceptionalProjectiveLineIso (A.stage n)).inv.base (projectiveSpace_nonempty k 1).some⟩

instance globalExceptionalScheme_isIntegral' : IsIntegral (globalExceptionalScheme (A.stage n)) :=
  isIntegral_of_isOpenImmersion (globalExceptionalProjectiveLineIso (A.stage n)).hom

theorem globalExceptionalScheme_topologicalKrullDim' :
    topologicalKrullDim (globalExceptionalScheme (A.stage n)) = 1 := by
  let e := globalExceptionalProjectiveLineIso (A.stage n)
  calc
    topologicalKrullDim (globalExceptionalScheme (A.stage n)) =
        topologicalKrullDim (projectiveSpace k 1) :=
      IsHomeomorph.topologicalKrullDim_eq e.schemeIsoToHomeo e.schemeIsoToHomeo.isHomeomorph
    _ = ((1 : ℕ) : WithBot ℕ∞) := projectiveSpace_topologicalKrullDim k 1
    _ = 1 := Nat.cast_one

theorem range_globalExceptionalInclusion_isIrreducible :
    IsIrreducible (Set.range (globalExceptionalInclusion (A.stage n)).base) := by
  have h := (IrreducibleSpace.isIrreducible_univ (globalExceptionalScheme (A.stage n))).image
    (globalExceptionalInclusion (A.stage n)).base
    (globalExceptionalInclusion (A.stage n)).continuous.continuousOn
  simpa only [Set.image_univ] using h

theorem range_globalExceptionalInclusion_isClosed :
    IsClosed (Set.range (globalExceptionalInclusion (A.stage n)).base) :=
  (globalExceptionalInclusion (A.stage n)).isClosedEmbedding.isClosed_range

theorem range_globalExceptionalInclusion_topologicalKrullDim :
    topologicalKrullDim (Set.range (globalExceptionalInclusion (A.stage n)).base) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (globalExceptionalInclusion (A.stage n)).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm.trans
    (globalExceptionalScheme_topologicalKrullDim' A n)

end exceptionalRange

variable [IsIntegral A.carrier] [IsProper A.structureMap]

/-- Dimension two propagates up the tower over any integral charted plane with proper structure
morphism (accepted `topologicalKrullDim_eq_of_proper_isomorphism_open` at the nonempty puncture). -/
theorem stage_topologicalKrullDim [IsAlgClosed k] (h0 : topologicalKrullDim A.carrier = 2) :
    ∀ n : ℕ, topologicalKrullDim (A.stage n).carrier = 2
  | 0 => h0
  | n + 1 => by
      letI : IsIntegral (A.stage n).carrier := instStageIsIntegral A n
      letI : IsIntegral (A.stage (n + 1)).carrier := instStageIsIntegral A (n + 1)
      letI : Nonempty (initialPuncture (A.stage n)) := initialPuncture_nonempty (A.stage n)
      letI : IsIso (A.stepProjection n ∣_ initialPuncture (A.stage n)) :=
        nextProjection_restrict_isIso (A.stage n)
      exact (topologicalKrullDim_eq_of_proper_isomorphism_open (A.stepProjection n)
        (A.stage n).structureMap (initialPuncture (A.stage n))).trans
        (stage_topologicalKrullDim h0 n)

/-- **Stage `n` over any charted plane as a normal projective surface**: the carrier is integral,
normal, of dimension two, with proper structure morphism; projectivity of the stage is the explicit
hypothesis `hproj`. -/
def stageSurfaceOf [IsAlgClosed k] (hA : IsNormalScheme A.carrier)
    (h0 : topologicalKrullDim A.carrier = 2) (n : ℕ)
    (hproj : IsProjectiveOverField (A.stage n).structureMap) : NormalProjectiveSurface k where
  toScheme := (A.stage n).carrier
  structureMorphism := (A.stage n).structureMap
  integral := instStageIsIntegral A n
  normal := FrobeniusStageNormal.PlaneChartedScheme.stage_isNormalScheme A hA n
  projective := hproj
  dimension_two := stage_topologicalKrullDim A h0 n

section exceptional

variable (n : ℕ) [IsAlgClosed k] (hA : IsNormalScheme A.carrier) (h0 : topologicalKrullDim A.carrier = 2)
  (hproj : IsProjectiveOverField (A.stage (n + 1)).structureMap)

/-- **The exceptional curve of the `(n+1)`-st blowup as a prime curve** of the stage-`(n+1)` surface
over any charted plane. -/
def exceptionalPrimeCurveOf : (stageSurfaceOf A hA h0 (n + 1) hproj).PrimeCurve :=
  ⟨⟨Set.range (globalExceptionalInclusion (A.stage n)).base,
      range_globalExceptionalInclusion_isIrreducible A n,
      range_globalExceptionalInclusion_isClosed A n⟩,
    range_globalExceptionalInclusion_topologicalKrullDim A n⟩

@[simp] theorem coe_exceptionalPrimeCurveOf :
    (exceptionalPrimeCurveOf A n hA h0 hproj : Set (stageSurfaceOf A hA h0 (n + 1) hproj).toScheme) =
      Set.range (globalExceptionalInclusion (A.stage n)).base := rfl

end exceptional

end PlaneChartedScheme

section selected

local instance selectedInitialIsIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial (k := k) p a).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Every stage of the translated tower at the graph point `(a, a^p)` is normal. -/
theorem selectedStage_isNormalScheme (p : ℕ) (a : k) (n : ℕ) :
    IsNormalScheme (selectedStage (k := k) p a n) :=
  FrobeniusStageNormal.PlaneChartedScheme.stage_isNormalScheme (translatedInitial p a)
    projectiveProduct_isNormalScheme n

/-- Every stage of the translated tower has dimension two. -/
theorem selectedStage_topologicalKrullDim [IsAlgClosed k] (p : ℕ) (a : k) (n : ℕ) :
    topologicalKrullDim (selectedStage (k := k) p a n) = 2 :=
  PlaneChartedScheme.stage_topologicalKrullDim (translatedInitial p a)
    projectiveProduct_topologicalKrullDim n

/-- **Stage `n` of the translated tower at `(a, a^p)` as a normal projective surface** (the towers
`T_a = selectedStage p a p` entering lane F's `S_{p,n}`), given a projective embedding `hproj`. -/
def selectedStageSurface [IsAlgClosed k] (p : ℕ) (a : k) (n : ℕ)
    (hproj : IsProjectiveOverField ((translatedInitial (k := k) p a).stage n).structureMap) :
    NormalProjectiveSurface k :=
  PlaneChartedScheme.stageSurfaceOf (translatedInitial p a) projectiveProduct_isNormalScheme
    projectiveProduct_topologicalKrullDim n hproj

@[simp] theorem selectedStageSurface_toScheme [IsAlgClosed k] (p : ℕ) (a : k) (n : ℕ)
    (hproj : IsProjectiveOverField ((translatedInitial (k := k) p a).stage n).structureMap) :
    (selectedStageSurface p a n hproj).toScheme = selectedStage (k := k) p a n := rfl

/-- The exceptional curve of the `(n+1)`-st blowup of the translated tower, as a prime curve. -/
def selectedExceptionalPrimeCurve [IsAlgClosed k] (p : ℕ) (a : k) (n : ℕ)
    (hproj : IsProjectiveOverField ((translatedInitial (k := k) p a).stage (n + 1)).structureMap) :
    (selectedStageSurface p a (n + 1) hproj).PrimeCurve :=
  PlaneChartedScheme.exceptionalPrimeCurveOf (translatedInitial p a) n projectiveProduct_isNormalScheme
    projectiveProduct_topologicalKrullDim hproj

end selected

end KltDP.Examples.FrobeniusSelectedStageSurface
