import KltDP.Examples.FrobeniusStageNormal
import KltDP.Examples.FrobeniusStageDimension
import KltDP.Examples.FrobeniusGlobalExceptionalBase
import KltDP.Examples.FrobeniusStrictTransformProductKernel
import KltDP.Geometry.SmoothSurfaceRegularity
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.PrimeDivisor

/-!
# The contact-tower stages as normal projective surfaces, and `E` as a prime curve

`stageSurface n hproj : NormalProjectiveSurface k` packages the stage `projectiveContactStage n` of
the Frobenius contact tower with the accepted structure (integrality: accepted `stage_isIntegral`;
normality: `projectiveContactStage_isNormalScheme`; dimension two:
`projectiveContactStage_topologicalKrullDim`, which needs `IsAlgClosed k`). **Projectivity is an
explicit hypothesis** `hproj : IsProjectiveOverField (stage n).structureMap`: the accepted
definition asks for a closed immersion into some `projectiveSpace k m` over `k`, and neither the
pinned Mathlib (no `Proj.map`, no Segre or Veronese embedding) nor the accepted tree provides such an
embedding for `P¹ ×_k P¹` or for its point blowups. Nothing else is assumed.

The surface is smooth over `k` (accepted `projectiveContactStage_structure_smooth`), hence every
point is regular (`stageSurface_regularPoints`, accepted `regularPoints_of_isSmooth`).

The newest exceptional curve `E` of stage `n + 1` (the accepted closed immersion
`stepExceptionalInclusion n` of the categorical centre fibre, isomorphic to `P¹` by the accepted
`globalExceptionalProjectiveLineIso`) is realised as an actual `PrimeCurve` of `stageSurface (n+1)`:
its range is an irreducible closed subset of dimension one (`exceptionalPrimeCurve`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStageSurface

open KltDP.Geometry
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth
open FrobeniusGlobalExceptionalNormal FrobeniusGlobalExceptionalBase
open FrobeniusStrictTransformProductKernel FrobeniusStageNormal FrobeniusStageDimension
open FrobeniusTowerFunctionField.PlaneChartedScheme

variable {k : Type u} [Field k]

local instance stageSurfaceInitialIsIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **Stage `n` of the contact tower as a normal projective surface**, given a closed projective
embedding of the stage over `k` (`hproj`). Integrality, normality and dimension two are proved. -/
def stageSurface [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap) :
    NormalProjectiveSurface k where
  toScheme := projectiveContactStage (k := k) n
  structureMorphism := ((projectiveProductInitial (k := k)).stage n).structureMap
  integral := instStageIsIntegral (projectiveProductInitial (k := k)) n
  normal := projectiveContactStage_isNormalScheme n
  projective := hproj
  dimension_two := projectiveContactStage_topologicalKrullDim n

@[simp] theorem stageSurface_toScheme [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap) :
    (stageSurface n hproj).toScheme = projectiveContactStage (k := k) n := rfl

@[simp] theorem stageSurface_structureMorphism [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap) :
    (stageSurface n hproj).structureMorphism =
      ((projectiveProductInitial (k := k)).stage n).structureMap := rfl

/-- The surface's structure morphism is the accepted smooth one. -/
instance stageSurface_structure_isSmooth [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap) :
    IsSmooth (stageSurface n hproj).structureMorphism :=
  projectiveContactStage_structure_smooth n

/-- Every point of the stage surface is regular (smooth over an algebraically closed field). -/
theorem stageSurface_regularPoints [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage n).structureMap) :
    ∀ x : (stageSurface n hproj).Point, RegularPoint (stageSurface n hproj).toScheme x :=
  (stageSurface n hproj).regularPoints_of_isSmooth

section exceptional

local instance stageSurfaceOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

local instance stageSurfaceProjectiveLineIsIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

variable (n : ℕ)

/-- The exceptional fibre scheme of the `(n+1)`-st blowup is nonempty (it is `P¹`). -/
instance globalExceptionalScheme_nonempty :
    Nonempty (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)) :=
  ⟨(globalExceptionalProjectiveLineIso ((projectiveProductInitial (k := k)).stage n)).inv.base
    (projectiveSpace_nonempty k 1).some⟩

/-- The exceptional fibre scheme is integral (it is isomorphic to `P¹`). -/
instance globalExceptionalScheme_isIntegral :
    IsIntegral (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)) :=
  isIntegral_of_isOpenImmersion
    (globalExceptionalProjectiveLineIso ((projectiveProductInitial (k := k)).stage n)).hom

/-- The exceptional fibre scheme has dimension one. -/
theorem globalExceptionalScheme_topologicalKrullDim :
    topologicalKrullDim (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)) =
      1 := by
  let e := globalExceptionalProjectiveLineIso ((projectiveProductInitial (k := k)).stage n)
  calc
    topologicalKrullDim (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n)) =
        topologicalKrullDim (projectiveSpace k 1) :=
      IsHomeomorph.topologicalKrullDim_eq e.schemeIsoToHomeo e.schemeIsoToHomeo.isHomeomorph
    _ = ((1 : ℕ) : WithBot ℕ∞) := projectiveSpace_topologicalKrullDim k 1
    _ = 1 := Nat.cast_one

/-- The range of the exceptional curve is irreducible. -/
theorem range_stepExceptionalInclusion_isIrreducible :
    IsIrreducible (Set.range (stepExceptionalInclusion (k := k) n).base) := by
  have h := (IrreducibleSpace.isIrreducible_univ
    (globalExceptionalScheme ((projectiveProductInitial (k := k)).stage n))).image
    (stepExceptionalInclusion (k := k) n).base
    (stepExceptionalInclusion (k := k) n).continuous.continuousOn
  simpa only [Set.image_univ] using h

/-- The range of the exceptional curve is closed. -/
theorem range_stepExceptionalInclusion_isClosed :
    IsClosed (Set.range (stepExceptionalInclusion (k := k) n).base) :=
  (stepExceptionalInclusion (k := k) n).isClosedEmbedding.isClosed_range

/-- The range of the exceptional curve has dimension one. -/
theorem range_stepExceptionalInclusion_topologicalKrullDim :
    topologicalKrullDim (Set.range (stepExceptionalInclusion (k := k) n).base) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (stepExceptionalInclusion (k := k) n).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm.trans
    (globalExceptionalScheme_topologicalKrullDim n)

variable [IsAlgClosed k]
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **The newest exceptional curve `E` as a prime curve** of the stage-`(n+1)` surface: the
irreducible closed dimension-one range of the accepted closed immersion `stepExceptionalInclusion n`. -/
def exceptionalPrimeCurve : (stageSurface (n + 1) hproj).PrimeCurve :=
  ⟨⟨Set.range (stepExceptionalInclusion (k := k) n).base,
      range_stepExceptionalInclusion_isIrreducible n,
      range_stepExceptionalInclusion_isClosed n⟩,
    range_stepExceptionalInclusion_topologicalKrullDim n⟩

@[simp] theorem coe_exceptionalPrimeCurve :
    (exceptionalPrimeCurve n hproj : Set (stageSurface (n + 1) hproj).toScheme) =
      Set.range (stepExceptionalInclusion (k := k) n).base := rfl

end exceptional

end KltDP.Examples.FrobeniusStageSurface
