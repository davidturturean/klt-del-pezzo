import KltDP.Geometry.PointBlowupExceptionalPullbackPairing
import KltDP.Examples.FrobeniusStageOneProjective
import KltDP.Examples.FrobeniusStageExceptionalSelfIntersection
import KltDP.Examples.FrobeniusStageZeroProjective

/-!
# The Picard splitting on an actual surface: stage one of the Frobenius contact tower

BRIEF36, task 1. This is the **nonvacuity witness** for the F09 Picard thread: every earlier statement in
the thread (`picardDecomposition'`, `picardDecomposition''`, `mem_ker_iff`, `kernelEquivInt`) either
carries a hypothesis `hres`, or lane E's three Stacks literals, or an abstract retraction. Here the whole
splitting holds on a concrete surface with **no literature hypothesis and no projectivity hypothesis at
all**: stage `1` of the Frobenius contact tower, the blowup of `P¹ ×_k P¹` at the origin of its
coordinate chart.

Everything is assembled from accepted material plus lane A1's own modules; nothing new is assumed.

* Stage `n + 1` **is** the accepted glued point blowup: `nextScheme` is an `abbrev` for
  `PointBlowupGluing.scheme A.chart originPoint A.center_closed`, and `stepProjection n` is
  `PointBlowupGluing.projection` of the same data. So the accepted `PointBlowupPicard` retraction
  machinery applies directly at `A := projectiveProductInitial`, with no transport.
* The exceptional curve is accepted: `exceptionalPrimeCurve 0` with `coe_exceptionalPrimeCurve` a `rfl`
  to `Set.range (stepExceptionalInclusion 0).base`, and `stepExceptionalInclusion 0` is the accepted
  `globalCenterFiberι` of that data. Hence **`coe_stageOneExceptionalCurve`**: its underlying set is the
  fibre over the centre, by the accepted `range_globalCenterFiberι` — this is the range identity the
  brief asked for, and it is a transport of accepted material rather than new work.
* **`complementOpen_stageOneExceptionalCurve`**: the complement of `E` is the accepted
  `exceptionalComplementOpen`, hence (definitionally) the open of the accepted `restrictComplement`.
* The retraction is BRIEF29's `retraction`, whose hypothesis `hres` is discharged by BRIEF31's
  `restrictPuncture_bijective` on the **base** surface `projectiveProductSurface = stageSurface 0`,
  whose stalks are factorial because every point is regular (accepted `stageSurface_regularPoints`,
  smoothness over an algebraically closed field).
* Infinite order comes from the accepted unconditional `f09_exceptional_self_intersection_stage_one`
  (`E · E = −1`, stated with `stageRegular 0`, which is an `abbrev` for `stageSurface_regularPoints 1`)
  through BRIEF32's `infiniteOrder_of_intersectionNumber_neg_one`.

**`stageOnePicardSplitting : Nonempty (Pic (stage 1) ≃* Pic (P¹ × P¹) × Multiplicative ℤ)`.**
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStageOnePicardSplitting

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PrimeCurveComplementKernel
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStageZeroProjective FrobeniusStageOneProjective
open FrobeniusStageExceptionalSelfIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance stageOneSplittingOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-! ## The blowup data of stage one -/

/-- The blowup data: stage `1` is the glued point blowup of stage `0` at the origin of its chart. -/
abbrev baseChart : plane k ⟶ (projectiveProductInitial (k := k)).carrier :=
  (projectiveProductInitial (k := k)).chart

theorem stageOne_scheme_eq :
    projectiveContactStage (k := k) 1 =
      PointBlowupGluing.scheme (baseChart (k := k)) (originPoint (k := k))
        (projectiveProductInitial (k := k)).center_closed := rfl

theorem stageOne_projection_eq :
    (projectiveProductInitial (k := k)).stepProjection 0 =
      PointBlowupGluing.projection (baseChart (k := k)) (originPoint (k := k))
        (projectiveProductInitial (k := k)).center_closed := rfl

/-! ## The range identity for the exceptional curve -/

/-- **The range identity**: the exceptional curve of stage one is the fibre over the centre. The
accepted `coe_exceptionalPrimeCurve` is `rfl` to `Set.range (stepExceptionalInclusion 0).base`, which is
the accepted `globalCenterFiberι` of the blowup data, so this is the accepted
`range_globalCenterFiberι`. -/
theorem coe_stageOneExceptionalCurve :
    ((stageOneExceptionalCurve (k := k) :
        (stageOneSurface (k := k)).PrimeCurve) :
        Set (stageOneSurface (k := k)).toScheme) =
      (PointBlowupGluing.projection (baseChart (k := k)) (originPoint (k := k))
        (projectiveProductInitial (k := k)).center_closed).base ⁻¹'
          {(baseChart (k := k)).base (originPoint (k := k))} :=
  PointBlowupGluing.range_globalCenterFiberι (baseChart (k := k)) (originPoint (k := k))
    (projectiveProductInitial (k := k)).center_closed

/-- **The complement of `E` is the accepted `exceptionalComplementOpen`.** -/
theorem complementOpen_stageOneExceptionalCurve :
    complementOpen (stageOneExceptionalCurve (k := k)) =
      PointBlowupGluing.exceptionalComplementOpen (baseChart (k := k)) (originPoint (k := k))
        (projectiveProductInitial (k := k)).center_closed := by
  apply TopologicalSpace.Opens.ext
  show ((stageOneExceptionalCurve (k := k) : (stageOneSurface (k := k)).PrimeCurve) :
      Set (stageOneSurface (k := k)).toScheme)ᶜ = _
  rw [coe_stageOneExceptionalCurve]
  rfl

/-! ## The retraction -/

/-- Stage `0` is `P¹ ×_k P¹` as a normal projective surface, with factorial stalks: every point is
regular (accepted `stageSurface_regularPoints`, smoothness over an algebraically closed field). -/
theorem baseSurface_regular :
    ∀ x : (projectiveProductSurface (k := k)).Point,
      RegularPoint (projectiveProductSurface (k := k)).toScheme x :=
  stageSurface_regularPoints 0 (stage_zero_projective (k := k))

/-- The hypothesis `hres` of BRIEF29's `picardDecomposition`, discharged on the base. -/
theorem stageOne_restrictPuncture_bijective :
    haveI := (projectiveProductSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
      (baseSurface_regular (k := k))
    Function.Bijective (PointBlowupPicard.restrictPuncture (baseChart (k := k))
      (originPoint (k := k)) (projectiveProductInitial (k := k)).center_closed) := by
  haveI := (projectiveProductSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
    (baseSurface_regular (k := k))
  exact CartierExtension.restrictPuncture_bijective (X := projectiveProductSurface (k := k))
    (baseChart (k := k)) (originPoint (k := k))
    (projectiveProductInitial (k := k)).center_closed

/-! ## Infinite order of the exceptional class -/

/-- The exceptional class of stage one has infinite order, from the accepted unconditional
`E · E = −1`. -/
theorem stageOne_infiniteOrder :
    haveI := (stageOneSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
      (stageRegular 0 (stage_one_projective (k := k)))
    InfiniteOrder (primeCurveClass (stageOneExceptionalCurve (k := k))) := by
  haveI := (stageOneSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
    (stageRegular 0 (stage_one_projective (k := k)))
  refine infiniteOrder_of_intersectionNumber_neg_one (stageOneExceptionalCurve (k := k)) ?_
  exact f09_exceptional_self_intersection_stage_one k

/-! ## The splitting -/

/-- **The F09 Picard splitting on an actual surface**: for stage `1` of the Frobenius contact tower —
the blowup of `P¹ ×_k P¹` at the origin of its coordinate chart —
`Pic (stage 1) ≃* Pic (P¹ × P¹) × ℤ`, with **no literature hypothesis and no projectivity
hypothesis**. This is the nonvacuity witness for the whole F09 Picard thread. -/
theorem stageOnePicardSplitting :
    Nonempty ((projectiveContactStage (k := k) 1).Pic ≃*
      (projectiveContactStage (k := k) 0).Pic × Multiplicative ℤ) := by
  haveI := (projectiveProductSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
    (baseSurface_regular (k := k))
  haveI := (stageOneSurface (k := k)).stalks_uniqueFactorizationMonoid_of_regular
    (stageRegular 0 (stage_one_projective (k := k)))
  have hres := stageOne_restrictPuncture_bijective (k := k)
  have hV : ∀ C : (stageOneSurface (k := k)).PrimeCurve,
      C.genericPoint ∈ complementOpen (stageOneExceptionalCurve (k := k)) ↔
        C ≠ stageOneExceptionalCurve (k := k) :=
    genericPoint_mem_complementOpen_iff (stageOneExceptionalCurve (k := k))
  have hker : (PointBlowupPicard.retraction (baseChart (k := k)) (originPoint (k := k))
        (projectiveProductInitial (k := k)).center_closed hres).ker =
      (schemePicardPullbackHom (complementOpen (stageOneExceptionalCurve (k := k))).ι).ker := by
    rw [PointBlowupPicard.ker_retraction]
    show (schemePicardPullbackHom (PointBlowupGluing.exceptionalComplementOpen
      (baseChart (k := k)) (originPoint (k := k))
      (projectiveProductInitial (k := k)).center_closed).ι).ker = _
    rw [complementOpen_stageOneExceptionalCurve]
  show Nonempty ((stageOneSurface (k := k)).toScheme.Pic ≃*
    (projectiveProductSurface (k := k)).toScheme.Pic × Multiplicative ℤ)
  exact ⟨picardEquivProdInt (stageOneExceptionalCurve (k := k)) hV (stageOne_infiniteOrder (k := k))
    (PointBlowupPicard.pullbackHom (baseChart (k := k)) (originPoint (k := k))
      (projectiveProductInitial (k := k)).center_closed)
    (PointBlowupPicard.retraction (baseChart (k := k)) (originPoint (k := k))
      (projectiveProductInitial (k := k)).center_closed hres)
    (PointBlowupPicard.retraction_pullback (baseChart (k := k)) (originPoint (k := k))
      (projectiveProductInitial (k := k)).center_closed hres) hker⟩

/-- Universe check at `Type`/`Scheme.{0}`. -/
example (k₀ : Type) [Field k₀] [IsAlgClosed k₀] :
    Nonempty ((projectiveContactStage (k := k₀) 1).Pic ≃*
      (projectiveContactStage (k := k₀) 0).Pic × Multiplicative ℤ) :=
  stageOnePicardSplitting

end KltDP.Examples.FrobeniusStageOnePicardSplitting
