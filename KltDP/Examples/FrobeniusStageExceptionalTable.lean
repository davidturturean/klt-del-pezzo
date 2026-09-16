import KltDP.Examples.FrobeniusStageExceptionalPairing
import KltDP.Examples.FrobeniusStageOneProjective

/-!
# The manuscript's intersection table for the newest exceptional curve, and `E_i · E_j` (BRIEF13)

The `P`-row of Prop. 10.1's table on stage `n+1` of the origin contact tower, in `Additive Pic`
paired through lane D's restriction-degree homomorphism at the newest exceptional curve
`P = E_n`, together with the exceptional pairings `E_n · E_j^{tot} = −δ_{j,n}` (which, read at every
stage, is the manuscript's `E_i · E_j = −δ_{ij}` for `i ≤ j` in the form "the curve `E_j` against the
total transform of `E_i`"):

* general stage `n+1`: `f29_intersection_table k n hproj h0` with the explicit hypotheses
  `hproj : IsProjectiveOverField ((projectiveProductInitial).stage (n+1)).structureMap`,
  `h0 : FiberKernelInvertible 0` (lane F's stage-`0` fibre hypothesis, only for the two fibre rows)
  and `[IsAlgClosed k]`;
* stage `1` (`n = 0`): `hproj` is discharged by BRIEF11's `stage_one_projective`
  (`f29_intersection_table_stage_one`).

Not proved (recorded as open): the pairings of two *older* classes (`E_i · E_j` for `i, j < n`,
`B²`, `C_j²`, `C_j · C_{j+1}`, `F²`) on the top stage, which need lane D's symmetric
`picardEulerPairing` and the invariance `π^*D₁ · π^*D₂ = D₁ · D₂` (BRIEF13 item 1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageExceptionalTable

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageExceptionalPairing
open FrobeniusStrictTransformPicardStep FrobeniusStrictTransformClassesTower
open FrobeniusGraphPicardClassTotalTransform FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard
open FrobeniusStageOneProjective

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## Stage `1` without `hproj` -/

/-- The pairing `E_0 · (−)` on stage `1`, with no projectivity hypothesis. -/
abbrev stageOnePairing : Additive (projectiveContactStage (k := k) 1).Pic →+ ℤ :=
  exceptionalPairing 0 (stage_one_projective (k := k))

theorem stageOnePairing_self :
    stageOnePairing (k := k) (stepExceptionalPicardClass 0) = -1 :=
  exceptionalPairing_self 0 (stage_one_projective (k := k))

theorem stageOnePairing_strictCurve (m : ℕ) :
    stageOnePairing (k := k) (strictCurvePicardClass 1 m) = 1 :=
  exceptionalPairing_strictCurve 0 (stage_one_projective (k := k)) m

theorem stageOnePairing_firstFiber : stageOnePairing (k := k) (firstFiberTotalClass 1) = 0 :=
  exceptionalPairing_firstFiber 0 (stage_one_projective (k := k))

theorem stageOnePairing_secondFiber : stageOnePairing (k := k) (secondFiberTotalClass 1) = 0 :=
  exceptionalPairing_secondFiber 0 (stage_one_projective (k := k))

theorem stageOnePairing_fiberStrict (h0 : FiberKernelInvertible (k := k) 0) :
    stageOnePairing (k := k) (fiberPicardClass h0 1) = 1 :=
  exceptionalPairing_fiberStrict 0 (stage_one_projective (k := k)) h0

end KltDP.Examples.FrobeniusStageExceptionalTable

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageExceptionalPairing
open FrobeniusStrictTransformPicardStep FrobeniusStrictTransformClassesTower
open FrobeniusGraphPicardClassTotalTransform FrobeniusOldExceptionalLaterStages FrobeniusFiberPicard
open FrobeniusStageOneProjective FrobeniusStageExceptionalTable

/-- **Bundle (Prop. 10.1, the newest exceptional curve `P = E_n` on stage `n+1`)**: in `Additive Pic`
paired through the restriction degree at `P`,
`P · E_j^{tot} = −δ_{j,n}` (so `P · P = −1`, `E_i · E_j = 0` for `i < j = n`),
`P · a = P · b = 0`, `P · B = 1`, `P · C_j = [j + 1 = n]`, `P · π^*F_0 = 0`, `P · F̃ = 1`. -/
theorem f29_intersection_table (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h0 : FiberKernelInvertible (k := k) 0) :
    (∀ j : Fin (n + 1), exceptionalPairing n hproj (totalExceptionalClass (n + 1) j) =
        if j = Fin.last n then -1 else 0) ∧
      exceptionalPairing n hproj (stepExceptionalPicardClass n) = -1 ∧
      exceptionalPairing n hproj (firstFiberTotalClass (n + 1)) = 0 ∧
      exceptionalPairing n hproj (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ m : ℕ, exceptionalPairing n hproj (strictCurvePicardClass (n + 1) m) = 1) ∧
      (∀ j : Fin n, exceptionalPairing n hproj (oldExceptionalStrictClass (n + 1) j.val (by omega)) =
        if j.succ = Fin.last n then 1 else 0) ∧
      exceptionalPairing n hproj (fiberTotalClass h0 (n + 1)) = 0 ∧
      exceptionalPairing n hproj (fiberPicardClass h0 (n + 1)) = 1 :=
  ⟨exceptionalPairing_totalExceptional n hproj, exceptionalPairing_self n hproj,
    exceptionalPairing_firstFiber n hproj, exceptionalPairing_secondFiber n hproj,
    exceptionalPairing_strictCurve n hproj, exceptionalPairing_oldExceptional n hproj,
    exceptionalPairing_fiberTotal n hproj h0, exceptionalPairing_fiberStrict n hproj h0⟩

/-- **Stage `1` without `hproj`**: the same table for `P = E_0` on the first blowup. -/
theorem f29_intersection_table_stage_one (k : Type u) [Field k] [IsAlgClosed k]
    (h0 : FiberKernelInvertible (k := k) 0) :
    stageOnePairing (k := k) (stepExceptionalPicardClass 0) = -1 ∧
      stageOnePairing (k := k) (firstFiberTotalClass 1) = 0 ∧
      stageOnePairing (k := k) (secondFiberTotalClass 1) = 0 ∧
      (∀ m : ℕ, stageOnePairing (k := k) (strictCurvePicardClass 1 m) = 1) ∧
      stageOnePairing (k := k) (fiberPicardClass h0 1) = 1 :=
  ⟨stageOnePairing_self, stageOnePairing_firstFiber, stageOnePairing_secondFiber,
    stageOnePairing_strictCurve, stageOnePairing_fiberStrict h0⟩

/-- The bundles have exactly one universe parameter. -/
theorem f29_intersection_table_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h0 : FiberKernelInvertible (k := k) 0) : True := by
  have _ := f29_intersection_table.{u} k n hproj h0
  have _ := f29_intersection_table_stage_one.{u} k h0
  trivial

end KltDP.Examples
