import KltDP.Examples.FrobeniusFiberZeroInvertible

/-!
# The full strict-transform class table on one contact tower

With lane F's `FrobeniusFiberZeroInvertible` discharging the stage-`0` hypothesis of
`FrobeniusFiberPicard` (the ideal of the strict fibre `y = 0` of `P¹ × P¹` is invertible), the fibre
classes of the lane become unconditional: `fiberClass N` is the class of the strict fibre `F_N` on stage
`N` and `fiberZeroTotalClass N` the total transform `F_0^{(N)}` of the class of the stage-`0` fibre
`y = 0`. This module exports the class table of the manuscript's Proposition 10.1 on every stage `N` of
one contact tower (`strictTransformClasses_tower_full`):

* `B = (m + N)·a + b − Σ_{j<N} E_j` (graph strict transform, `strictCurvePicardClass_tower`);
* `C_j = E_j − E_{j+1}` for all `j + 2 ≤ N` (`oldExceptionalStrictClasses_tower`);
* `F = F_0^{(N)} − Σ_{j<N} E_j` and the one-step relation `F_{n+1} = π^* F_n − E_n`
  (`fiberClass_tower`, `fiberClass_succ`);
* `P = E_{N}` on stage `N+1` is the newest exceptional class (`totalExceptionalClass_last`).

All classes live in `Additive (projectiveContactStage N).Pic : Type u` for `k : Type u`
(`strictTransformClasses_tower_full_universe_check`). The identification `F_0 = b` of the stage-`0`
fibre class with the accepted `b`-fibre class is lane F's and is not stated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformClassesFull

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages
open FrobeniusFiberPicard FrobeniusFiberZeroInvertible

variable {k : Type u} [Field k]

/-- The class of the strict fibre `F_N` on stage `N` (ideal-sheaf sign convention), unconditional. -/
def fiberClass (N : ℕ) : Additive (projectiveContactStage (k := k) N).Pic :=
  fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) N

/-- The total transform on stage `N` of the class of the stage-`0` strict fibre `y = 0`. -/
def fiberZeroTotalClass (N : ℕ) : Additive (projectiveContactStage (k := k) N).Pic :=
  fiberTotalClass (fiberKernel_zero_isInvertible (k := k)) N

/-- `F_{n+1} = π^* F_n − E_n` on stage `n+1`. -/
theorem fiberClass_succ (n : ℕ) :
    fiberClass (k := k) (n + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (fiberClass n) - stepExceptionalPicardClass (k := k) n :=
  fiberPicardClass_succ (fiberKernel_zero_isInvertible (k := k)) n

/-- `F_N = F_0^{(N)} − Σ_{j<N} E_j^{(N)}` on stage `N`. -/
theorem fiberClass_tower (N : ℕ) :
    fiberClass (k := k) N = fiberZeroTotalClass N - ∑ j : Fin N, totalExceptionalClass N j :=
  fiberPicardClass_tower (fiberKernel_zero_isInvertible (k := k)) N

end KltDP.Examples.FrobeniusStrictTransformClassesFull

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPicardStep
open FrobeniusGraphPicardClassTotalTransform
open FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages
open FrobeniusStrictTransformClassesFull

/-- The class table of Proposition 10.1 on every stage `N` of one contact tower, in
`Additive (projectiveContactStage N).Pic`: `B`, `C_j`, `F` (iteration and one-step relation) and `P`. -/
theorem strictTransformClasses_tower_full (k : Type u) [Field k] :
    (∀ N m : ℕ, strictCurvePicardClass (k := k) N m =
      (m + N) • firstFiberTotalClass N + secondFiberTotalClass N -
        ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
      oldExceptionalStrictClass (k := k) N j h =
        totalExceptionalClass N ⟨j, by omega⟩ - totalExceptionalClass N ⟨j + 1, by omega⟩) ∧
    (∀ N : ℕ, fiberClass (k := k) N =
      fiberZeroTotalClass N - ∑ j : Fin N, totalExceptionalClass N j) ∧
    (∀ n : ℕ, fiberClass (k := k) (n + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (fiberClass n) - stepExceptionalPicardClass n) ∧
    (∀ N : ℕ, totalExceptionalClass (k := k) (N + 1) (Fin.last N) =
      stepExceptionalPicardClass N) :=
  ⟨strictCurvePicardClass_tower, oldExceptionalStrictClasses_tower, fiberClass_tower,
    fiberClass_succ, totalExceptionalClass_last⟩

/-- The bundle has exactly one universe parameter. -/
theorem strictTransformClasses_tower_full_universe_check (k : Type u) [Field k] : True := by
  have _ := strictTransformClasses_tower_full.{u} k
  trivial

end KltDP.Examples
