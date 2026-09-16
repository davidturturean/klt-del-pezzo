import KltDP.Examples.FrobeniusStageProjectiveOfLiteral
import KltDP.Examples.FrobeniusOldExceptionalAdjacentRows
import KltDP.Examples.FrobeniusStrictTransformFiberRows
import KltDP.Examples.FrobeniusFiberZeroInvertible
import KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue

/-!
# The F29 intersection table with the literal as its only hypothesis (BRIEF20, item 2)

`f29_intersection_table_of_literal k hlit n` collects, on stage `n + 1` of the origin contact tower over
an algebraically closed field, the accepted and queued rows of the table. Every projectivity hypothesis
(`hproj` of stage `n + 1`, `hprojj` of the stages `j + 1`, `hstages` of the stages `2, …, n`) is supplied
by `stage_isProjective_of_literal hlit`. Lane F's fibre hypothesis is `h0 := f29_fiber_zero_invertible`.
The only hypothesis left is `hlit : RegularProperProjectiveLiteral k` (Stacks 0C5P). The rows are:

* BRIEF19 `f29_intersection_table_adjacent`. It contains BRIEF16's `f29_intersection_table_extended`:
  BRIEF13's table of `P = E_n` (`P · E_j^tot = −δ`, `P · P = −1`, `P · a = P · b = 0`, `P · B = 1`,
  `P · C_j = [j + 1 = n]`, `P · π^*F_0 = 0`, `P · F̃ = 1`); the rows `C_j · a = C_j · b = 0`,
  `C_j · E_i^tot = 0` (`i < j`) and `C_j · C_i = 0` (`i + 2 ≤ j`); and `F̃ · b = 0`. On top of that it has
  `C_j · E_{j+1}^tot = 1`, `C_j · C_j = −2`, **`C_j · C_{j+1} = 1`**, now without the stage-`j+2`
  assumption, and `C_{n−1} · P = 1`.
* BRIEF14 `C_j · E_j^tot = −1` and `C_j · C_{j−1} = 1`; BRIEF16 `C_j · E_i^tot = 0` (`i ≥ j + 2`) and
  `C_j · C_i = 0` for all non-adjacent pairs.
* Lane D's `E_n · E_n = −1` in `selfIntersectionNumber` (`f09_exceptional_self_intersection`).
* BRIEF15's reduction of `B · a`, `B · b`, `F̃ · a`, `F̃ · b` to Euler degrees on `P¹`
  (`f29_strict_transform_fiber_rows_reduction`).

Not included: the BRIEF16–18 exponent and Laurent forms of the reduction, which are conditional on
the three parked `P¹` exponents; `B · B` and `F̃ · F̃` (not proved).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.PrimeCurveDegreeTransport KltDP.Literature.Stacks
  FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStrictTransformClassesTower
  FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformPairing
  FrobeniusOldExceptionalLaterStages FrobeniusOldExceptionalChainRows
  FrobeniusStrictTransformFiberRowsValues FrobeniusStageExceptionalPairing
  FrobeniusStrictTransformPicardStep FrobeniusFiberPicard FrobeniusOldExceptionalAdjacentRows
  FrobeniusStrictTransformFiberRows FrobeniusGraphPicardClassFiberClasses
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassZeroFiber FrobeniusProjectiveMorphism
  FrobeniusStageExceptionalSelfIntersection FrobeniusStageProjectiveOfLiteral

/-- **The F29 intersection table on stage `n + 1`, with Stacks 0C5P as the only hypothesis.** -/
theorem f29_intersection_table_of_literal (k : Type u) [Field k] [IsAlgClosed k]
    (hlit : RegularProperProjectiveLiteral k) (n : ℕ) :
    ((((∀ j : Fin (n + 1),
        exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
          (totalExceptionalClass (n + 1) j) = if j = Fin.last n then -1 else 0) ∧
      exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (stepExceptionalPicardClass n) = -1 ∧
      exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (firstFiberTotalClass (n + 1)) = 0 ∧
      exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ m : ℕ, exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (strictCurvePicardClass (n + 1) m) = 1) ∧
      (∀ j : Fin n, exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (oldExceptionalStrictClass (n + 1) j.val (by omega)) =
          if j.succ = Fin.last n then 1 else 0) ∧
      exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (fiberTotalClass (f29_fiber_zero_invertible k) (n + 1)) = 0 ∧
      exceptionalPairing n (stage_isProjective_of_literal hlit (n + 1))
        (fiberPicardClass (f29_fiber_zero_invertible k) (n + 1)) = 1) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1),
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
        (firstFiberTotalClass (n + 1)) = 0 ∧
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
        (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ i : Fin (n + 1), i.val < j →
        oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
          (totalExceptionalClass (n + 1) i) = 0) ∧
      (∀ (i : ℕ) (hi : i + 2 ≤ j),
        oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
          (oldExceptionalStrictClass (n + 1) i (by omega)) = 0)) ∧
    fiberStrictPairing n (stage_isProjective_of_literal hlit (n + 1))
      (secondFiberTotalClass (n + 1)) = 0) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1),
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
        (totalExceptionalClass (n + 1) ⟨j + 1, by omega⟩) = 1 ∧
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
        (oldExceptionalStrictClass (n + 1) j (by omega)) = -2) ∧
    (∀ (j : ℕ) (h : j + 3 ≤ n + 1),
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j (by omega)
        (oldExceptionalStrictClass (n + 1) (j + 1) (by omega)) = 1) ∧
    (∀ hn : 1 ≤ n,
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) (n - 1) (by omega)
        (stepExceptionalPicardClass n) = 1)) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1),
      oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
        (totalExceptionalClass (n + 1) ⟨j, by omega⟩) = -1 ∧
      (∀ i : Fin (n + 1), j + 2 ≤ i.val →
        oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
          (totalExceptionalClass (n + 1) i) = 0) ∧
      (∀ (i : ℕ) (hin : i + 2 ≤ n + 1), (i + 2 ≤ j ∨ j + 2 ≤ i) →
        oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
          (oldExceptionalStrictClass (n + 1) i hin) = 0) ∧
      (∀ hj : 1 ≤ j,
        oldExceptionalPairing n (stage_isProjective_of_literal hlit (n + 1)) j h
          (oldExceptionalStrictClass (n + 1) (j - 1) (by omega)) = 1)) ∧
    (exceptionalPrimeCurve n (stage_isProjective_of_literal hlit (n + 1))).selfIntersectionNumber
        (stageRegular n (stage_isProjective_of_literal hlit (n + 1))) = -1 ∧
    (∀ m : ℕ,
      graphStrictPairing n (stage_isProjective_of_literal hlit (n + 1)) m
          (firstFiberTotalClass (n + 1)) =
        -eulerDegree (graphSectionBase (m + (n + 1)))
          (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
            (verticalFiberIdealLine (k := k)).toPic) ∧
      graphStrictPairing n (stage_isProjective_of_literal hlit (n + 1)) m
          (secondFiberTotalClass (n + 1)) =
        -eulerDegree (graphSectionBase (m + (n + 1)))
          (schemePicardPullbackHom (projectiveGraphMorphism (k := k) (m + (n + 1)))
            (graphIdealLine (k := k) 0).toPic) ∧
      fiberStrictPairing n (stage_isProjective_of_literal hlit (n + 1))
          (firstFiberTotalClass (n + 1)) =
        -eulerDegree fiberSectionBase
          (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
            (verticalFiberIdealLine (k := k)).toPic) ∧
      fiberStrictPairing n (stage_isProjective_of_literal hlit (n + 1))
          (secondFiberTotalClass (n + 1)) =
        -eulerDegree fiberSectionBase
          (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
            (graphIdealLine (k := k) 0).toPic)) :=
  ⟨f29_intersection_table_adjacent k n (stage_isProjective_of_literal hlit (n + 1))
      (f29_fiber_zero_invertible k) (fun i _ _ => stage_isProjective_of_literal hlit i),
    fun j h => ⟨f29_old_exceptional_self_row k n (stage_isProjective_of_literal hlit (n + 1)) j h
        (stage_isProjective_of_literal hlit (j + 1)),
      (f29_old_exceptional_far_rows k n (stage_isProjective_of_literal hlit (n + 1)) j h).1,
      (f29_old_exceptional_far_rows k n (stage_isProjective_of_literal hlit (n + 1)) j h).2,
      fun hj => f29_old_exceptional_chain_adjacent k n (stage_isProjective_of_literal hlit (n + 1))
        j h hj (stage_isProjective_of_literal hlit (j + 1))⟩,
    f09_exceptional_self_intersection k n (stage_isProjective_of_literal hlit (n + 1)),
    fun m => f29_strict_transform_fiber_rows_reduction k n
      (stage_isProjective_of_literal hlit (n + 1)) m⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_intersection_table_of_literal_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (hlit : RegularProperProjectiveLiteral k) (n : ℕ) : True := by
  have _ := f29_intersection_table_of_literal.{u} k hlit n
  trivial

end KltDP.Examples
