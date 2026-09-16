import KltDP.Examples.FrobeniusOldExceptionalSelfRow
import KltDP.Examples.FrobeniusOldExceptionalLaterStages

/-!
# Rows `C_j · C_i` of the older exceptional chain (BRIEF14, item 3, class form)

With the accepted class relation `[C_i] = E_i^tot − E_{i+1}^tot` (`oldExceptionalStrictClass_eq'`) and the
rows `C_j · E_i^tot = 0` (`i < j`), `C_j · E_j^tot = −1` of `FrobeniusStrictTransformPairing` /
`FrobeniusOldExceptionalSelfRow`:

* `C_j · [C_i] = 0` for `i + 2 ≤ j` (non-adjacent older curves, unconditional);
* `C_j · [C_{j−1}] = 1` (adjacent older curves meet once), given the projectivity of stage `j+1`;
* `C_j · [C_j] = −2` given additionally the row `C_j · E_{j+1}^tot = 1` (transversality, not proved here).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalChainRows

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
open FrobeniusOldExceptionalLaterStages FrobeniusStrictTransformPairing
open FrobeniusOldExceptionalSelfRow

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
  (j : ℕ) (h : j + 2 ≤ n + 1)

/-- **`C_j · C_i = 0` for `i + 2 ≤ j`** (class form). -/
theorem oldExceptionalPairing_oldStrictClass_of_lt (i : ℕ) (hi : i + 2 ≤ j) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i (by omega)) = 0 := by
  rw [oldExceptionalStrictClass_eq', map_sub,
    oldExceptionalPairing_totalExceptional_of_lt n hproj j h ⟨i, by omega⟩ (show i < j by omega),
    oldExceptionalPairing_totalExceptional_of_lt n hproj j h ⟨i + 1, by omega⟩
      (show i + 1 < j by omega), sub_zero]

/-- **`C_j · C_{j−1} = 1`**: adjacent older curves meet once (class form), given the projectivity of
stage `j+1`. -/
theorem oldExceptionalPairing_oldStrictClass_pred (hj : 1 ≤ j)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) (j - 1) (by omega)) = 1 := by
  rw [oldExceptionalStrictClass_eq', map_sub,
    oldExceptionalPairing_totalExceptional_of_lt n hproj j h ⟨j - 1, by omega⟩
      (show j - 1 < j by omega)]
  have e : (⟨j - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨j, by omega⟩ := Fin.ext (Nat.sub_add_cancel hj)
  rw [e, oldExceptionalPairing_totalExceptional_self n hproj j h hprojj, sub_neg_eq_add, zero_add]

/-- **`C_j · C_j = −2`** (class form), given the projectivity of stage `j+1` and the transversality
row `C_j · E_{j+1}^tot = 1`. -/
theorem oldExceptionalPairing_oldStrictClass_self
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap)
    (hrow : oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) ⟨j + 1, by omega⟩) = 1) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) j (by omega)) = -2 := by
  rw [oldExceptionalStrictClass_eq', map_sub,
    oldExceptionalPairing_totalExceptional_self n hproj j h hprojj, hrow]
  norm_num

end KltDP.Examples.FrobeniusOldExceptionalChainRows

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusOldExceptionalLaterStages
  FrobeniusStrictTransformPairing FrobeniusOldExceptionalChainRows

/-- **Non-adjacent older curves do not meet**: `C_j · [C_i] = 0` for `i + 2 ≤ j` on
`stageSurface (n+1) hproj`. -/
theorem f29_old_exceptional_chain_zero (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) (i : ℕ) (hi : i + 2 ≤ j) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i (by omega)) = 0 :=
  oldExceptionalPairing_oldStrictClass_of_lt n hproj j h i hi

/-- **Adjacent older curves meet once**: `C_j · [C_{j−1}] = 1` on `stageSurface (n+1) hproj`, given
the projectivity of stage `j+1`. -/
theorem f29_old_exceptional_chain_adjacent (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) (hj : 1 ≤ j)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) (j - 1) (by omega)) = 1 :=
  oldExceptionalPairing_oldStrictClass_pred n hproj j h hj hprojj

/-- The bundles have exactly one universe parameter. -/
theorem f29_old_exceptional_chain_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) (hj : 1 ≤ j)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap) : True := by
  have _ := f29_old_exceptional_chain_adjacent.{u} k n hproj j h hj hprojj
  trivial

end KltDP.Examples
