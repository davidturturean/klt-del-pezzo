import KltDP.Geometry.KernelLinePullbackOffRange
import KltDP.Geometry.IsoOfPunctureAndChart
import KltDP.Examples.FrobeniusOldExceptionalChainRows
import KltDP.Examples.FrobeniusStrictTransformProductKernel

/-!
# The rows `C_j · E_i^tot = 0` and `C_j · C_i = 0` for `i ≥ j + 2` (BRIEF16, table extension)

The older exceptional curve `C_j ⊆ stage (n+1)` blown down to the birth stage `i+1` of a later
exceptional curve `E_i` (`i ≥ j + 2`) is disjoint from `E_i` (accepted `finalOld_disjoint_newest`,
transported by `finalOldMap_between`), so the pullback of the ideal line of `E_i` to `C_j` is
trivial (`kernelLine_pullback_unitIso`) and **`C_j · E_i^tot = 0`**
(`oldExceptionalPairing_totalExceptional_of_ge`). With `[C_i] = E_i^tot − E_{i+1}^tot` this gives
**`C_j · C_i = 0` for `i ≥ j + 2`**, and together with BRIEF14's `i + 2 ≤ j` case, for all
non-adjacent pairs (`oldExceptionalPairing_oldStrictClass_of_far`). Bundle `f29_old_exceptional_far_rows`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalLaterRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.PrimeCurveInclusionLift
open KltDP.Geometry.IsoOfPunctureAndChart KltDP.Geometry.KernelLinePullbackOffRange
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusExceptionalFinalConfiguration FrobeniusGlobalExceptionalSuccessor
open FrobeniusStrictTransformClassesTower FrobeniusStrictTransformPrimeCurves
open FrobeniusStrictTransformPairing FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformProductKernel FrobeniusOldExceptionalLaterStages
open FrobeniusOldExceptionalChainRows

variable {k : Type u} [Field k]

/-- `C_j ⊆ stage N` blown down to the birth stage of `E_i` (`i ≥ j + 2`) misses `E_i`. -/
theorem finalOldMap_between_disjoint (N j : ℕ) (h : j + 2 ≤ N) (i : ℕ) (hi : j + 2 ≤ i)
    (hin : i + 1 ≤ N) :
    Disjoint (Set.range (finalOldMap (projectiveProductInitial (k := k)) N j h ≫
        between (projectiveProductInitial (k := k)) hin).base)
      (Set.range (stepExceptionalInclusion (k := k) i).base) := by
  rw [finalOldMap_between (projectiveProductInitial (k := k)) (show j + 2 ≤ i + 1 by omega) hin]
  exact finalOld_disjoint_newest (projectiveProductInitial (k := k)) i j hi

section Rows

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
  (j : ℕ) (h : j + 2 ≤ n + 1)

/-- **`C_j · E_i^tot = 0` for `i ≥ j + 2`**: the later exceptional curve misses `C_j`. -/
theorem oldExceptionalPairing_totalExceptional_of_ge (i : Fin (n + 1)) (hi : j + 2 ≤ i.val) :
    oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0 := by
  have hdisj : Disjoint (Set.range ((oldExceptionalPrimeCurve n hproj j h).inclusion ≫
      between (projectiveProductInitial (k := k)) i.isLt).base)
      (Set.range (stepExceptionalInclusion (k := k) i.val).base) := by
    rw [inclusion_eq_inv_lift (oldExceptionalPrimeCurve n hproj j h)
        (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl,
      Category.assoc, range_comp_base_of_isIso]
    exact finalOldMap_between_disjoint (n + 1) j h i.val hi i.isLt
  have hunit := kernelLine_pullback_unitIso (stepExceptionalInclusion (k := k) i.val)
    ((oldExceptionalPrimeCurve n hproj j h).inclusion ≫
      between (projectiveProductInitial (k := k)) i.isLt) hdisj
  rw [totalExceptionalClass, stepExceptionalPicardClass, map_neg, map_neg, neg_eq_zero]
  change (oldExceptionalPrimeCurve n hproj j h).picardRestrictionDegree
    (schemePicardPullbackHom (between (projectiveProductInitial (k := k)) i.isLt)
      (stepExceptionalIdealLine (k := k) i.val).toPic) = 0
  rw [schemePicardPullbackHom_toPic, PrimeCurve.picardRestrictionDegree_toPic]
  erw [PrimeCurve.restrictionDegree_pullback]
  exact (oldExceptionalPrimeCurve n hproj j h).lineDegree_eq_zero_of_iso_unit _ hunit

/-- **`C_j · C_i = 0` for `i ≥ j + 2`** (class form). -/
theorem oldExceptionalPairing_oldStrictClass_of_ge (i : ℕ) (hi : j + 2 ≤ i) (hin : i + 2 ≤ n + 1) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i hin) = 0 := by
  rw [oldExceptionalStrictClass_eq', map_sub,
    oldExceptionalPairing_totalExceptional_of_ge n hproj j h ⟨i, by omega⟩ hi,
    oldExceptionalPairing_totalExceptional_of_ge n hproj j h ⟨i + 1, by omega⟩
      (show j + 2 ≤ i + 1 by omega),
    sub_zero]

/-- **Non-adjacent older curves do not meet**: `C_j · C_i = 0` whenever `|i − j| ≥ 2`. -/
theorem oldExceptionalPairing_oldStrictClass_of_far (i : ℕ) (hin : i + 2 ≤ n + 1)
    (hfar : i + 2 ≤ j ∨ j + 2 ≤ i) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i hin) = 0 := by
  rcases hfar with hfar | hfar
  · exact oldExceptionalPairing_oldStrictClass_of_lt n hproj j h i hfar
  · exact oldExceptionalPairing_oldStrictClass_of_ge n hproj j h i hfar hin

end Rows

end KltDP.Examples.FrobeniusOldExceptionalLaterRows

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
  FrobeniusOldExceptionalLaterStages FrobeniusStrictTransformPairing
  FrobeniusOldExceptionalLaterRows

/-- **The far rows of the older exceptional curves**: on `stageSurface (n+1) hproj`, `C_j · E_i^tot = 0`
for `i ≥ j + 2` and `C_j · C_i = 0` for all non-adjacent `i`. -/
theorem f29_old_exceptional_far_rows (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) :
    (∀ i : Fin (n + 1), j + 2 ≤ i.val →
      oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0) ∧
    (∀ (i : ℕ) (hin : i + 2 ≤ n + 1), (i + 2 ≤ j ∨ j + 2 ≤ i) →
      oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i hin) = 0) :=
  ⟨fun i hi => oldExceptionalPairing_totalExceptional_of_ge n hproj j h i hi,
    fun i hin hfar => oldExceptionalPairing_oldStrictClass_of_far n hproj j h i hin hfar⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_old_exceptional_far_rows_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) : True := by
  have _ := f29_old_exceptional_far_rows.{u} k n hproj j h
  trivial

end KltDP.Examples
