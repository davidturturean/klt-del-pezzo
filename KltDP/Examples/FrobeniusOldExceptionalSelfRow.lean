import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusStageExceptionalPairing
import KltDP.Examples.FrobeniusStageExceptionalPullback
import KltDP.Examples.FrobeniusStageOneProjective

/-!
# The row `C_j · E_j^tot = −1` (BRIEF14, item 3)

The older exceptional curve `C_j ⊆ stage (n+1)` blown down to stage `j+1` is the accepted
isomorphism `strictToFiber` onto the exceptional fibre `E_j` of stage `j+1`
(`finalOldMap_comp_between_succ`). The total class `E_j^tot` of stage `n+1` is the pullback of
the exceptional class of stage `j+1`, so `C_j · E_j^tot` is the degree on `C_j` of the pullback of
`O(E_j)|_{E_j}` along `C_j ≅ E_j`; by the generic degree transport (`picardDegree_pullback_iso`) it
equals `E_j · E_j = −1` (BRIEF13's `exceptionalPairing_self`, which needs the projectivity of stage
`j+1`, here the hypothesis `hprojj`). Also `between_structureMap`: the structure morphisms of the
stages are compatible with the accepted projections `between`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalSelfRow

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.PrimeCurveInclusionLift
open KltDP.Geometry.PrimeCurveDegreeTransport
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStageSurface FrobeniusExceptionalFinalConfiguration
open FrobeniusGlobalExceptionalSuccessor FrobeniusPreviousStrictBlowdown
open FrobeniusStrictTransformClassesTower FrobeniusStrictTransformPrimeCurves
open FrobeniusStrictTransformPairing FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformProductKernel FrobeniusGlobalExceptionalNormal
open FrobeniusStageExceptionalPairing FrobeniusStageExceptionalPullback

variable {k : Type u} [Field k]

section Structure

variable (A : PlaneChartedScheme k)

/-- The structure morphisms of the stages are compatible with the projections `between`. -/
theorem between_structureMap {j N : ℕ} (h : j ≤ N) :
    between A h ≫ (A.stage j).structureMap = (A.stage N).structureMap := by
  induction N, h using Nat.le_induction with
  | base => rw [between_refl, Category.id_comp]
  | succ N hjN ih =>
    rw [between_succ A hjN, Category.assoc, ih]
    rfl

/-- **`C_j ⊆ stage N` blown down to stage `j+1` is `strictToFiber` followed by the exceptional
fibre inclusion.** -/
theorem finalOldMap_comp_between_succ (N j : ℕ) (h : j + 2 ≤ N) :
    finalOldMap A N j h ≫ between A (show j + 1 ≤ N by omega) =
      strictToFiber (A.stage j) ≫ previousFiberι (A.stage j) := by
  have h1 : between A (show j + 1 ≤ N by omega) =
      between A h ≫ between A (show j + 1 ≤ j + 2 by omega) :=
    (between_comp A (show j + 1 ≤ j + 2 by omega) h).symm
  have e1 : between A (show j + 1 ≤ j + 2 by omega) = A.stepProjection (j + 1) :=
    between_step A (j + 1)
  rw [h1, ← Category.assoc, finalOldMap_projection, e1]
  exact (strictToFiber_ι (A.stage j)).symm

end Structure

section Row

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
  (j : ℕ) (h : j + 2 ≤ n + 1)
  (hprojj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap)

/-- The base of the exceptional fibre `E_j` of stage `j+1`. -/
abbrev exceptionalBase :
    globalExceptionalScheme ((projectiveProductInitial (k := k)).stage j) ⟶
      Spec (CommRingCat.of k) :=
  stepExceptionalInclusion (k := k) j ≫
    ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap

/-- **`C_j ≅ E_j`**: the prime-curve scheme of `C_j` maps isomorphically onto the exceptional
fibre of stage `j+1`. -/
abbrev oldToExceptional :
    (oldExceptionalPrimeCurve n hproj j h).toScheme ⟶
      globalExceptionalScheme ((projectiveProductInitial (k := k)).stage j) :=
  inv (lift (oldExceptionalPrimeCurve n hproj j h)
      (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
    strictToFiber ((projectiveProductInitial (k := k)).stage j)

instance oldToExceptional_isIso : IsIso (oldToExceptional n hproj j h) := by
  unfold oldToExceptional
  infer_instance

/-- The isomorphism `C_j ≅ E_j` is over `k`. -/
theorem oldToExceptional_base :
    oldToExceptional n hproj j h ≫ exceptionalBase j = (oldExceptionalPrimeCurve n hproj j h).toSpec := by
  change _ = (oldExceptionalPrimeCurve n hproj j h).inclusion ≫
    ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap
  rw [inclusion_eq_inv_lift (oldExceptionalPrimeCurve n hproj j h)
      (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl,
    ← between_structureMap (projectiveProductInitial (k := k)) (show j + 1 ≤ n + 1 by omega)]
  simp only [Category.assoc]
  rw [← Category.assoc (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h),
    finalOldMap_comp_between_succ, Category.assoc]

/-- The prime-curve scheme of `E_j` maps isomorphically onto the exceptional fibre, over `k`. -/
theorem exceptionalLift_base :
    inv (exceptionalLift j hprojj) ≫ exceptionalBase j = (exceptionalPrimeCurve j hprojj).toSpec := by
  change _ = (exceptionalPrimeCurve j hprojj).inclusion ≫
    ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap
  rw [inclusion_eq_inv_exceptionalLift j hprojj, Category.assoc]

include hprojj in
/-- **`C_j · E_j^tot = −1`** (given the projectivity of stage `j+1`): by degree transport along
`C_j ≅ E_j` from `E_j · E_j = −1`. -/
theorem oldExceptionalPairing_totalExceptional_self :
    oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) ⟨j, by omega⟩) = -1 := by
  rw [← exceptionalPairing_self j hprojj]
  change (oldExceptionalPrimeCurve n hproj j h).picardRestrictionDegree
      (schemePicardPullbackHom
        (between (projectiveProductInitial (k := k)) (show j + 1 ≤ n + 1 by omega))
        (stepExceptionalPicardClass j).toMul) =
    (exceptionalPrimeCurve j hprojj).picardRestrictionDegree (stepExceptionalPicardClass j).toMul
  erw [PrimeCurve.picardRestrictionDegree_pullback]
  unfold PrimeCurve.picardRestrictionDegree
  rw [inclusion_eq_inv_lift (oldExceptionalPrimeCurve n hproj j h)
      (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl,
    Category.assoc, finalOldMap_comp_between_succ, ← Category.assoc,
    inclusion_eq_inv_exceptionalLift j hprojj,
    schemePicardPullbackHom_comp (previousFiberι ((projectiveProductInitial (k := k)).stage j))
      (inv (lift (oldExceptionalPrimeCurve n hproj j h)
        (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h) rfl) ≫
        strictToFiber ((projectiveProductInitial (k := k)).stage j)),
    schemePicardPullbackHom_comp (stepExceptionalInclusion (k := k) j)
      (inv (exceptionalLift j hprojj))]
  change (oldExceptionalPrimeCurve n hproj j h).picardDegree
      (schemePicardPullbackHom (oldToExceptional n hproj j h)
        (schemePicardPullbackHom (stepExceptionalInclusion (k := k) j)
          (stepExceptionalPicardClass j).toMul)) =
    (exceptionalPrimeCurve j hprojj).picardDegree
      (schemePicardPullbackHom (inv (exceptionalLift j hprojj))
        (schemePicardPullbackHom (stepExceptionalInclusion (k := k) j)
          (stepExceptionalPicardClass j).toMul))
  rw [picardDegree_pullback_iso _ (oldToExceptional n hproj j h) (exceptionalBase j)
      (oldToExceptional_base n hproj j h),
    picardDegree_pullback_iso _ (inv (exceptionalLift j hprojj)) (exceptionalBase j)
      (exceptionalLift_base j hprojj)]

/-- **`C_0 · E_0^tot = −1` unconditionally**: stage `1` is projective (BRIEF11's
`stage_one_projective`), so no extra hypothesis is needed for the first older curve. -/
theorem oldExceptionalPairing_totalExceptional_zero (h : 0 + 2 ≤ n + 1) :
    oldExceptionalPairing n hproj 0 h (totalExceptionalClass (n + 1) ⟨0, Nat.zero_lt_succ n⟩) =
      -1 :=
  oldExceptionalPairing_totalExceptional_self n hproj 0 h
    (FrobeniusStageOneProjective.stage_one_projective (k := k))

end Row

end KltDP.Examples.FrobeniusOldExceptionalSelfRow

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
  FrobeniusStrictTransformPairing FrobeniusOldExceptionalSelfRow

/-- **`C_j · E_j^tot = −1`** on `stageSurface (n+1) hproj`, given the projectivity of stage
`j+1`. -/
theorem f29_old_exceptional_self_row (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap) :
    oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) ⟨j, by omega⟩) = -1 :=
  oldExceptionalPairing_totalExceptional_self n hproj j h hprojj

/-- **`C_0 · E_0^tot = −1`** on `stageSurface (n+1) hproj`, unconditionally. -/
theorem f29_old_exceptional_self_row_zero (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h : 0 + 2 ≤ n + 1) :
    oldExceptionalPairing n hproj 0 h (totalExceptionalClass (n + 1) ⟨0, Nat.zero_lt_succ n⟩) =
      -1 :=
  oldExceptionalPairing_totalExceptional_zero n hproj h

/-- The bundle has exactly one universe parameter. -/
theorem f29_old_exceptional_self_row_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1)).structureMap) : True := by
  have _ := f29_old_exceptional_self_row.{u} k n hproj j h hprojj
  trivial

end KltDP.Examples
