import KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue
import KltDP.Examples.FrobeniusStrictTransformClassesTower
import KltDP.Examples.FrobeniusTowerPicardRelation
import KltDP.Geometry.NumericalEquivalence
import KltDP.Geometry.RationalTreePicardMultidegree
import KltDP.Examples.FrobeniusGraphPicardClassIntegral

/-!
# The newest exceptional curve paired with the Picard classes of the tower (BRIEF13, item 2)

On stage `n+1` of the origin contact tower let `E_n = exceptionalPrimeCurve n hproj` be the newest
exceptional curve (a prime curve of `stageSurface (n+1) hproj`). Lane D's F02 homomorphism
`picardRestrictionDegreeHom E_n : Additive Pic →+ ℤ` (the degree of a Picard class restricted to `E_n`)
is the pairing `E_n · (−)` on classes; it agrees with lane D's `intersectionNumber` on Cartier classes.

* `exceptionalPairing_pullback`: **`E_n · π^*q = 0`** for every Picard class `q` of stage `n`
  (BRIEF8 `restrictionDegree_pullback_stepProjection`, lane D `toPic_surjective`);
* `cartierPicardHom_exceptionalCartier`: the Cartier class of `D_{E_n}` is the accepted
  `stepExceptionalPicardClass n` (BRIEF8 `negativeCartierKernelIso : O(−D_E) ≅ I(E)`, and
  `stepExceptionalIdealLine n` is that ideal line);
* `exceptionalPairing_self`: **`E_n · E_n = −1`** on the class `stepExceptionalPicardClass n`
  (BRIEF9 `f09_exceptional_self_intersection`);
* `exceptionalPairing_totalExceptional`: **`E_n · E_j^{tot} = −δ_{j, last}`** for the accepted total
  transform classes `totalExceptionalClass (n+1) j`, `j : Fin (n+1)`; hence for all `i ≤ j` the
  manuscript's `E_i · E_j = −δ_{ij}` in the form "newest curve against total class";
* the fibre classes: `E_n · a = E_n · b = 0` (`firstFiberTotalClass`, `secondFiberTotalClass`);
* **the `P`-row of the manuscript table** on stage `n+1` (`P = E_n`): `P · B = 1`
  (`strictCurvePicardClass`, any exponent), `P · C_j = [j+1 = n]` (`oldExceptionalStrictClass`),
  `P · π^*F_0 = 0` and `P · F̃ = 1` (lane F's fibre classes, under `FiberKernelInvertible 0`),
  `P · P = −1`.

Everything carries `hproj : IsProjectiveOverField ((projectiveProductInitial).stage (n+1)).structureMap`
and `[IsAlgClosed k]`; the specialisation to stage `1` without `hproj` is in
`FrobeniusStageExceptionalTable`. The symmetric pairing of two *older* total classes on the top stage
(lane D's `picardEulerPairing`) is not treated: it needs `π^*D₁ · π^*D₂ = D₁ · D₂` in class form
(BRIEF13 item 1), recorded as open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStageExceptionalPairing

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.InvertibleSheaf
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageExceptionalPullback
open FrobeniusStageExceptionalSelfIntersection FrobeniusStageExceptionalSelfIntersectionValue
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformClassesTower FrobeniusGraphPicardClassTotalTransform
open FrobeniusOldExceptionalLaterStages FrobeniusTowerPicardRelation FrobeniusFiberPicard

variable {k : Type u} [Field k]

/-- The initial product is integral (accepted), so every stage is (accepted `instStageIsIntegral`). -/
local instance initial_isIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **The pairing `E_n · (−)`** of the newest exceptional curve with the Picard classes of stage
`n+1` (lane D's restriction-degree homomorphism). -/
abbrev exceptionalPairing : Additive (projectiveContactStage (k := k) (n + 1)).Pic →+ ℤ :=
  (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (exceptionalPrimeCurve n hproj)

/-! ## Pull-backs from the previous stage -/

/-- **`E_n · π^*q = 0`** for every Picard class `q` of stage `n`. -/
theorem exceptionalPairing_pullback (q : Additive (projectiveContactStage (k := k) n).Pic) :
    exceptionalPairing n hproj
      ((schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive q) =
      0 := by
  obtain ⟨L, hL⟩ := RationalTreePicard.toPic_surjective q.toMul
  change (exceptionalPrimeCurve n hproj).picardRestrictionDegree
    (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n) q.toMul) = 0
  rw [← hL, schemePicardPullbackHom_toPic, picardRestrictionDegree_toPic]
  exact restrictionDegree_pullback_stepProjection n hproj L

theorem exceptionalPairing_firstFiber :
    exceptionalPairing n hproj (firstFiberTotalClass (n + 1)) = 0 := by
  rw [firstFiberTotalClass_succ]
  exact exceptionalPairing_pullback n hproj _

theorem exceptionalPairing_secondFiber :
    exceptionalPairing n hproj (secondFiberTotalClass (n + 1)) = 0 := by
  rw [secondFiberTotalClass_succ]
  exact exceptionalPairing_pullback n hproj _

/-! ## The class of the exceptional Cartier divisor -/

/-- `O(−D_E)` and the exceptional ideal line have the same Picard class. -/
theorem toPic_neg_exceptionalCartier :
    (cartierDivisorInvertibleSheaf (projectiveContactStage (k := k) (n + 1))
        (-(exceptionalCartier n hproj))).toPic =
      (stepExceptionalIdealLine (k := k) n).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (n + 1))
  apply Units.ext
  change ((cartierDivisorInvertibleSheaf (projectiveContactStage (k := k) (n + 1))
      (-(exceptionalCartier n hproj))).toPic :
        Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) =
    ((stepExceptionalIdealLine (k := k) n).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨negativeCartierKernelIso n hproj⟩

/-- **The Cartier class of `D_{E_n}` is the accepted exceptional Picard class.** -/
theorem cartierPicardHom_exceptionalCartier :
    cartierPicardHom (projectiveContactStage (k := k) (n + 1)) (exceptionalCartier n hproj) =
      stepExceptionalPicardClass n := by
  have h2 : cartierPicardHom (projectiveContactStage (k := k) (n + 1)) (-(exceptionalCartier n hproj)) =
      Additive.ofMul (stepExceptionalIdealLine (k := k) n).toPic := by
    change Additive.ofMul (cartierPicardClass (projectiveContactStage (k := k) (n + 1))
      (-(exceptionalCartier n hproj))) = _
    rw [cartierPicardClass]
    exact congrArg Additive.ofMul (toPic_neg_exceptionalCartier n hproj)
  rw [stepExceptionalPicardClass, ← h2, map_neg, neg_neg]

/-- **`E_n · E_n = −1`** on the exceptional Picard class. -/
theorem exceptionalPairing_self :
    exceptionalPairing n hproj (stepExceptionalPicardClass n) = -1 := by
  rw [← cartierPicardHom_exceptionalCartier n hproj]
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (exceptionalPrimeCurve n hproj)
    (cartierPicardHom (stageSurface (n + 1) hproj).toScheme (exceptionalCartier n hproj)) = -1
  rw [picardRestrictionDegreeHom_cartierPicardHom]
  exact f09_exceptional_self_intersection k n hproj

/-! ## The total transform classes -/

theorem castSucc_ne_last (i : Fin n) : Fin.castSucc i ≠ Fin.last n := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_castSucc, Fin.val_last] at this
  exact absurd this (Nat.ne_of_lt i.isLt)

/-- **`E_n · E_j^{tot} = −δ_{j, last}`**: the newest curve against every total exceptional class. -/
theorem exceptionalPairing_totalExceptional (j : Fin (n + 1)) :
    exceptionalPairing n hproj (totalExceptionalClass (n + 1) j) =
      if j = Fin.last n then -1 else 0 := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [totalExceptionalClass_castSucc, exceptionalPairing_pullback, if_neg (castSucc_ne_last n i)]
  · rw [totalExceptionalClass_last, exceptionalPairing_self, if_pos rfl]

theorem exceptionalPairing_totalExceptional_castSucc (i : Fin n) :
    exceptionalPairing n hproj (totalExceptionalClass (n + 1) (Fin.castSucc i)) = 0 := by
  rw [exceptionalPairing_totalExceptional, if_neg (castSucc_ne_last n i)]

theorem exceptionalPairing_totalExceptional_last :
    exceptionalPairing n hproj (totalExceptionalClass (n + 1) (Fin.last n)) = -1 := by
  rw [exceptionalPairing_totalExceptional, if_pos rfl]

theorem exceptionalPairing_sum_totalExceptional :
    ∑ j : Fin (n + 1), exceptionalPairing n hproj (totalExceptionalClass (n + 1) j) = -1 := by
  rw [Fin.sum_univ_castSucc, exceptionalPairing_totalExceptional_last]
  simp only [exceptionalPairing_totalExceptional_castSucc, Finset.sum_const_zero, zero_add]

/-! ## The `P`-row of the manuscript table on stage `n+1` -/

/-- **`P · B = 1`**: the newest exceptional curve meets the strict transform of the graph once
(class form, any residual exponent `m`). -/
theorem exceptionalPairing_strictCurve (m : ℕ) :
    exceptionalPairing n hproj (strictCurvePicardClass (n + 1) m) = 1 := by
  rw [strictCurvePicardClass_tower, map_sub, map_add, map_nsmul, map_sum,
    exceptionalPairing_firstFiber, exceptionalPairing_secondFiber,
    exceptionalPairing_sum_totalExceptional]
  simp

/-- **`P · C_j = [j + 1 = n]`**: the newest exceptional curve meets only the previous one. -/
theorem exceptionalPairing_oldExceptional (j : Fin n) :
    exceptionalPairing n hproj (oldExceptionalStrictClass (n + 1) j.val (by omega)) =
      if j.succ = Fin.last n then 1 else 0 := by
  rw [oldExceptionalStrictClass_eq_castSucc, map_sub, exceptionalPairing_totalExceptional_castSucc,
    exceptionalPairing_totalExceptional, zero_sub]
  split_ifs <;> simp

/-- **`P · π^*F_0 = 0`**: the total transform of the stage-`0` fibre. -/
theorem exceptionalPairing_fiberTotal (h0 : FiberKernelInvertible (k := k) 0) :
    exceptionalPairing n hproj (fiberTotalClass h0 (n + 1)) = 0 := by
  rw [fiberTotalClass_succ]
  exact exceptionalPairing_pullback n hproj _

/-- **`P · F̃ = 1`**: the newest exceptional curve meets the strict fibre once (lane F's tower
relation `π^*F_0 = F̃ + Σ (j+1) C_j + (n+1) P`). -/
theorem exceptionalPairing_fiberStrict (h0 : FiberKernelInvertible (k := k) 0) :
    exceptionalPairing n hproj (fiberPicardClass h0 (n + 1)) = 1 := by
  have h := congrArg (exceptionalPairing n hproj) (fiberTotal_eq_strict_add_exceptional h0 n)
  rw [exceptionalPairing_fiberTotal, map_add, map_add, map_sum, map_nsmul,
    exceptionalPairing_totalExceptional_last] at h
  simp only [map_nsmul, exceptionalPairing_oldExceptional] at h
  rcases n with _ | n
  · simp at h
    linarith
  · rw [Fin.sum_univ_castSucc] at h
    have hlast : ∀ i : Fin n, (Fin.castSucc i).succ ≠ Fin.last (n + 1) := by
      intro i hi
      have := congrArg Fin.val hi
      simp only [Fin.val_succ, Fin.coe_castSucc, Fin.val_last] at this
      exact absurd (Nat.succ_injective this) (Nat.ne_of_lt i.isLt)
    simp only [hlast, if_false, smul_zero, Finset.sum_const_zero, zero_add, Fin.succ_last, if_true,
      Fin.val_last, nsmul_eq_mul, mul_one, mul_neg] at h
    push_cast at h
    linarith

end KltDP.Examples.FrobeniusStageExceptionalPairing
