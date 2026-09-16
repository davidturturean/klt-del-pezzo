import KltDP.Geometry.PrimeCurveTransversalPoint
import KltDP.Examples.FrobeniusOldExceptionalLaterRows
import KltDP.Examples.FrobeniusStrictTransformFiberRowsValues
import KltDP.Examples.FrobeniusExceptionalChainTransversal

/-!
# The adjacent rows `C_j · C_{j+1} = 1`, `C_j · E_{j+1}^tot = 1`, `C_j · C_j = −2` (BRIEF19, item 2)

On stage `n+1` of the origin contact tower (`[IsAlgClosed k]`, `hproj` the projectivity of stage
`n+1`), `C_j = oldExceptionalPrimeCurve n hproj j h` (`j + 2 ≤ n + 1`) is the strict transform of the
`j`-th exceptional curve and `P = E_n = exceptionalPrimeCurve n hproj` the newest one; the pairings are
lane D's restriction degrees `C · (−)` on `Additive Pic`.

* `cartierPicardHom_oldCartier`: the Cartier class of `D_{C_j} = primeCurveCartier C_j` is the accepted
  `oldExceptionalStrictClass (n+1) j` (generic `cartierPicardHom_primeCurveCartier_of_kernel` for the
  closed immersion `finalOldMap`, whose kernel ideal line is `oldFinalKernelLine`).
* `oldExceptionalPairing_oldStrictClass_succ`: **`C_j · [C_{j+1}] = 1`** for `j + 3 ≤ n + 1`, given the
  projectivity of stage `j + 2`: adjacent curves meet in at most one point (lane F's accepted
  `chainSinglePoints`, field `old`), so `C_j · [D_{C_{j+1}}] = C_{j+1} · [D_{C_j}]` (F03 symmetry,
  `picardRestrictionDegreeHom_primeCurveCartier_symm`), and the right side is the accepted row
  `C_{j+1} · [C_j] = 1` (`oldExceptionalPairing_oldStrictClass_pred`).
* `oldExceptionalPairing_stepExceptional` (stage `m + 2`), `…_stepExceptional_pred` (stage `n + 1`,
  `1 ≤ n`): **`C_{n−1} · [P] = 1`** with no further hypothesis: `chainSinglePoints`, field `newest`,
  symmetry, `[P] = [D_P]` (`cartierPicardHom_exceptionalCartier`) and the accepted `P`-row
  `P · [C_{n−1}] = 1` (`exceptionalPairing_oldExceptional`).
* `oldExceptionalPairing_totalExceptional_succ_of_lt`, `…_succ_last`, `…_succ`:
  **`C_j · E_{j+1}^tot = 1`**, from `E_{j+1}^tot = [C_{j+1}] + E_{j+2}^tot` (accepted
  `oldExceptionalStrictClass_eq'`), the zero row `C_j · E_{j+2}^tot = 0`
  (`oldExceptionalPairing_totalExceptional_of_ge`) and the row above; for `j + 1 = n` from
  `E_n^tot = [P]` (`totalExceptionalClass_last`).
* `oldExceptionalPairing_oldStrictClass_self_eq`: **`C_j · [C_j] = −2`** (the accepted conditional
  `oldExceptionalPairing_oldStrictClass_self` with the row above).
* Bundles `KltDP.Examples.f29_intersection_table_adjacent` (the accepted
  `f29_intersection_table_extended` together with the new rows, under `hstages`: projectivity of the
  stages `2, …, n`; stage `1` is BRIEF11's `stage_one_projective`) and
  `f29_intersection_table_adjacent_stage_two` (stage `2`, only `hproj`).

The rows go through the F03 symmetry, not through the local length of `PrimeCurveTransversalPoint`:
the passage from lane F's `TransversalCrossing` to the uniformizer hypothesis there is not proved; with
it, `C_j · [C_{j+1}] = 1` would not need the projectivity of stage `j + 2`. Not treated: `B · B`,
`F̃ · F̃`, and the three `P¹` exponents behind `B · a`, `B · b`, `F̃ · a`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalAdjacentRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.PrimeCurveTransversalPoint
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusExceptionalFinalConfiguration
open FrobeniusStrictTransformClassesTower FrobeniusStrictTransformPrimeCurves
open FrobeniusStrictTransformPairing FrobeniusStrictTransformPicardStep
open FrobeniusOldExceptionalLaterStages FrobeniusOldExceptionalChainRows FrobeniusOldExceptionalLaterRows
open FrobeniusStageExceptionalSelfIntersection FrobeniusStageExceptionalPairing

variable {k : Type u} [Field k]

/-- The initial product is integral (accepted), so every stage is (accepted `instStageIsIntegral`). -/
local instance adjacentRows_initial_isIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Projectivity of the stages `1, …, n` from that of the stages `2, …, n` (stage `1`: BRIEF11). -/
theorem stage_projective_of_le (n : ℕ)
    (hstages : ∀ i : ℕ, 2 ≤ i → i ≤ n →
      IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap)
    (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ n) :
    IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap := by
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · obtain rfl : i = 1 := by omega
    exact FrobeniusStageOneProjective.stage_one_projective
  · exact hstages i hge hi

variable [IsAlgClosed k]

/-! ## The Cartier class of `C_j` -/

/-- The Cartier divisor `D_{C_j}` of the older exceptional curve `C_j` on stage `n+1` (lane D's
`primeCurveCartier`). -/
abbrev oldCartier (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) : CartierDivisor (stageSurface (n + 1) hproj).toScheme :=
  (stageSurface (n + 1) hproj).primeCurveCartier (stageRegular n hproj)
    (oldExceptionalPrimeCurve n hproj j h)

/-- **The Cartier class of `D_{C_j}` is the accepted class `oldExceptionalStrictClass (n+1) j`.** -/
theorem cartierPicardHom_oldCartier (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1) :
    cartierPicardHom (stageSurface (n + 1) hproj).toScheme (oldCartier n hproj j h) =
      oldExceptionalStrictClass (n + 1) j h :=
  cartierPicardHom_primeCurveCartier_of_kernel (stageRegular n hproj)
    (oldExceptionalPrimeCurve n hproj j h) (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j h)
    rfl (oldFinalKernelLine (n + 1) j h) rfl

/-! ## Adjacent curves -/

set_option maxHeartbeats 1000000 in
/-- The last older curve `C_m` and the newest exceptional curve `P` of stage `m + 2` meet in at most
one point (lane F's accepted `chainSinglePoints`, field `newest`). -/
theorem oldExceptional_inter_exceptional_subsingleton (m : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (m + 1 + 1)).structureMap) :
    ((oldExceptionalPrimeCurve (m + 1) hproj m (by omega) :
      Set (stageSurface (m + 1 + 1) hproj).toScheme) ∩
        exceptionalPrimeCurve (m + 1) hproj).Subsingleton := by
  rw [coe_oldExceptionalPrimeCurve, coe_exceptionalPrimeCurve]
  exact (FrobeniusExceptionalChainTransversal.chainSinglePoints
    (projectiveProductInitial (k := k)) (m + 1)).newest m rfl

/-- `C_m · [P]` is `C_m · [D_P]` (`cartierPicardHom_exceptionalCartier`). -/
theorem oldExceptionalPairing_stepExceptional_eq_cartier (m : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (m + 1 + 1)).structureMap) :
    oldExceptionalPairing (m + 1) hproj m (by omega) (stepExceptionalPicardClass (m + 1)) =
      (stageSurface (m + 1 + 1) hproj).picardRestrictionDegreeHom
        (oldExceptionalPrimeCurve (m + 1) hproj m (by omega))
        (cartierPicardHom (stageSurface (m + 1 + 1) hproj).toScheme (exceptionalCartier (m + 1) hproj)) :=
  congrArg (oldExceptionalPairing (m + 1) hproj m (by omega))
    (cartierPicardHom_exceptionalCartier (m + 1) hproj).symm

/-- `P · [D_{C_m}] = 1`: the accepted `P`-row `P · [C_m] = 1` with `[D_{C_m}] = [C_m]`. -/
theorem exceptionalPairing_oldCartier_last (m : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (m + 1 + 1)).structureMap) :
    (stageSurface (m + 1 + 1) hproj).picardRestrictionDegreeHom (exceptionalPrimeCurve (m + 1) hproj)
      (cartierPicardHom (stageSurface (m + 1 + 1) hproj).toScheme
        (oldCartier (m + 1) hproj m (by omega))) = 1 := by
  have h4 := exceptionalPairing_oldExceptional (m + 1) hproj (Fin.last m)
  have h5 : (if (Fin.last m).succ = Fin.last (m + 1) then (1 : ℤ) else 0) = 1 :=
    if_pos (Fin.succ_last m)
  exact (congrArg (exceptionalPairing (m + 1) hproj)
    (cartierPicardHom_oldCartier (m + 1) hproj m (by omega))).trans (h4.trans h5)

/-- **`C_m · [P] = 1`** on stage `m + 2`: the last older curve meets the newest exceptional curve
once. -/
theorem oldExceptionalPairing_stepExceptional (m : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (m + 1 + 1)).structureMap) :
    oldExceptionalPairing (m + 1) hproj m (by omega) (stepExceptionalPicardClass (m + 1)) = 1 :=
  (oldExceptionalPairing_stepExceptional_eq_cartier m hproj).trans
    ((picardRestrictionDegreeHom_primeCurveCartier_symm (stageRegular (m + 1) hproj)
      (oldExceptionalPrimeCurve (m + 1) hproj m (by omega)) (exceptionalPrimeCurve (m + 1) hproj)
        (oldExceptional_inter_exceptional_subsingleton m hproj)).trans
      (exceptionalPairing_oldCartier_last m hproj))

/-- **`C_{n−1} · [P] = 1`** on stage `n + 1`, `1 ≤ n`. -/
theorem oldExceptionalPairing_stepExceptional_pred (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (hn : 1 ≤ n) :
    oldExceptionalPairing n hproj (n - 1) (by omega) (stepExceptionalPicardClass n) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact oldExceptionalPairing_stepExceptional m hproj

/-- **`C_j · [C_{j+1}] = 1`** for two older adjacent curves (`j + 3 ≤ n + 1`), given the projectivity
of stage `j + 2`. -/
theorem oldExceptionalPairing_oldStrictClass_succ (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 3 ≤ n + 1)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1 + 1)).structureMap) :
    oldExceptionalPairing n hproj j (by omega)
      (oldExceptionalStrictClass (n + 1) (j + 1) (by omega)) = 1 := by
  have hs : ((oldExceptionalPrimeCurve n hproj j (by omega) :
      Set (stageSurface (n + 1) hproj).toScheme) ∩
        oldExceptionalPrimeCurve n hproj (j + 1) (by omega)).Subsingleton :=
    (FrobeniusExceptionalChainTransversal.chainSinglePoints
      (projectiveProductInitial (k := k)) n).old j (by omega)
  exact (congrArg (oldExceptionalPairing n hproj j (by omega))
      (cartierPicardHom_oldCartier n hproj (j + 1) (by omega)).symm).trans
    ((picardRestrictionDegreeHom_primeCurveCartier_symm (stageRegular n hproj)
      (oldExceptionalPrimeCurve n hproj j (by omega))
        (oldExceptionalPrimeCurve n hproj (j + 1) (by omega)) hs).trans
    ((congrArg (oldExceptionalPairing n hproj (j + 1) (by omega))
      (cartierPicardHom_oldCartier n hproj j (by omega))).trans
    (oldExceptionalPairing_oldStrictClass_pred n hproj (j + 1) (by omega) (by omega) hprojj)))

/-! ## The rows `C_j · E_{j+1}^tot = 1` and `C_j · C_j = −2` -/

/-- **`C_j · E_{j+1}^tot = 1`** for `j + 3 ≤ n + 1`, given the projectivity of stage `j + 2`. -/
theorem oldExceptionalPairing_totalExceptional_succ_of_lt (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 3 ≤ n + 1)
    (hprojj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (j + 1 + 1)).structureMap) :
    oldExceptionalPairing n hproj j (by omega) (totalExceptionalClass (n + 1) ⟨j + 1, by omega⟩) = 1 := by
  have hrel := oldExceptionalStrictClass_eq' (k := k) (n + 1) (j + 1) (by omega)
  rw [eq_sub_iff_add_eq] at hrel
  rw [← hrel, map_add, oldExceptionalPairing_oldStrictClass_succ n hproj j h hprojj,
    oldExceptionalPairing_totalExceptional_of_ge n hproj j (by omega) ⟨j + 1 + 1, by omega⟩
      (show j + 2 ≤ j + 1 + 1 by omega), add_zero]

/-- **`C_m · E_{m+1}^tot = 1`** on stage `m + 2` (the newest total class is `[P]`). -/
theorem oldExceptionalPairing_totalExceptional_succ_last (m : ℕ)
    (hproj : IsProjectiveOverField
      ((projectiveProductInitial (k := k)).stage (m + 1 + 1)).structureMap) :
    oldExceptionalPairing (m + 1) hproj m (by omega)
      (totalExceptionalClass (m + 1 + 1) ⟨m + 1, by omega⟩) = 1 :=
  (congrArg (oldExceptionalPairing (m + 1) hproj m (by omega))
    (totalExceptionalClass_last (k := k) (m + 1))).trans (oldExceptionalPairing_stepExceptional m hproj)

/-- **`C_j · E_{j+1}^tot = 1`** for every older curve `C_j` on stage `n + 1`, given the projectivity
of the stages `2, …, n`. -/
theorem oldExceptionalPairing_totalExceptional_succ (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1)
    (hstages : ∀ i : ℕ, 2 ≤ i → i ≤ n →
      IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap) :
    oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) ⟨j + 1, by omega⟩) = 1 := by
  rcases Nat.lt_or_ge (j + 1) n with hlt | hge
  · exact oldExceptionalPairing_totalExceptional_succ_of_lt n hproj j (by omega)
      (stage_projective_of_le n hstages (j + 1 + 1) (by omega) (by omega))
  · obtain rfl : n = j + 1 := by omega
    exact oldExceptionalPairing_totalExceptional_succ_last j hproj

/-- **`C_j · [C_j] = −2`** for every older curve `C_j` on stage `n + 1`, given the projectivity of the
stages `2, …, n`. -/
theorem oldExceptionalPairing_oldStrictClass_self_eq (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (j : ℕ) (h : j + 2 ≤ n + 1)
    (hstages : ∀ i : ℕ, 2 ≤ i → i ≤ n →
      IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap) :
    oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) j (by omega)) = -2 :=
  oldExceptionalPairing_oldStrictClass_self n hproj j h
    (stage_projective_of_le n hstages (j + 1) (by omega) (by omega))
    (oldExceptionalPairing_totalExceptional_succ n hproj j h hstages)

end KltDP.Examples.FrobeniusOldExceptionalAdjacentRows

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformClassesTower
  FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformPairing
  FrobeniusOldExceptionalLaterStages FrobeniusOldExceptionalChainRows
  FrobeniusStrictTransformFiberRowsValues FrobeniusStageExceptionalPairing
  FrobeniusStrictTransformPicardStep FrobeniusFiberPicard FrobeniusOldExceptionalAdjacentRows

/-- **The table with the adjacent rows** on stage `n + 1`: the accepted extended table
(`f29_intersection_table_extended`), and for the older exceptional curves `C_j`:
`C_j · E_{j+1}^tot = 1`, `C_j · [C_j] = −2`, `C_j · [C_{j+1}] = 1` (`j + 3 ≤ n + 1`), and
`C_{n−1} · [P] = 1`; the rows of `C_j` use the projectivity of the stages `2, …, n` (`hstages`). -/
theorem f29_intersection_table_adjacent (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h0 : FiberKernelInvertible (k := k) 0)
    (hstages : ∀ i : ℕ, 2 ≤ i → i ≤ n →
      IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap) :
    (((∀ j : Fin (n + 1), exceptionalPairing n hproj (totalExceptionalClass (n + 1) j) =
        if j = Fin.last n then -1 else 0) ∧
      exceptionalPairing n hproj (stepExceptionalPicardClass n) = -1 ∧
      exceptionalPairing n hproj (firstFiberTotalClass (n + 1)) = 0 ∧
      exceptionalPairing n hproj (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ m : ℕ, exceptionalPairing n hproj (strictCurvePicardClass (n + 1) m) = 1) ∧
      (∀ j : Fin n, exceptionalPairing n hproj (oldExceptionalStrictClass (n + 1) j.val (by omega)) =
        if j.succ = Fin.last n then 1 else 0) ∧
      exceptionalPairing n hproj (fiberTotalClass h0 (n + 1)) = 0 ∧
      exceptionalPairing n hproj (fiberPicardClass h0 (n + 1)) = 1) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1),
      oldExceptionalPairing n hproj j h (firstFiberTotalClass (n + 1)) = 0 ∧
      oldExceptionalPairing n hproj j h (secondFiberTotalClass (n + 1)) = 0 ∧
      (∀ i : Fin (n + 1), i.val < j →
        oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0) ∧
      (∀ (i : ℕ) (hi : i + 2 ≤ j),
        oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) i (by omega)) = 0)) ∧
    fiberStrictPairing n hproj (secondFiberTotalClass (n + 1)) = 0) ∧
    (∀ (j : ℕ) (h : j + 2 ≤ n + 1),
      oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) ⟨j + 1, by omega⟩) = 1 ∧
      oldExceptionalPairing n hproj j h (oldExceptionalStrictClass (n + 1) j (by omega)) = -2) ∧
    (∀ (j : ℕ) (h : j + 3 ≤ n + 1),
      oldExceptionalPairing n hproj j (by omega)
        (oldExceptionalStrictClass (n + 1) (j + 1) (by omega)) = 1) ∧
    (∀ hn : 1 ≤ n,
      oldExceptionalPairing n hproj (n - 1) (by omega) (stepExceptionalPicardClass n) = 1) :=
  ⟨f29_intersection_table_extended k n hproj h0,
    fun j h => ⟨oldExceptionalPairing_totalExceptional_succ n hproj j h hstages,
      oldExceptionalPairing_oldStrictClass_self_eq n hproj j h hstages⟩,
    fun j h => oldExceptionalPairing_oldStrictClass_succ n hproj j h
      (stage_projective_of_le n hstages (j + 1 + 1) (by omega) (by omega)),
    fun hn => oldExceptionalPairing_stepExceptional_pred n hproj hn⟩

/-- **Stage `2`, only `hproj`**: `C_0 · [P] = 1`, `C_0 · E_1^tot = 1`, `C_0 · [C_0] = −2`. -/
theorem f29_intersection_table_adjacent_stage_two (k : Type u) [Field k] [IsAlgClosed k]
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (1 + 1)).structureMap) :
    oldExceptionalPairing 1 hproj 0 (by omega) (stepExceptionalPicardClass 1) = 1 ∧
      oldExceptionalPairing 1 hproj 0 (by omega) (totalExceptionalClass (1 + 1) ⟨0 + 1, by omega⟩) = 1 ∧
      oldExceptionalPairing 1 hproj 0 (by omega) (oldExceptionalStrictClass (1 + 1) 0 (by omega)) = -2 :=
  ⟨oldExceptionalPairing_stepExceptional 0 hproj,
    oldExceptionalPairing_totalExceptional_succ_last 0 hproj,
    oldExceptionalPairing_oldStrictClass_self_eq 1 hproj 0 (by omega)
      (fun i h2 h1 => absurd (le_trans h2 h1) (by omega))⟩

/-- The bundles have exactly one universe parameter. -/
theorem f29_intersection_table_adjacent_universe_check (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (h0 : FiberKernelInvertible (k := k) 0)
    (hstages : ∀ i : ℕ, 2 ≤ i → i ≤ n →
      IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap) : True := by
  have _ := f29_intersection_table_adjacent.{u} k n hproj h0 hstages
  have _ := f29_intersection_table_adjacent_stage_two.{u} k
  trivial

end KltDP.Examples
