import KltDP.LinearAlgebra.ChainMatrix
import KltDP.LinearAlgebra.Stieltjes
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# A path with one higher-weight endpoint

The actual path matrix has first diagonal `β`, all other diagonal entries
two, and minus-one entries between successive vertices. A scaled column of
the proved chain Green matrix solves its actual diagonal-minus-two source.
The endpoint formulas and the source's strict scalar inequalities follow.

The matrix comparison theorem states positive definiteness and the row
inequalities explicitly; no geometric path or discrepancy vector is assumed.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

/-- The rank-one determinant lemma specialized to an actual single diagonal
update. This is a direct adapter of Mathlib's matrix determinant lemma. -/
theorem det_add_diagonal_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) (root : ι) (weight : 𝕜) (hA : IsUnit A.det) :
    (A + Matrix.diagonal (Pi.single root weight)).det =
      A.det * (1 + weight * A⁻¹ root root) := by
  have hdiag : Matrix.diagonal (Pi.single root weight) =
      Matrix.replicateCol Unit (Pi.single root weight) *
        Matrix.replicateRow Unit (Pi.single root (1 : 𝕜)) := by
    ext i j
    by_cases hi : i = root <;> by_cases hj : j = root
    · subst i
      subst j
      simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
    · subst i
      simp [Matrix.diagonal_apply, Matrix.mul_apply, Matrix.replicateCol,
        Matrix.replicateRow, hj, Ne.symm hj]
    · subst j
      simp [Matrix.diagonal_apply, Matrix.mul_apply, Matrix.replicateCol,
        Matrix.replicateRow, hi]
    · simp [Matrix.diagonal_apply, Matrix.mul_apply, Matrix.replicateCol,
        Matrix.replicateRow, hi, hj]
  rw [hdiag, Matrix.det_add_replicateCol_mul_replicateRow (ι := Unit) hA]
  congr 1
  rw [Matrix.det_unique (n := Unit)]
  simp only [Matrix.add_apply, Matrix.one_apply, if_pos rfl, if_true]
  rw [← Matrix.replicateRow_vecMul, Matrix.single_one_vecMul,
    Matrix.replicateRow_mul_replicateCol_apply, dotProduct_single]
  ring

/-- A reusable single-diagonal update certificate. A scaled unit-source
column remains a source solution after changing its root diagonal when the
displayed scalar equation holds. No matrix inverse is assumed. -/
theorem diagonal_single_mulVec_scaled_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) (root : ι) (column : ι → 𝕜) (weight scale : 𝕜)
    (hcolumn : A *ᵥ column = Pi.single root 1)
    (hscale : scale * (1 + weight * column root) = weight) :
    (A + Matrix.diagonal (Pi.single root weight)) *ᵥ (scale • column) =
      Pi.single root weight := by
  rw [Matrix.add_mulVec, Matrix.mulVec_smul, hcolumn]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  by_cases hi : i = root
  · subst i
    simp only [Pi.single_eq_same]
    linear_combination hscale
  · simp only [Pi.single_eq_of_ne hi, mul_zero, zero_mul, add_zero]

/-- Denominator for the path with one endpoint of weight `β`. -/
def canonicalEndDenominator (β d : 𝕜) : 𝕜 := (β - 1) * d + β

/-- Coefficient at the higher-weight endpoint. -/
def canonicalEndFirst (β d : 𝕜) : 𝕜 :=
  (β - 2) * (d + 1) / canonicalEndDenominator β d

/-- Coefficient at the other endpoint, whose weight is two when `d ≥ 1`. -/
def canonicalEndLast (β d : 𝕜) : 𝕜 :=
  (β - 2) / canonicalEndDenominator β d

/-- The actual canonical source, supported at the higher-weight endpoint. -/
def canonicalEndSource (d : ℕ) (β : 𝕜) : Fin (d + 1) → 𝕜 :=
  Pi.single (0 : Fin (d + 1)) (β - 2)

/-- The actual weighted path, including the one-vertex case `d=0`. -/
def canonicalEndPath (d : ℕ) (β : 𝕜) : Matrix (Fin (d + 1)) (Fin (d + 1)) 𝕜 :=
  weightTwoChain (d + 1) + Matrix.diagonal (canonicalEndSource d β)

/-- The source is computed from the actual matrix diagonal. -/
theorem canonicalEndPath_diagonal_source (d : ℕ) (β : 𝕜) :
    (fun i => canonicalEndPath d β i i - 2) = canonicalEndSource d β := by
  ext i
  simp [canonicalEndPath, weightTwoChain_apply]

/-- The actual determinant is the endpoint denominator, for every length and
every weight. No nonzero hypothesis is imposed on this identity. -/
theorem det_canonicalEndPath [CharZero 𝕜] (d : ℕ) (β : 𝕜) :
    (canonicalEndPath d β).det = canonicalEndDenominator β (d : 𝕜) := by
  have hden : (d : 𝕜) + 2 ≠ 0 := by
    exact_mod_cast (show d + 2 ≠ 0 by omega)
  rw [canonicalEndPath, canonicalEndSource,
    det_add_diagonal_single (weightTwoChain (d + 1)) 0 (β - 2)
      ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_weightTwoChain (d + 1))),
    det_weightTwoChain, weightTwoChain_inverse_first_diagonal]
  simp only [Nat.add_assoc]
  push_cast
  field_simp [hden]; unfold canonicalEndDenominator; ring

/-- Invertibility of the actual path follows exactly from the explicit
denominator being nonzero, rather than remaining an assumed matrix property. -/
theorem isUnit_canonicalEndPath_iff [CharZero 𝕜] (d : ℕ) (β : 𝕜) :
    IsUnit (canonicalEndPath d β) ↔ canonicalEndDenominator β (d : 𝕜) ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, det_canonicalEndPath, isUnit_iff_ne_zero]

/-- A candidate built from an actual Green column of the weight-two chain. -/
def canonicalEndSolution (d : ℕ) (β : 𝕜) : Fin (d + 1) → 𝕜 :=
  ((β - 2) * ((d + 2 : ℕ) : 𝕜) / canonicalEndDenominator β (d : 𝕜)) •
    (fun i : Fin (d + 1) => chainGreen (𝕜 := 𝕜) (d + 1) i (0 : Fin (d + 1)))

/-- Direct calculation of the candidate's two endpoint values. -/
theorem canonicalEndSolution_endpoints [CharZero 𝕜] (d : ℕ) (β : 𝕜)
    (hE : canonicalEndDenominator β (d : 𝕜) ≠ 0) :
    canonicalEndSolution d β 0 = canonicalEndFirst β (d : 𝕜) ∧
      canonicalEndSolution d β (Fin.last d) = canonicalEndLast β (d : 𝕜) := by
  have hden : (d : 𝕜) + 2 ≠ 0 := by
    exact_mod_cast (show d + 2 ≠ 0 by omega)
  constructor
  · simp only [canonicalEndSolution, Pi.smul_apply, smul_eq_mul, chainGreen_apply,
      Fin.val_zero, min_self, max_self, zero_add, Nat.sub_zero, Nat.add_assoc]
    unfold canonicalEndFirst
    push_cast
    field_simp [hE, hden]; ring
  · simp only [canonicalEndSolution, Pi.smul_apply, smul_eq_mul, chainGreen_apply,
      Fin.val_last, Fin.val_zero, Nat.min_zero, Nat.max_zero, zero_add,
      Nat.add_sub_cancel_left, Nat.cast_one, one_mul, Nat.add_assoc]
    unfold canonicalEndLast
    push_cast
    field_simp [hE, hden]; ring

/-- The candidate solves the actual weighted matrix equation. This proof
reuses the all-length chain Green certificate and a single-diagonal update. -/
theorem canonicalEndPath_mul_solution [CharZero 𝕜] (d : ℕ) (β : 𝕜)
    (hE : canonicalEndDenominator β (d : 𝕜) ≠ 0) :
    canonicalEndPath d β *ᵥ canonicalEndSolution d β = canonicalEndSource d β := by
  have hden : (d : 𝕜) + 2 ≠ 0 := by
    exact_mod_cast (show d + 2 ≠ 0 by omega)
  have hcolumn : weightTwoChain (d + 1) *ᵥ
      (fun i => chainGreen (𝕜 := 𝕜) (d + 1) i 0) = Pi.single 0 1 := by
    have hg : (fun i => chainGreen (𝕜 := 𝕜) (d + 1) i 0) =
        chainGreen (d + 1) *ᵥ Pi.single 0 1 :=
      (Matrix.mulVec_single_one (chainGreen (d + 1)) 0).symm
    rw [hg, Matrix.mulVec_mulVec, weightTwoChain_mul_chainGreen, Matrix.one_mulVec]
  apply diagonal_single_mulVec_scaled_column (weightTwoChain (d + 1)) 0
    (fun i : Fin (d + 1) => chainGreen (𝕜 := 𝕜) (d + 1) i 0) (β - 2)
    ((β - 2) * ((d + 2 : ℕ) : 𝕜) / canonicalEndDenominator β (d : 𝕜)) hcolumn
  rw [chainGreen_apply]
  simp only [Fin.val_zero, min_self, max_self, zero_add, Nat.sub_zero,
    Nat.cast_one, one_mul, Nat.add_assoc]
  push_cast
  field_simp [hE, hden]; unfold canonicalEndDenominator; ring

/-- The actual inverse solution has the two explicit endpoint values whenever
the actual weighted path is invertible. -/
theorem canonicalEndPath_inverse_endpoints [CharZero 𝕜] (d : ℕ) (β : 𝕜)
    (hE : canonicalEndDenominator β (d : 𝕜) ≠ 0) :
    ((canonicalEndPath d β)⁻¹ *ᵥ canonicalEndSource d β) 0 =
        canonicalEndFirst β (d : 𝕜) ∧
      ((canonicalEndPath d β)⁻¹ *ᵥ canonicalEndSource d β) (Fin.last d) =
        canonicalEndLast β (d : 𝕜) := by
  letI : Invertible (canonicalEndPath d β) :=
    ((isUnit_canonicalEndPath_iff d β).mpr hE).invertible
  have hsol : (canonicalEndPath d β)⁻¹ *ᵥ canonicalEndSource d β =
      canonicalEndSolution d β :=
    Matrix.inv_mulVec_eq_vec (canonicalEndPath_mul_solution d β hE).symm
  rw [hsol]
  exact canonicalEndSolution_endpoints d β hE

/-- The sum of the two endpoint coefficients, in the form used in §9. -/
theorem canonicalEnd_sum (β d : 𝕜) :
    canonicalEndFirst β d + canonicalEndLast β d =
      (β - 2) * (d + 2) / canonicalEndDenominator β d := by
  unfold canonicalEndFirst canonicalEndLast
  ring

/-- The exact endpoint ratio for the isolated path. -/
theorem canonicalEnd_first_eq (β d : 𝕜) :
    canonicalEndFirst β d = (d + 1) * canonicalEndLast β d := by
  unfold canonicalEndFirst canonicalEndLast
  ring

/-- Weight-three specialization of both endpoint expressions. -/
theorem canonicalEnd_three (d : 𝕜) :
    canonicalEndFirst 3 d = (d + 1) / (2 * d + 3) ∧
      canonicalEndLast 3 d = 1 / (2 * d + 3) := by
  constructor <;> norm_num [canonicalEndFirst, canonicalEndLast, canonicalEndDenominator]

section Ordered

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Positivity of the actual path denominator in the intended range. -/
theorem canonicalEndDenominator_pos {β d : 𝕜} (hβ : 3 ≤ β) (hd : 0 ≤ d) :
    0 < canonicalEndDenominator β d := by
  unfold canonicalEndDenominator
  have hprod : 0 ≤ (β - 1) * d := mul_nonneg (by linarith) hd
  linarith

/-- The weight-three endpoint sum is strictly greater than one half. -/
theorem canonicalEnd_three_sum_gt_half {d : 𝕜} (hd : 0 ≤ d) :
    (1 : 𝕜) / 2 < canonicalEndFirst 3 d + canonicalEndLast 3 d := by
  rw [canonicalEnd_sum]
  norm_num only [canonicalEndDenominator, show (3 : 𝕜) - 2 = 1 by norm_num,
    show (3 : 𝕜) - 1 = 2 by norm_num, one_mul]
  apply (div_lt_div_iff₀ (by norm_num : (0 : 𝕜) < 2) (by linarith)).mpr
  linarith

/-- For any endpoint weight at least four, the sum exceeds two thirds. -/
theorem canonicalEnd_sum_gt_two_thirds {β d : 𝕜} (hβ : 4 ≤ β) (hd : 0 ≤ d) :
    (2 : 𝕜) / 3 < canonicalEndFirst β d + canonicalEndLast β d := by
  rw [canonicalEnd_sum]
  apply (div_lt_div_iff₀ (by norm_num : (0 : 𝕜) < 3)
    (canonicalEndDenominator_pos (by linarith) hd)).mpr
  have hprod : 0 ≤ (β - 4) * d := mul_nonneg (by linarith) hd
  unfold canonicalEndDenominator
  nlinarith

/-- The canonical endpoint is at least `1/11` when its distance from a
weight-three endpoint is at most four. -/
theorem canonicalEnd_three_last_ge_eleventh {d : 𝕜} (hd : 0 ≤ d) (hfour : d ≤ 4) :
    (1 : 𝕜) / 11 ≤ canonicalEndLast 3 d := by
  rw [(canonicalEnd_three d).2]
  apply (div_le_div_iff₀ (by norm_num : (0 : 𝕜) < 11) (by linarith)).mpr
  linarith

/-- The actual path has nonpositive off-diagonal entries. -/
theorem canonicalEndPath_offDiagonal (d : ℕ) (β : 𝕜)
    (i j : Fin (d + 1)) (hij : i ≠ j) : canonicalEndPath d β i j ≤ 0 := by
  simp only [canonicalEndPath, Matrix.add_apply, Matrix.diagonal_apply_ne _ hij,
    weightTwoChain_apply, if_neg hij, add_zero]
  split_ifs <;> norm_num

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- Actual path comparison for a vector whose row images dominate the source.
The geometric restriction and its positive definiteness are explicit future
application obligations. -/
theorem canonicalEndPath_endpoint_lower_bounds (d : ℕ) (β : 𝕜)
    (hE : canonicalEndDenominator β (d : 𝕜) ≠ 0)
    (hA : (canonicalEndPath d β).PosDef) (coeff : Fin (d + 1) → 𝕜)
    (hrows : ∀ i, canonicalEndSource d β i ≤ (canonicalEndPath d β *ᵥ coeff) i) :
    canonicalEndFirst β (d : 𝕜) ≤ coeff 0 ∧
      canonicalEndLast β (d : 𝕜) ≤ coeff (Fin.last d) := by
  have hdiff : ∀ i, 0 ≤ (canonicalEndPath d β *ᵥ
      (coeff - canonicalEndSolution d β)) i := by
    rw [Matrix.mulVec_sub, canonicalEndPath_mul_solution d β hE]
    intro i
    exact sub_nonneg.mpr (hrows i)
  have hnonneg := nonneg_of_mulVec_nonneg hA (canonicalEndPath_offDiagonal d β) hdiff
  obtain ⟨hfirst, hlast⟩ := canonicalEndSolution_endpoints d β hE
  constructor
  · rw [← hfirst]
    exact sub_nonneg.mp (hnonneg 0)
  · rw [← hlast]
    exact sub_nonneg.mp (hnonneg (Fin.last d))

end Ordered

end KltDP.LinearAlgebra
