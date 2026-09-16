import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Weight-two chain matrices and their Green functions

This module defines the actual length-`n` chain matrix on `Fin n` and certifies
its inverse by matrix multiplication. The scalar proof is the second-difference
identity for a piecewise linear function with zero boundary values.

The endpoint diagonal `n/(n+1)` is the chain contribution used in manuscript
`lem:rooted-trees` (Section 9.1, planning task WP-R39). No finite enumeration,
geometric realization, or positive-definiteness hypothesis is used to certify
the inverse. The length-zero matrix is included.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

private def neighborMatrix {ι : Type*} [DecidableEq ι]
    (neighbor : ι → Option ι) : Matrix ι ι 𝕜 :=
  fun i j => if neighbor i = some j then 1 else 0

private theorem neighborMatrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (neighbor : ι → Option ι) (x : ι → 𝕜) (i : ι) :
    (neighborMatrix neighbor *ᵥ x) i = (neighbor i).elim 0 x := by
  cases h : neighbor i with
  | none => simp [neighborMatrix, Matrix.mulVec, dotProduct, h]
  | some k => simp [neighborMatrix, Matrix.mulVec, dotProduct, h, ite_mul]

private def chainPrev {n : ℕ} (i : Fin n) : Option (Fin n) :=
  if h : 0 < i.val then some ⟨i.val - 1, by have := i.isLt; omega⟩ else none

private def chainNext {n : ℕ} (i : Fin n) : Option (Fin n) :=
  if h : i.val + 1 < n then some ⟨i.val + 1, h⟩ else none

/-- The matrix with diagonal two and entry minus one between successive
indices. Missing endpoint neighbors contribute zero. -/
def weightTwoChain (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  (2 : 𝕜) • 1 - neighborMatrix chainPrev - neighborMatrix chainNext

private theorem chainPrev_eq_some {n : ℕ} (i j : Fin n) :
    chainPrev i = some j ↔ j.val + 1 = i.val := by
  simp only [chainPrev]
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
    omega
  · simp only [reduceCtorEq, false_iff]
    omega

private theorem chainNext_eq_some {n : ℕ} (i j : Fin n) :
    chainNext i = some j ↔ i.val + 1 = j.val := by
  simp only [chainNext]
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
  · simp only [reduceCtorEq, false_iff]
    have := j.isLt
    omega

/-- Agreement with the conventional entrywise definition of the Cartan
matrix of a path. In particular, the two endpoint cases are genuine matrix
entries, not separate assumptions. -/
theorem weightTwoChain_apply (n : ℕ) (i j : Fin n) :
    weightTwoChain (𝕜 := 𝕜) n i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  simp only [weightTwoChain, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, neighborMatrix, chainPrev_eq_some, chainNext_eq_some]
  by_cases hij : i = j
  · subst j
    simp
  · have hij' : i.val ≠ j.val := by simpa only [Fin.ext_iff] using hij
    split_ifs <;> norm_num at * <;> omega

/-- A chain matrix is the negative discrete second derivative, with zero
boundary values at positions zero and `n+1`. -/
theorem weightTwoChain_mulVec_of_boundary (n : ℕ) (f : ℕ → 𝕜)
    (hzero : f 0 = 0) (hlast : f (n + 1) = 0) (i : Fin n) :
    (weightTwoChain n *ᵥ (fun j => f (j.val + 1))) i =
      2 * f (i.val + 1) - f i.val - f (i.val + 2) := by
  have hprev : (chainPrev i).elim 0 (fun j => f (j.val + 1)) = f i.val := by
    unfold chainPrev
    split_ifs with h
    · simp only [Option.elim_some]
      congr 1
      omega
    · simp only [Option.elim_none]
      have hi : i.val = 0 := by omega
      simpa only [hi] using hzero.symm
  have hnext : (chainNext i).elim 0 (fun j => f (j.val + 1)) = f (i.val + 2) := by
    unfold chainNext
    split_ifs with h
    · simp only [Option.elim_some]
    · simp only [Option.elim_none]
      have hi : i.val + 2 = n + 1 := by have := i.isLt; omega
      simpa only [hi] using hlast.symm
  simp only [weightTwoChain, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    neighborMatrix_mulVec, hprev, hnext]

private def chainNumerator (n j k : ℕ) : 𝕜 :=
  if k ≤ j + 1 then
    (k : 𝕜) * (((n + 1 : ℕ) : 𝕜) - ((j + 1 : ℕ) : 𝕜))
  else
    ((j + 1 : ℕ) : 𝕜) * (((n + 1 : ℕ) : 𝕜) - (k : 𝕜))

private theorem chainNumerator_of_le {n j k : ℕ} (h : k ≤ j + 1) :
    chainNumerator (𝕜 := 𝕜) n j k =
      (k : 𝕜) * (((n + 1 : ℕ) : 𝕜) - ((j + 1 : ℕ) : 𝕜)) := by
  simp only [chainNumerator, if_pos h]

private theorem chainNumerator_of_ge {n j k : ℕ} (h : j + 1 ≤ k) :
    chainNumerator (𝕜 := 𝕜) n j k =
      ((j + 1 : ℕ) : 𝕜) * (((n + 1 : ℕ) : 𝕜) - (k : 𝕜)) := by
  by_cases h' : k ≤ j + 1
  · have hk : k = j + 1 := Nat.le_antisymm h' h
    simp [chainNumerator, hk]
  · simp [chainNumerator, h']

private theorem chainNumerator_zero (n j : ℕ) :
    chainNumerator (𝕜 := 𝕜) n j 0 = 0 := by simp [chainNumerator]

private theorem chainNumerator_last {n j : ℕ} (hj : j < n) :
    chainNumerator (𝕜 := 𝕜) n j (n + 1) = 0 := by
  rw [chainNumerator_of_ge (by omega : j + 1 ≤ n + 1)]
  simp

private theorem chainNumerator_second_difference (n i j : ℕ) :
    2 * chainNumerator (𝕜 := 𝕜) n j (i + 1) - chainNumerator n j i -
      chainNumerator n j (i + 2) = if i = j then ((n + 1 : ℕ) : 𝕜) else 0 := by
  rcases lt_trichotomy i j with hij | heq | hji
  · rw [chainNumerator_of_le (by omega : i + 1 ≤ j + 1),
      chainNumerator_of_le (by omega : i ≤ j + 1),
      chainNumerator_of_le (by omega : i + 2 ≤ j + 1), if_neg (by omega : i ≠ j)]
    push_cast
    ring
  · subst j
    rw [chainNumerator_of_le (by omega : i + 1 ≤ i + 1),
      chainNumerator_of_le (by omega : i ≤ i + 1),
      chainNumerator_of_ge (by omega : i + 1 ≤ i + 2), if_pos rfl]
    push_cast
    ring
  · rw [chainNumerator_of_ge (by omega : j + 1 ≤ i + 1),
      chainNumerator_of_ge (by omega : j + 1 ≤ i),
      chainNumerator_of_ge (by omega : j + 1 ≤ i + 2), if_neg (by omega : i ≠ j)]
    push_cast
    ring

/-- The explicit Green matrix, before identifying it with the inverse. -/
def chainGreen (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  fun i j => chainNumerator n j.val (i.val + 1) / ((n + 1 : ℕ) : 𝕜)

/-- The usual minimum/maximum formula for a chain's Green entries. Every
subtraction inside a cast is natural subtraction with a proved index bound. -/
theorem chainGreen_apply (n : ℕ) (i j : Fin n) :
    chainGreen (𝕜 := 𝕜) n i j =
      (((min i.val j.val + 1 : ℕ) : 𝕜) * ((n - max i.val j.val : ℕ) : 𝕜)) /
        ((n + 1 : ℕ) : 𝕜) := by
  by_cases hij : i.val ≤ j.val
  · rw [chainGreen, chainNumerator_of_le (by omega : i.val + 1 ≤ j.val + 1),
      min_eq_left hij, max_eq_right hij, Nat.cast_sub (Nat.le_of_lt j.isLt)]
    push_cast
    ring
  · have hji : j.val ≤ i.val := by omega
    rw [chainGreen, chainNumerator_of_ge (by omega : j.val + 1 ≤ i.val + 1),
      min_eq_right hji, max_eq_left hji, Nat.cast_sub (Nat.le_of_lt i.isLt)]
    push_cast
    ring

variable [CharZero 𝕜]

/-- A symbolic certificate for every length: multiplying the actual chain
matrix by the explicit Green matrix gives the identity. -/
theorem weightTwoChain_mul_chainGreen (n : ℕ) :
    weightTwoChain (𝕜 := 𝕜) n * chainGreen n = 1 := by
  ext i j
  have hden : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrow := weightTwoChain_mulVec_of_boundary n
    (fun k => chainNumerator (𝕜 := 𝕜) n j.val k / ((n + 1 : ℕ) : 𝕜))
    (by simp only [chainNumerator_zero, zero_div])
    (by simp only [chainNumerator_last j.isLt, zero_div]) i
  change (weightTwoChain n *ᵥ (fun k =>
    chainNumerator n j.val (k.val + 1) / ((n + 1 : ℕ) : 𝕜))) i =
      (1 : Matrix _ _ 𝕜) i j
  rw [hrow]
  calc
    _ = (2 * chainNumerator n j.val (i.val + 1) - chainNumerator n j.val i.val -
        chainNumerator n j.val (i.val + 2)) / ((n + 1 : ℕ) : 𝕜) := by ring
    _ = (if i.val = j.val then ((n + 1 : ℕ) : 𝕜) else 0) /
        ((n + 1 : ℕ) : 𝕜) := by rw [chainNumerator_second_difference]
    _ = (1 : Matrix _ _ 𝕜) i j := by
      by_cases hij : i = j
      · subst j
        simpa only [Matrix.one_apply, if_pos rfl] using (div_self hden)
      · have hij' : i.val ≠ j.val := by simpa only [Fin.ext_iff] using hij
        simp [Matrix.one_apply, hij, hij']

/-- The chain inverse equals the explicitly certified Green matrix. -/
theorem weightTwoChain_inverse (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) n)⁻¹ = chainGreen n :=
  Matrix.inv_eq_right_inv (weightTwoChain_mul_chainGreen n)

/-- Closed inverse entry formula for every pair of chain coordinates. -/
theorem weightTwoChain_inverse_apply (n : ℕ) (i j : Fin n) :
    (weightTwoChain (𝕜 := 𝕜) n)⁻¹ i j =
      (((min i.val j.val + 1 : ℕ) : 𝕜) * ((n - max i.val j.val : ℕ) : 𝕜)) /
        ((n + 1 : ℕ) : 𝕜) := by
  rw [weightTwoChain_inverse, chainGreen_apply]

/-- The inverse exists also for the empty chain; this result is obtained from
the same matrix certificate for every `n`. -/
theorem isUnit_weightTwoChain (n : ℕ) : IsUnit (weightTwoChain (𝕜 := 𝕜) n) := by
  exact (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (weightTwoChain_mul_chainGreen (𝕜 := 𝕜) n))

/-- Endpoint Schur contribution of a nonempty chain: a chain of length `n+1`
contributes `(n+1)/(n+2)`. -/
theorem weightTwoChain_inverse_first_diagonal (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) (n + 1))⁻¹ 0 0 =
      ((n + 1 : ℕ) : 𝕜) / ((n + 2 : ℕ) : 𝕜) := by
  rw [weightTwoChain_inverse_apply]
  simp [Nat.add_assoc]

/-- The off-diagonal endpoint entry of a length-`n+1` chain is `1/(n+2)`. -/
theorem weightTwoChain_inverse_endpoints (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) (n + 1))⁻¹ 0 (Fin.last n) =
      1 / ((n + 2 : ℕ) : 𝕜) := by
  rw [weightTwoChain_inverse_apply]
  simp [Nat.add_assoc]

omit [CharZero 𝕜] in
/-- The matrix of the empty chain is the empty identity matrix. -/
theorem weightTwoChain_zero : weightTwoChain (𝕜 := 𝕜) 0 = 1 := by
  ext i
  exact Fin.elim0 i

omit [CharZero 𝕜] in
/-- Deleting the first row and column leaves the shorter chain. -/
theorem weightTwoChain_succ_submatrix (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) (n + 1)).submatrix Fin.succ Fin.succ =
      weightTwoChain n := by
  ext i j
  simp [Matrix.submatrix_apply, weightTwoChain_apply, Fin.ext_iff]

private theorem weightTwoChain_adjugate (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) n).adjugate =
      (weightTwoChain (𝕜 := 𝕜) n).det • chainGreen (𝕜 := 𝕜) n := by
  calc
    _ = (weightTwoChain n).adjugate * (weightTwoChain n * chainGreen n) := by
      rw [weightTwoChain_mul_chainGreen, Matrix.mul_one]
    _ = ((weightTwoChain n).adjugate * weightTwoChain n) * chainGreen n := by
      rw [Matrix.mul_assoc]
    _ = ((weightTwoChain n).det • (1 : Matrix _ _ 𝕜)) * chainGreen n := by
      rw [Matrix.adjugate_mul]
    _ = _ := by rw [Matrix.smul_mul, Matrix.one_mul]

/-- Cofactor/Green recurrence used to evaluate the determinant. This follows
from actual adjugate entries, not from an assumed tridiagonal determinant
recurrence. -/
theorem weightTwoChain_det_recurrence (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) n).det = (weightTwoChain (n + 1)).det *
      (((n + 1 : ℕ) : 𝕜) / ((n + 2 : ℕ) : 𝕜)) := by
  have hcofactor : (weightTwoChain (𝕜 := 𝕜) (n + 1)).adjugate 0 0 =
      (weightTwoChain n).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.val_zero, zero_add, pow_zero, one_mul, Fin.succAbove_zero,
      weightTwoChain_succ_submatrix]
  rw [← hcofactor, weightTwoChain_adjugate]
  change (weightTwoChain (n + 1)).det * chainGreen (n + 1) 0 0 = _
  rw [← weightTwoChain_inverse, weightTwoChain_inverse_first_diagonal]

/-- The determinant of the length-`n` weight-two chain is exactly `n+1`,
including the empty determinant `1`. -/
theorem det_weightTwoChain (n : ℕ) :
    (weightTwoChain (𝕜 := 𝕜) n).det = ((n + 1 : ℕ) : 𝕜) := by
  induction n with
  | zero => simp [weightTwoChain_zero]
  | succ n ih =>
    have hrec := weightTwoChain_det_recurrence (𝕜 := 𝕜) n
    rw [ih] at hrec
    have hden : ((n + 2 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnum : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hmul : ((n + 1 : ℕ) : 𝕜) * ((n + 2 : ℕ) : 𝕜) =
        (weightTwoChain (n + 1)).det * ((n + 1 : ℕ) : 𝕜) :=
      (eq_div_iff hden).mp (by simpa only [mul_div_assoc] using hrec)
    have hdet : (weightTwoChain (𝕜 := 𝕜) (n + 1)).det = ((n + 2 : ℕ) : 𝕜) :=
      mul_right_cancel₀ hnum (hmul.symm.trans (mul_comm _ _))
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hdet

end KltDP.LinearAlgebra
