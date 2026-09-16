import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Alternating sums of dimension recurrences

The adjacent boundary terms in a finite alternating sum cancel. This file
records that integer identity, including both boundary terms. Applications
must prove the recurrence from their actual linear maps and prove that the
boundary terms vanish; no exactness or Euler equality is encoded here.
-/

open scoped BigOperators

namespace KltDP.LinearAlgebra.AlternatingDimensionSum

/-- A recurrence with adjacent boundary terms telescopes, leaving the
initial term and the signed terminal term. -/
theorem alternating_sum_eq_boundary (a b c d : ℕ → ℤ) (e : ℤ)
    (hzero : a 0 - b 0 + c 0 = e + d 0)
    (hstep : ∀ n, a (n + 1) - b (n + 1) + c (n + 1) = d n + d (n + 1))
    (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (a n - b n + c n)) =
      e + (-1 : ℤ) ^ N * d N := by
  induction N with
  | zero => simpa only [Nat.zero_add, Finset.sum_range_one, pow_zero, one_mul] using hzero
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, hstep N, pow_succ]
      ring

/-- If both boundary terms vanish, the alternating sum of the middle
sequence equals the sum of the two outer alternating sums. -/
theorem alternating_sum_additive_of_boundary_zero (a b c d : ℕ → ℤ) (e : ℤ)
    (hzero : a 0 - b 0 + c 0 = e + d 0)
    (hstep : ∀ n, a (n + 1) - b (n + 1) + c (n + 1) = d n + d (n + 1))
    (N : ℕ) (he : e = 0) (hd : d N = 0) :
    (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * b n) =
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n) +
        (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * c n) := by
  have hsum := alternating_sum_eq_boundary a b c d e hzero hstep N
  have hz :
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n) -
        (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * b n) +
          (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * c n) = 0 := by
    simpa only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      he, hd, mul_zero, add_zero] using hsum
  apply sub_eq_zero.mp
  calc
    (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * b n) -
        ((∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n) +
          (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * c n)) =
        -((∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n) -
          (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * b n) +
            (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * c n)) := by ring
    _ = 0 := by rw [hz, neg_zero]

end KltDP.LinearAlgebra.AlternatingDimensionSum
