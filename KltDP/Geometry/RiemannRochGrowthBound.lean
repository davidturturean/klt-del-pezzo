import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# An elementary quadratic growth bound

The integer self-intersection of an ample surface line bundle is at least
one. This rational inequality bounds the RR quadratic below by n²/4 and
simultaneously makes its complementary intersection negative. The integer
n can be chosen above any prescribed natural number.
-/

namespace KltDP.Geometry.RiemannRochGrowthBound

/-- A quadratic with leading coefficient at least one dominates n²/4 in
the displayed RR normalization, beyond arbitrarily large integers. -/
theorem exists_large_with_quadratic_bound (a b z : ℚ) (ha : 1 ≤ a) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ b < (n : ℚ) * a ∧
      (1 / 4 : ℚ) * (n : ℚ) ^ 2 ≤
        (a * (n : ℚ) ^ 2 - b * (n : ℚ)) / 2 + z := by
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * |b| + 4 * |z| + 1)
  let n := max N M
  have hn : 2 * |b| + 4 * |z| + 1 ≤ (n : ℚ) :=
    hM.trans (by exact_mod_cast (Nat.le_max_right N M))
  have hnOne : (1 : ℚ) ≤ n := by
    linarith [abs_nonneg b, abs_nonneg z]
  have hnZero : (0 : ℚ) ≤ n := le_trans zero_le_one hnOne
  refine ⟨n, Nat.le_max_left N M, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left ha hnZero
    linarith [le_abs_self b, abs_nonneg b, abs_nonneg z]
  · have hquadratic := mul_nonneg (sub_nonneg.mpr hn) hnZero
    have hleading := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (n : ℚ))
    have hlinear := mul_le_mul_of_nonneg_right (le_abs_self b) hnZero
    have hconstant := mul_le_mul_of_nonneg_left hnOne (abs_nonneg z)
    nlinarith [neg_abs_le z]

end KltDP.Geometry.RiemannRochGrowthBound
