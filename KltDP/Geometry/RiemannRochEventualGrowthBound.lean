import KltDP.Geometry.RiemannRochGrowthBound

/-!
# The existing RR quadratic bound for all sufficiently large exponents

This is the same explicit rational threshold as `RiemannRochGrowthBound`,
with its proof retained for every natural number beyond that threshold.
No geometric or literature statement is used by this arithmetic adapter.
-/

namespace KltDP.Geometry.RiemannRochGrowthBound

/-- Beyond one positive threshold, the RR quadratic dominates n²/4 and
its linear coefficient is less than n times the leading coefficient. -/
theorem exists_eventual_quadratic_bound (a b z : ℚ) (ha : 1 ≤ a) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      b < (n : ℚ) * a ∧
        (1 / 4 : ℚ) * (n : ℚ) ^ 2 ≤
          (a * (n : ℚ) ^ 2 - b * (n : ℚ)) / 2 + z := by
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * |b| + 4 * |z| + 1)
  refine ⟨max 1 M, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 M), ?_⟩
  intro n hn
  have hthreshold : 2 * |b| + 4 * |z| + 1 ≤ (n : ℚ) :=
    hM.trans (by exact_mod_cast ((Nat.le_max_right 1 M).trans hn))
  have hnOne : (1 : ℚ) ≤ n := by
    linarith [abs_nonneg b, abs_nonneg z]
  have hnZero : (0 : ℚ) ≤ n := le_trans zero_le_one hnOne
  constructor
  · have hmul := mul_le_mul_of_nonneg_left ha hnZero
    linarith [le_abs_self b, abs_nonneg b, abs_nonneg z]
  · have hquadratic := mul_nonneg (sub_nonneg.mpr hthreshold) hnZero
    have hleading := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (n : ℚ))
    have hlinear := mul_le_mul_of_nonneg_right (le_abs_self b) hnZero
    have hconstant := mul_le_mul_of_nonneg_left hnOne (abs_nonneg z)
    nlinarith [neg_abs_le z]

end KltDP.Geometry.RiemannRochGrowthBound
