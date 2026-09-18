import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-!
# The strict weighted bound for a point blowup

This finite-sum calculation consumes the actual multiplicities supplied by
the geometric SNC theorem. It needs only nonnegative multiplicities with
total at most two, not a separate simplicity assertion for every branch.
-/

open scoped BigOperators

namespace KltDP.Geometry.DiscrepancyWeightedMultiplicity

theorem neg_two_lt_weighted_sum {ι : Type*} (s : Finset ι) (d m : ι → ℚ)
    (hd : ∀ i ∈ s, (-1 : ℚ) < d i)
    (hm : ∀ i ∈ s, 0 ≤ m i) (htotal : (∑ i ∈ s, m i) ≤ 2) :
    (-2 : ℚ) < ∑ i ∈ s, d i * m i := by
  by_cases hpos : ∃ i ∈ s, 0 < m i
  · have hsum : 0 < ∑ i ∈ s, (d i + 1) * m i := by
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (by linarith [hd i hi]) (hm i hi)
      · obtain ⟨i, hi, hmi⟩ := hpos
        exact ⟨i, hi, mul_pos (by linarith [hd i hi]) hmi⟩
    have heq : (∑ i ∈ s, (d i + 1) * m i) =
        (∑ i ∈ s, d i * m i) + ∑ i ∈ s, m i := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
    rw [heq] at hsum
    linarith
  · have hzero : ∀ i ∈ s, m i = 0 := by
      intro i hi
      exact le_antisymm (le_of_not_gt (fun h => hpos ⟨i, hi, h⟩)) (hm i hi)
    have hsum : (∑ i ∈ s, d i * m i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i hi, mul_zero]
    rw [hsum]
    norm_num

theorem neg_one_lt_one_add_weighted_sum {ι : Type*} (s : Finset ι) (d m : ι → ℚ)
    (hd : ∀ i ∈ s, (-1 : ℚ) < d i)
    (hm : ∀ i ∈ s, 0 ≤ m i) (htotal : (∑ i ∈ s, m i) ≤ 2) :
    (-1 : ℚ) < 1 + ∑ i ∈ s, d i * m i := by
  linarith [neg_two_lt_weighted_sum s d m hd hm htotal]

end KltDP.Geometry.DiscrepancyWeightedMultiplicity

#print axioms KltDP.Geometry.DiscrepancyWeightedMultiplicity.neg_two_lt_weighted_sum
#print axioms KltDP.Geometry.DiscrepancyWeightedMultiplicity.neg_one_lt_one_add_weighted_sum
