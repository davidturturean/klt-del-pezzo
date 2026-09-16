import Mathlib.Tactic

/-!
# Support obligation U-AVERAGE-DESCENT: weighted averaging finds a shorter prime

Plan contract (`U-AVERAGE-DESCENT`): "If an effective adjoint has at least two
exterior components counted with positive integral coefficients, some actual
exterior prime has degree at most half its total degree; if coefficient mass is
one, eliminate the exceptional remainder geometrically."

This module proves the arithmetic clause. An effective divisor
`N = Σ_i a_i Z_i + Z_exc` with integer coefficients `a_i ≥ 1` on at least two
exterior primes `Z_i` of positive `L`-degree `d_i`, and an exceptional
remainder of nonnegative `L`-degree `z`, has total degree
`deg = Σ_i a_i d_i + z`, and some `i` satisfies `d_i ≤ deg / 2`. The degrees
are arbitrary rationals here; no divisor, curve or nef class is constructed.

The second clause (coefficient mass one, geometric elimination of the
exceptional remainder) and the identification of `d_i` with actual `L`-degrees
of actual exterior primes are the geometric obligations F02 and F20.
-/

namespace KltDP.Support

open scoped BigOperators

/-- **Weighted averaging.** Among at least two positive quantities `d i` weighted
by integers `a i ≥ 1`, with a nonnegative remainder `z`, some `d i` is at most
half of the weighted total `Σ a i * d i + z`. -/
theorem exists_le_half_of_two_weighted {ι : Type*} (s : Finset ι) (hs : 2 ≤ s.card)
    (a : ι → ℕ) (ha : ∀ i ∈ s, 1 ≤ a i) (d : ι → ℚ) (hd : ∀ i ∈ s, 0 < d i)
    (z : ℚ) (hz : 0 ≤ z) :
    ∃ i ∈ s, d i ≤ (∑ j ∈ s, (a j : ℚ) * d j + z) / 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  set D := ∑ k ∈ s, (a k : ℚ) * d k + z with hD
  have hterm : ∀ k ∈ s, d k ≤ (a k : ℚ) * d k := fun k hk => by
    have h1 : (1 : ℚ) ≤ a k := by exact_mod_cast ha k hk
    have := hd k hk
    nlinarith
  have hnonneg : ∀ k ∈ s, 0 ≤ (a k : ℚ) * d k := fun k hk =>
    mul_nonneg (by positivity) (le_of_lt (hd k hk))
  have hpair : (a i : ℚ) * d i + (a j : ℚ) * d j ≤ ∑ k ∈ s, (a k : ℚ) * d k := by
    have hsub : ({i, j} : Finset ι) ⊆ s := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k hk _ => hnonneg k hk)
    rwa [Finset.sum_pair hij] at this
  have hi' := hcon i hi
  have hj' := hcon j hj
  have hti := hterm i hi
  have htj := hterm j hj
  linarith


/-- **Coefficient-mass form.** With total exterior coefficient mass `Σ a_i ≥ 2` (the
manuscript's `M ≥ 2`, which also allows a single component of coefficient at least two),
some component has degree at most half the weighted total. -/
theorem exists_le_half_of_mass_two {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (ha : ∀ i ∈ s, 1 ≤ a i) (hmass : 2 ≤ ∑ i ∈ s, a i)
    (d : ι → ℚ) (hd : ∀ i ∈ s, 0 < d i) (z : ℚ) (hz : 0 ≤ z) :
    ∃ i ∈ s, d i ≤ (∑ j ∈ s, (a j : ℚ) * d j + z) / 2 := by
  classical
  by_cases hbig : ∃ i ∈ s, 2 ≤ a i
  · obtain ⟨i, hi, h2⟩ := hbig
    refine ⟨i, hi, ?_⟩
    have hterm : 2 * d i ≤ (a i : ℚ) * d i := by
      have : (2 : ℚ) ≤ a i := by exact_mod_cast h2
      have := hd i hi
      nlinarith
    have hnonneg : ∀ k ∈ s, 0 ≤ (a k : ℚ) * d k := fun k hk =>
      mul_nonneg (by positivity) (le_of_lt (hd k hk))
    have hle : (a i : ℚ) * d i ≤ ∑ k ∈ s, (a k : ℚ) * d k := Finset.single_le_sum hnonneg hi
    linarith
  · push_neg at hbig
    have hone : ∀ i ∈ s, a i = 1 := fun i hi => by have := ha i hi; have := hbig i hi; omega
    have hcard : 2 ≤ s.card := by
      have : ∑ i ∈ s, a i = s.card := by
        rw [Finset.card_eq_sum_ones]; exact Finset.sum_congr rfl hone
      omega
    exact exists_le_half_of_two_weighted s hcard a ha d hd z hz

/-- **U-AVERAGE-DESCENT**, arithmetic clause. -/
theorem u_average_descent {ι : Type*} (s : Finset ι)
    (a : ι → ℕ) (ha : ∀ i ∈ s, 1 ≤ a i) (hmass : 2 ≤ ∑ i ∈ s, a i)
    (d : ι → ℚ) (hd : ∀ i ∈ s, 0 < d i) (z : ℚ) (hz : 0 ≤ z) :
    ∃ i ∈ s, d i ≤ (∑ j ∈ s, (a j : ℚ) * d j + z) / 2 :=
  exists_le_half_of_mass_two s a ha hmass d hd z hz

/-- Strict form: with at least two components, some `d i` is strictly less than
the total degree (so the located prime is strictly shorter than the adjoint). -/
theorem exists_lt_total_of_two_weighted {ι : Type*} (s : Finset ι) (hs : 2 ≤ s.card)
    (a : ι → ℕ) (ha : ∀ i ∈ s, 1 ≤ a i) (d : ι → ℚ) (hd : ∀ i ∈ s, 0 < d i)
    (z : ℚ) (hz : 0 ≤ z) :
    ∃ i ∈ s, d i < ∑ j ∈ s, (a j : ℚ) * d j + z := by
  obtain ⟨i, hi, hle⟩ := exists_le_half_of_two_weighted s hs a ha d hd z hz
  refine ⟨i, hi, ?_⟩
  have hpos : 0 < ∑ j ∈ s, (a j : ℚ) * d j + z := by
    have : 0 < d i := hd i hi
    linarith
  linarith

end KltDP.Support
