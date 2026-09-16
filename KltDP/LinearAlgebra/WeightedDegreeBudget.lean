import KltDP.LinearAlgebra.DiscreteDegree

/-!
# Multiplicity budgets from a positive degree lower bound

These adapters reuse Mathlib's finite-sum monotonicity and distributivity.
They apply to any explicitly finite set of components with natural
multiplicities. The geometric application must first remove exceptional
components of degree zero and prove the lower bound on the remaining primes.
No effectivity, Cartier, or geometric degree identity is assumed by a wrapper.
-/

namespace KltDP.LinearAlgebra.DiscreteDegree

open scoped BigOperators

/-- A lower bound on component degrees bounds the total multiplicity.
The component set is an actual finite set, not a finiteness assumption on
all prime curves. -/
theorem minimum_mul_total_multiplicity_le {ι : Type*}
    (s : Finset ι) (degree : ι → ℚ) (coefficient : ι → ℕ) (ell : ℚ)
    (hlower : ∀ i ∈ s, ell ≤ degree i) :
    ell * ((∑ i ∈ s, coefficient i : ℕ) : ℚ) ≤
      ∑ i ∈ s, (coefficient i : ℚ) * degree i := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_comm ell] using
    mul_le_mul_of_nonneg_left (hlower i hi) (Nat.cast_nonneg (coefficient i) :
      (0 : ℚ) ≤ coefficient i)

/-- A strict degree budget gives a strict natural-number multiplicity
budget, for every natural threshold. -/
theorem total_multiplicity_lt_of_degree_lt {ι : Type*}
    (s : Finset ι) (degree : ι → ℚ) (coefficient : ι → ℕ) (ell : ℚ)
    (hell : 0 < ell) (hlower : ∀ i ∈ s, ell ≤ degree i) (n : ℕ)
    (hdegree : (∑ i ∈ s, (coefficient i : ℚ) * degree i) < ell * n) :
    (∑ i ∈ s, coefficient i) < n := by
  have h := lt_of_le_of_lt
    (minimum_mul_total_multiplicity_le s degree coefficient ell hlower) hdegree
  have hcast := (mul_lt_mul_left hell).mp h
  exact_mod_cast hcast

/-- Below twice the least degree, the exterior part has total
multiplicity at most one. Curve realization remains a geometric adapter. -/
theorem total_multiplicity_le_one_of_degree_lt_twice {ι : Type*}
    (s : Finset ι) (degree : ι → ℚ) (coefficient : ι → ℕ) (ell : ℚ)
    (hell : 0 < ell) (hlower : ∀ i ∈ s, ell ≤ degree i)
    (hdegree : (∑ i ∈ s, (coefficient i : ℚ) * degree i) < 2 * ell) :
    (∑ i ∈ s, coefficient i) ≤ 1 := by
  have h := total_multiplicity_lt_of_degree_lt s degree coefficient ell hell hlower 2
    (by simpa only [Nat.cast_ofNat, mul_comm ell] using hdegree)
  omega

end KltDP.LinearAlgebra.DiscreteDegree
