import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A least degree from a common denominator

These are the discrete-order steps used when a Cartier multiple makes curve
degrees integral. The degree function and its common denominator are explicit.
No curve, Cartier divisor, nefness, or contraction is postulated here.
-/

namespace KltDP.LinearAlgebra.DiscreteDegree

/-- A nonempty family of positive rational degrees has an attained positive
minimum if one positive natural multiple of every degree is integral. -/
theorem exists_positive_minimum {α : Type*} [Nonempty α]
    (degree : α → ℚ) (d : ℕ) (hd : 0 < d)
    (hpositive : ∀ a, 0 < degree a)
    (hintegral : ∀ a, ∃ n : ℕ, (n : ℚ) = (d : ℚ) * degree a) :
    ∃ a, 0 < degree a ∧ ∀ b, degree a ≤ degree b := by
  classical
  have hex : ∃ n : ℕ, ∃ a, (n : ℚ) = (d : ℚ) * degree a := by
    obtain ⟨a⟩ := ‹Nonempty α›
    obtain ⟨n, hn⟩ := hintegral a
    exact ⟨n, a, hn⟩
  obtain ⟨a, ha⟩ := Nat.find_spec hex
  refine ⟨a, hpositive a, ?_⟩
  intro b
  obtain ⟨n, hn⟩ := hintegral b
  have hmin : Nat.find hex ≤ n := Nat.find_min' hex ⟨b, hn⟩
  have hscaled : (d : ℚ) * degree a ≤ (d : ℚ) * degree b := by
    rw [← ha, ← hn]
    exact_mod_cast hmin
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  exact (mul_le_mul_left hdq).mp hscaled

/-- An effective sum of degrees at least `ell` cannot have degree below
`ell` unless every coefficient vanishes. -/
theorem coefficients_zero_of_sum_lt_minimum {ι : Type*} [Fintype ι]
    (degree : ι → ℚ) (coefficient : ι → ℕ) (ell : ℚ)
    (hell : 0 < ell) (hlower : ∀ i, ell ≤ degree i)
    (hsum : (∑ i, (coefficient i : ℚ) * degree i) < ell) :
    ∀ i, coefficient i = 0 := by
  classical
  intro i
  by_contra hne
  have hpos : ∀ j, 0 ≤ degree j := fun j => le_trans (le_of_lt hell) (hlower j)
  have hi : (1 : ℚ) ≤ (coefficient i : ℚ) := by
    exact_mod_cast (show 1 ≤ coefficient i from Nat.one_le_iff_ne_zero.mpr hne)
  have hterm : ell ≤ (coefficient i : ℚ) * degree i := by
    calc
      ell ≤ degree i := hlower i
      _ = 1 * degree i := (one_mul _).symm
      _ ≤ (coefficient i : ℚ) * degree i := mul_le_mul_of_nonneg_right hi (hpos i)
  have htotal : (coefficient i : ℚ) * degree i ≤
      ∑ j, (coefficient j : ℚ) * degree j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hpos j))
      (Finset.mem_univ i)
  exact (not_lt_of_ge (le_trans hterm htotal)) hsum

end KltDP.LinearAlgebra.DiscreteDegree
