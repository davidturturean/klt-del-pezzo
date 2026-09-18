import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith

/-! Exact positivity cases for the original anticanonical coefficient. -/

namespace KltDP.Examples.FrobeniusAnticanonicalParameterCases

/-- For the original prime `q+1` and `n>2`, the original coefficient is
positive exactly in characteristic two, or in characteristic three with `n=3`. -/
theorem coefficient_pos_iff (q n : ℕ) [Fact (q + 1).Prime] (hn : 2 < n) :
    ((0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2)) ↔
      q = 1 ∨ (q = 2 ∧ n = 3) := by
  have hprime : (q + 1).Prime := Fact.out
  have hq : 1 ≤ q := by
    have htwo := hprime.two_le
    omega
  constructor
  · intro hd
    by_cases hqone : q = 1
    · exact Or.inl hqone
    · have hprod : (0 : ℤ) ≤ ((q : ℤ) - 1) * ((n : ℤ) - 3) :=
        mul_nonneg (by omega) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hd
      have hqlt : (q : ℤ) < 3 := by nlinarith [hprod]
      have hqtwo : q = 2 := by omega
      refine Or.inr ⟨hqtwo, ?_⟩
      subst q
      norm_num at hd
      omega
  · rintro (rfl | ⟨rfl, rfl⟩) <;> norm_num

end KltDP.Examples.FrobeniusAnticanonicalParameterCases
