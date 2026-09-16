import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Numerical formulas for the Frobenius family

This module proves only arithmetic statements. In particular, `canonicalScale`
and `canonicalSquare` are rational numbers, not invariants of a constructed
surface. Their identification with geometric invariants is a separate task.

All subtraction in the parameters takes place after casting to `ℤ` or `ℚ`.
The case `p = 4`, which would create an additional zero case at `n = 3`, is
excluded by the genuine primality hypothesis in the sign classification.
-/

namespace KltDP.Examples.FrobeniusArithmetic

/-- The integer numerator `d = 2 - (p - 2)(n - 2)`, with no truncated subtraction. -/
def integerNumerator (p n : ℕ) : ℤ :=
  2 - ((p : ℤ) - 2) * ((n : ℤ) - 2)

/-- The same numerator in the rational coefficient field. -/
def numerator (p n : ℕ) : ℚ :=
  2 - ((p : ℚ) - 2) * ((n : ℚ) - 2)

/-- The numerical self-intersection assigned to `M` in the manuscript. -/
def denominator (p n : ℕ) : ℚ := (p : ℚ) * ((n : ℚ) - 2)

/-- The numerical scalar `t = d / (p(n - 2))`. -/
def canonicalScale (p n : ℕ) : ℚ := numerator p n / denominator p n

/-- The numerical expression for the canonical square. -/
def canonicalSquare (p n : ℕ) : ℚ := (numerator p n) ^ 2 / denominator p n

/-- The rational coefficient of the isolated graph component. -/
def graphCoefficient (p n : ℕ) : ℚ := 1 - 2 / denominator p n

/-- The rational coefficient of each special strict fiber. -/
def fiberCoefficient (p : ℕ) : ℚ := 1 - 2 / (p : ℚ)

theorem three_le_iff_int (n : ℕ) : 3 ≤ n ↔ (3 : ℤ) ≤ n := by
  exact_mod_cast (Iff.rfl : 3 ≤ n ↔ 3 ≤ n)

theorem numerator_eq_intCast (p n : ℕ) :
    numerator p n = (integerNumerator p n : ℚ) := by
  simp [numerator, integerNumerator]

@[simp] theorem integerNumerator_two (n : ℕ) : integerNumerator 2 n = 2 := by
  norm_num [integerNumerator]

@[simp] theorem integerNumerator_three (n : ℕ) :
    integerNumerator 3 n = 4 - (n : ℤ) := by
  dsimp [integerNumerator]
  ring

@[simp] theorem numerator_two (n : ℕ) : numerator 2 n = 2 := by
  norm_num [numerator]

@[simp] theorem numerator_three (n : ℕ) : numerator 3 n = 4 - (n : ℚ) := by
  dsimp [numerator]
  ring

/-- The negative range needs no primality assumption once `p ≥ 5`. -/
theorem integerNumerator_neg_of_five_le {p n : ℕ} (hp : 5 ≤ p) (hn : 3 ≤ n) :
    integerNumerator p n < 0 := by
  have hpz : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hnz : (3 : ℤ) ≤ n := by exact_mod_cast hn
  have hprod : 0 ≤ ((p : ℤ) - 5) * ((n : ℤ) - 3) :=
    mul_nonneg (by omega) (by omega)
  dsimp [integerNumerator]
  nlinarith

/-- Exact positive sign classification for the integer numerator. -/
theorem integerNumerator_pos_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    0 < integerNumerator p n ↔ p = 2 ∨ p = 3 ∧ n = 3 := by
  by_cases hp2 : p = 2
  · subst p
    simp
  by_cases hp3 : p = 3
  · subst p
    rw [integerNumerator_three]
    have hnz : (3 : ℤ) ≤ n := by exact_mod_cast hn
    constructor
    · intro h
      right
      exact ⟨rfl, by omega⟩
    · rintro (h | ⟨_, rfl⟩)
      · omega
      · norm_num
  have hneg := integerNumerator_neg_of_five_le
    (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hn
  constructor
  · intro h
    omega
  · intro h
    rcases h with h | ⟨h, _⟩
    · exact (hp2 h).elim
    · exact (hp3 h).elim

/-- Exact zero sign classification; primality rules out `(p,n) = (4,3)`. -/
theorem integerNumerator_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    integerNumerator p n = 0 ↔ p = 3 ∧ n = 4 := by
  by_cases hp2 : p = 2
  · subst p
    simp
  by_cases hp3 : p = 3
  · subst p
    rw [integerNumerator_three]
    constructor
    · intro h
      exact ⟨rfl, by omega⟩
    · rintro ⟨_, rfl⟩
      norm_num
  have hneg := integerNumerator_neg_of_five_le
    (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hn
  constructor
  · intro h
    omega
  · rintro ⟨h, _⟩
    exact (hp3 h).elim

/-- The remaining prime parameters give a strictly negative numerator. -/
theorem integerNumerator_neg_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    integerNumerator p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n) := by
  have hpos := integerNumerator_pos_iff hp hn
  have hzero := integerNumerator_eq_zero_iff hp hn
  omega

theorem numerator_pos_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    0 < numerator p n ↔ p = 2 ∨ p = 3 ∧ n = 3 := by
  rw [numerator_eq_intCast]
  exact_mod_cast integerNumerator_pos_iff hp hn

theorem numerator_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    numerator p n = 0 ↔ p = 3 ∧ n = 4 := by
  rw [numerator_eq_intCast]
  exact_mod_cast integerNumerator_eq_zero_iff hp hn

theorem numerator_neg_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    numerator p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n) := by
  rw [numerator_eq_intCast]
  exact_mod_cast integerNumerator_neg_iff hp hn

theorem parameter_sub_two_pos {n : ℕ} (hn : 3 ≤ n) : 0 < (n : ℚ) - 2 := by
  have hnq : (3 : ℚ) ≤ n := by exact_mod_cast hn
  linarith

theorem parameter_sub_two_ne_zero {n : ℕ} (hn : 3 ≤ n) : (n : ℚ) - 2 ≠ 0 :=
  ne_of_gt (parameter_sub_two_pos hn)

/-- The denominator bound is valid for every `p ≥ 2`, independently of primality. -/
theorem two_le_denominator {p n : ℕ} (hp : 2 ≤ p) (hn : 3 ≤ n) :
    2 ≤ denominator p n := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hnq : (3 : ℚ) ≤ n := by exact_mod_cast hn
  dsimp [denominator]
  calc
    (2 : ℚ) = 2 * 1 := by norm_num
    _ ≤ (p : ℚ) * ((n : ℚ) - 2) :=
      mul_le_mul hpq (by linarith) (by norm_num) (by positivity)

theorem denominator_pos {p n : ℕ} (hp : 2 ≤ p) (hn : 3 ≤ n) :
    0 < denominator p n := lt_of_lt_of_le (by norm_num) (two_le_denominator hp hn)

theorem denominator_ne_zero {p n : ℕ} (hp : 2 ≤ p) (hn : 3 ≤ n) :
    denominator p n ≠ 0 := ne_of_gt (denominator_pos hp hn)

theorem canonicalScale_pos_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    0 < canonicalScale p n ↔ p = 2 ∨ p = 3 ∧ n = 3 := by
  rw [canonicalScale, div_pos_iff_of_pos_right (denominator_pos hp.two_le hn)]
  exact numerator_pos_iff hp hn

theorem canonicalScale_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    canonicalScale p n = 0 ↔ p = 3 ∧ n = 4 := by
  rw [canonicalScale, div_eq_zero_iff]
  simp only [denominator_ne_zero hp.two_le hn, or_false]
  exact numerator_eq_zero_iff hp hn

theorem canonicalScale_neg_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    canonicalScale p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n) := by
  rw [canonicalScale, div_lt_iff₀ (denominator_pos hp.two_le hn), zero_mul]
  exact numerator_neg_iff hp hn

/-- A reusable field identity behind the self-intersection calculation. -/
theorem square_div_mul {F : Type*} [Field F] (a b : F) (hb : b ≠ 0) :
    (a / b) ^ 2 * b = a ^ 2 / b := by
  field_simp [hb]
  ring

theorem canonicalSquare_eq_scale_sq_mul_denominator {p n : ℕ}
    (hp : 2 ≤ p) (hn : 3 ≤ n) :
    canonicalSquare p n = (canonicalScale p n) ^ 2 * denominator p n := by
  exact (square_div_mul (numerator p n) (denominator p n)
    (denominator_ne_zero hp hn)).symm

theorem canonicalSquare_nonneg {p n : ℕ} (hp : 2 ≤ p) (hn : 3 ≤ n) :
    0 ≤ canonicalSquare p n :=
  div_nonneg (sq_nonneg _) (le_of_lt (denominator_pos hp hn))

theorem canonicalSquare_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    canonicalSquare p n = 0 ↔ p = 3 ∧ n = 4 := by
  simp only [canonicalSquare, div_eq_zero_iff, denominator_ne_zero hp.two_le hn,
    or_false, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)]
  exact numerator_eq_zero_iff hp hn

theorem canonicalSquare_pos_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    0 < canonicalSquare p n ↔ ¬ (p = 3 ∧ n = 4) := by
  rw [canonicalSquare, div_pos_iff_of_pos_right (denominator_pos hp.two_le hn),
    sq_pos_iff, ne_eq, numerator_eq_zero_iff hp hn]

/-- Reusable coefficient estimate for any rational denominator at least two. -/
theorem one_sub_two_div_bounds {q : ℚ} (hq : 2 ≤ q) :
    0 ≤ 1 - 2 / q ∧ 1 - 2 / q < 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hle : 2 / q ≤ 1 := (div_le_one hqpos).2 hq
  have hpos : 0 < 2 / q := div_pos (by norm_num) hqpos
  constructor <;> linarith

theorem graphCoefficient_bounds {p n : ℕ} (hp : 2 ≤ p) (hn : 3 ≤ n) :
    0 ≤ graphCoefficient p n ∧ graphCoefficient p n < 1 :=
  one_sub_two_div_bounds (two_le_denominator hp hn)

theorem fiberCoefficient_bounds {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ fiberCoefficient p ∧ fiberCoefficient p < 1 := by
  apply one_sub_two_div_bounds
  exact_mod_cast hp

theorem canonicalScale_two {n : ℕ} (hn : 3 ≤ n) :
    canonicalScale 2 n = 1 / ((n : ℚ) - 2) := by
  rw [canonicalScale, numerator_two]
  dsimp [denominator]
  norm_num
  field_simp [parameter_sub_two_ne_zero hn]

theorem canonicalSquare_two {n : ℕ} (hn : 3 ≤ n) :
    canonicalSquare 2 n = 2 / ((n : ℚ) - 2) := by
  rw [canonicalSquare, numerator_two]
  dsimp [denominator]
  norm_num
  field_simp [parameter_sub_two_ne_zero hn]
  ring

theorem canonicalScale_three (n : ℕ) :
    canonicalScale 3 n = (4 - (n : ℚ)) / (3 * ((n : ℚ) - 2)) := by
  simp [canonicalScale, denominator]

theorem canonicalSquare_three (n : ℕ) :
    canonicalSquare 3 n = ((n : ℚ) - 4) ^ 2 / (3 * ((n : ℚ) - 2)) := by
  simp only [canonicalSquare, numerator_three, denominator, Nat.cast_ofNat]
  congr 1
  ring

@[simp] theorem fiberCoefficient_two : fiberCoefficient 2 = 0 := by
  norm_num [fiberCoefficient]

@[simp] theorem fiberCoefficient_three : fiberCoefficient 3 = 1 / 3 := by
  norm_num [fiberCoefficient]

theorem graphCoefficient_two {n : ℕ} (hn : 3 ≤ n) :
    graphCoefficient 2 n = 1 - 1 / ((n : ℚ) - 2) := by
  dsimp [graphCoefficient, denominator]
  norm_num
  field_simp [parameter_sub_two_ne_zero hn]

@[simp] theorem canonicalScale_two_three : canonicalScale 2 3 = 1 := by
  norm_num [canonicalScale, numerator, denominator]

@[simp] theorem canonicalSquare_two_three : canonicalSquare 2 3 = 2 := by
  norm_num [canonicalSquare, numerator, denominator]

@[simp] theorem canonicalScale_three_three : canonicalScale 3 3 = 1 / 3 := by
  norm_num [canonicalScale, numerator, denominator]

@[simp] theorem canonicalSquare_three_three : canonicalSquare 3 3 = 1 / 3 := by
  norm_num [canonicalSquare, numerator, denominator]

@[simp] theorem canonicalScale_three_four : canonicalScale 3 4 = 0 := by
  norm_num [canonicalScale, numerator, denominator]

@[simp] theorem canonicalSquare_three_four : canonicalSquare 3 4 = 0 := by
  norm_num [canonicalSquare, numerator, denominator]

end KltDP.Examples.FrobeniusArithmetic
