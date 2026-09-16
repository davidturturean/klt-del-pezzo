import KltDP.Examples.FrobeniusArithmetic
import Mathlib.Algebra.CharP.Lemmas

/-!
# Support obligation U-FROBENIUS-SIGN: all canonical-sign cases of the general family

Manuscript `source/manuscript.tex` lines 2985–2995 (Proposition 10.1 and the
sentence "In particular `-K_{X_{p,n}}` is ample exactly for `p = 2` or
`(p,n) = (3,3)`; `K_{X_{3,4}} ~_Q 0`; and `K_{X_{p,n}}` is ample in all other
cases with prime `p` and `n ≥ 3`"). The numerical content is the exact sign
classification of `d_{p,n} = 2 - (p-2)(n-2)` and of the scalar
`t_{p,n} = d_{p,n} / (p(n-2))` for prime `p` and `n ≥ 3`, with subtraction
performed after casting to `ℤ` or `ℚ` (no truncated natural subtraction).

This module packages the existing accepted arithmetic of
`KltDP.Examples.FrobeniusArithmetic` into the single support declaration
`u_frobenius_sign`, adds the exhaustive and exclusive trichotomy, and proves
that the primality hypothesis is supplied by the characteristic of any field
of positive characteristic `p` (so `p = 4` can never create a spurious zero
case). It proves nothing about surfaces: the identification of `t_{p,n}` with
the actual canonical scalar of the contracted surface `X_{p,n}`, ampleness,
Q-triviality and the descent of `K` are the geometric obligations F04 and F30,
which remain open.
-/

namespace KltDP.Support

open KltDP.Examples.FrobeniusArithmetic

/-- Positive case of the numerator sign: exactly `p = 2` or `(p, n) = (3, 3)`. -/
theorem frobeniusSign_pos_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    0 < integerNumerator p n ↔ p = 2 ∨ p = 3 ∧ n = 3 :=
  integerNumerator_pos_iff hp hn

/-- Zero case of the numerator sign: exactly `(p, n) = (3, 4)`. -/
theorem frobeniusSign_eq_zero_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    integerNumerator p n = 0 ↔ p = 3 ∧ n = 4 :=
  integerNumerator_eq_zero_iff hp hn

/-- Negative case of the numerator sign: every remaining prime parameter pair. -/
theorem frobeniusSign_neg_iff {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    integerNumerator p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n) :=
  integerNumerator_neg_iff hp hn

/-- The three sign cases are exhaustive and pairwise exclusive. -/
theorem frobeniusSign_trichotomy {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    ((p = 2 ∨ p = 3 ∧ n = 3) ∧ ¬ (p = 3 ∧ n = 4) ∧ ¬ (p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n))) ∨
    (¬ (p = 2 ∨ p = 3 ∧ n = 3) ∧ (p = 3 ∧ n = 4) ∧ ¬ (p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n))) ∨
    (¬ (p = 2 ∨ p = 3 ∧ n = 3) ∧ ¬ (p = 3 ∧ n = 4) ∧ (p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n))) := by
  rw [← frobeniusSign_pos_iff hp hn, ← frobeniusSign_eq_zero_iff hp hn,
    ← frobeniusSign_neg_iff hp hn]
  rcases lt_trichotomy (integerNumerator p n) 0 with h | h | h
  · exact Or.inr (Or.inr ⟨by omega, by omega, h⟩)
  · exact Or.inr (Or.inl ⟨by omega, h, by omega⟩)
  · exact Or.inl ⟨h, by omega, by omega⟩

/-- The rational scalar `t_{p,n} = d_{p,n} / (p (n - 2))` has the sign of the
integer numerator, because the denominator is positive for every `p ≥ 2`. -/
theorem canonicalScale_sign_eq {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    (0 < canonicalScale p n ↔ 0 < integerNumerator p n) ∧
    (canonicalScale p n = 0 ↔ integerNumerator p n = 0) ∧
    (canonicalScale p n < 0 ↔ integerNumerator p n < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [canonicalScale_pos_iff hp hn, integerNumerator_pos_iff hp hn]
  · rw [canonicalScale_eq_zero_iff hp hn, integerNumerator_eq_zero_iff hp hn]
  · rw [canonicalScale_neg_iff hp hn, integerNumerator_neg_iff hp hn]

/-- **U-FROBENIUS-SIGN**, arithmetic clause. For prime `p` and `n ≥ 3` the integer
`d = 2 - (p - 2)(n - 2)` is positive exactly for `p = 2` or `(p, n) = (3, 3)`,
zero exactly for `(p, n) = (3, 4)`, and negative otherwise, and the scalar
`t = d / (p (n - 2))` has the same sign. -/
theorem u_frobenius_sign {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) :
    (0 < integerNumerator p n ↔ p = 2 ∨ p = 3 ∧ n = 3) ∧
    (integerNumerator p n = 0 ↔ p = 3 ∧ n = 4) ∧
    (integerNumerator p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n)) ∧
    (0 < canonicalScale p n ↔ p = 2 ∨ p = 3 ∧ n = 3) ∧
    (canonicalScale p n = 0 ↔ p = 3 ∧ n = 4) ∧
    (canonicalScale p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n)) :=
  ⟨integerNumerator_pos_iff hp hn, integerNumerator_eq_zero_iff hp hn,
    integerNumerator_neg_iff hp hn, canonicalScale_pos_iff hp hn,
    canonicalScale_eq_zero_iff hp hn, canonicalScale_neg_iff hp hn⟩

/-- The primality hypothesis is not an extra assumption: the characteristic of
a field of positive characteristic is prime. -/
theorem charP_prime_of_ne_zero (k : Type*) [Field k] (p : ℕ) [CharP k p] (hp : p ≠ 0) :
    p.Prime :=
  CharP.char_prime_of_ne_zero k hp

/-- **U-FROBENIUS-SIGN** stated for an arbitrary field of positive characteristic `p`,
with primality derived from the characteristic rather than assumed. -/
theorem u_frobenius_sign_of_charP (k : Type*) [Field k] (p : ℕ) [CharP k p]
    (hp : p ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    (0 < integerNumerator p n ↔ p = 2 ∨ p = 3 ∧ n = 3) ∧
    (integerNumerator p n = 0 ↔ p = 3 ∧ n = 4) ∧
    (integerNumerator p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n)) ∧
    (0 < canonicalScale p n ↔ p = 2 ∨ p = 3 ∧ n = 3) ∧
    (canonicalScale p n = 0 ↔ p = 3 ∧ n = 4) ∧
    (canonicalScale p n < 0 ↔ p ≠ 2 ∧ (p ≠ 3 ∨ 5 ≤ n)) :=
  u_frobenius_sign (charP_prime_of_ne_zero k p hp) hn

/-- The numerator is literally `2 - (p - 2)(n - 2)` computed in `ℤ`. -/
theorem integerNumerator_def (p n : ℕ) :
    integerNumerator p n = 2 - ((p : ℤ) - 2) * ((n : ℤ) - 2) := rfl

/-- The four displayed instances of the manuscript sentence. -/
theorem frobeniusSign_examples :
    0 < integerNumerator 2 7 ∧ 0 < integerNumerator 3 3 ∧
    integerNumerator 3 4 = 0 ∧ integerNumerator 5 3 < 0 ∧ integerNumerator 3 5 < 0 := by
  simp only [integerNumerator_def]
  norm_num

end KltDP.Support
