/-
Copyright (c) 2026 KltDelPezzoLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The imported variable-interchange API is the bounded compatibility port of
Mathlib/Algebra/Polynomial/Bivariate.lean, official commit
59e84018b299993f5d4ca6d8cb4012b08bc55241 (Copyright 2024 Junyan Xu).
The coefficient identity and degree bound below are new ordinary proofs,
not declarations copied from that upstream section.
-/
import KltDP.Compatibility.BivariateSwap
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Coefficients and degree under bivariate variable interchange

Swapping the two variables transposes the coefficient indices. Consequently,
each original coefficient polynomial has degree at most the outer degree of
the swapped polynomial, without a nonzero or linear independence hypothesis.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace KltDP.Compatibility.BivariateSwapCoefficients

variable {R : Type*} [CommSemiring R]

/-- Interchanging the variables interchanges the two coefficient indices. -/
theorem coeff_coeff_swap (p : R[X][Y]) (i j : ℕ) :
    ((Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [_root_.map_add, coeff_add, hp, hq]
  | monomial n f =>
      rw [Bivariate.swap_monomial, coeff_mul_C, coeff_map, coeff_C_mul_X_pow]
      by_cases h : n = j
      · subst j
        simp
      · simp [coeff_monomial, h, Ne.symm h]

/-- The degree in the original inner variable is bounded by the outer degree
after interchange, for every individual coefficient polynomial. -/
theorem natDegree_coeff_le_natDegree_swap (p : R[X][Y]) (i : ℕ) :
    (p.coeff i).natDegree ≤ (Bivariate.swap p).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← coeff_coeff_swap p j i, coeff_eq_zero_of_natDegree_lt hj, coeff_zero]

end KltDP.Compatibility.BivariateSwapCoefficients

#print axioms KltDP.Compatibility.BivariateSwapCoefficients.coeff_coeff_swap
#print axioms KltDP.Compatibility.BivariateSwapCoefficients.natDegree_coeff_le_natDegree_swap
