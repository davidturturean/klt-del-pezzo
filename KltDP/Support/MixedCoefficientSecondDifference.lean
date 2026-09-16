import Mathlib.Tactic

/-!
# The mixed coefficient of a two-variable polynomial of total degree at most two

Pure algebra, no geometry. For a function `f : ℤ → ℤ → R` into a commutative ring which agrees on all
of `ℤ²` with a polynomial of total degree at most two,

  `f m n = a₀₀ + a₁₀ m + a₀₁ n + a₂₀ m² + a₁₁ m n + a₀₂ n²`,

the coefficient `a₁₁` of the mixed term equals the **second difference at the origin**
`f 1 1 − f 1 0 − f 0 1 + f 0 0`.

This is the algebraic half of the single specialisation debt of the numerical-intersection literal:
Stacks Definition 33.45.3 (0BEP) takes the intersection number to be the coefficient of `n₁n₂` in the
numerical polynomial of Lemma 33.45.1 (0BEM), whereas the accepted `picardEulerPairing` is a
four-term second difference. The coefficients are allowed to be rational (numerical polynomials are
integer-valued, not integer-coefficient), which is why `R` is an arbitrary commutative ring; the
geometric application takes `R = ℚ`.
-/

namespace KltDP.Support.MixedCoefficient

variable {R : Type*} [CommRing R]

/-- The second difference of `f` at the origin, `f(1,1) − f(1,0) − f(0,1) + f(0,0)`. -/
def secondDifference (f : ℤ → ℤ → R) : R := f 1 1 - f 1 0 - f 0 1 + f 0 0

theorem secondDifference_eq (f : ℤ → ℤ → R) :
    secondDifference f = f 1 1 - f 1 0 - f 0 1 + f 0 0 := rfl

/-- **The mixed coefficient of a total-degree-`≤ 2` polynomial is its second difference.** -/
theorem mixedCoeff_eq_secondDifference (f : ℤ → ℤ → R) (a₀₀ a₁₀ a₀₁ a₂₀ a₁₁ a₀₂ : R)
    (hf : ∀ m n : ℤ, f m n =
      a₀₀ + a₁₀ * (m : R) + a₀₁ * (n : R) + a₂₀ * (m : R) ^ 2 +
        a₁₁ * ((m : R) * (n : R)) + a₀₂ * (n : R) ^ 2) :
    a₁₁ = secondDifference f := by
  simp only [secondDifference, hf]
  push_cast
  ring

end KltDP.Support.MixedCoefficient
