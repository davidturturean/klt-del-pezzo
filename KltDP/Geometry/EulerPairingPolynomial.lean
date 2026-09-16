import KltDP.Literature.NumericalIntersectionPolynomial
import KltDP.Literature.NumericalIntersectionLiterals

/-!
# The specialisation debt discharged: the symbol is the accepted four-term pairing

The E8 literal `NumericalIntersectionSurfaceLiteral` asserted that the Stacks intersection symbol
equals the accepted `picardEulerPairing`. That clause is **proved here** from the faithful literal
`NumericalIntersectionPolynomialLiteral` (Stacks 0BEM/0BEP/0BEQ/0BER in the source's own shape),
using only the pure-algebra lemma `KltDP.Support.MixedCoefficient.mixedCoeff_eq_secondDifference`:

* `symbol_eq_secondDifference`: the symbol is `χ(pq) − χ(p) − χ(q) + χ(1)` — the coefficient of `m·n`
  of a total-degree-`≤ 2` polynomial is its second difference, evaluated through `p^0 = 1`, `p^1 = p`;
* `symbol_inv_inv`: additivity forces `sym p⁻¹ q⁻¹ = sym p q`, which is exactly the **sign
  convention**: the accepted pairing is the second difference taken at the inverse classes;
* `picardEulerPairing_eq_symbol`: hence `picardEulerPairing p q = sym p q`;
* **`numericalIntersectionSurfaceLiteral_of_polynomialLiteral`**: therefore the E8 literal is a
  *consequence* of the faithful one, and every E8 consumer (`cartierEulerPairingAdditive_of_literal`,
  the agreement of the two pairings, `nullLocus_form_eq`) now rests on a literal with nothing
  implicit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry KltDP.Literature.Stacks
open KltDP.Support.MixedCoefficient

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

section Symbol

variable (sym : X.toScheme.Pic → X.toScheme.Pic → ℤ)
  (hleft : ∀ p p' q : X.toScheme.Pic, sym (p * p') q = sym p q + sym p' q)
  (hright : ∀ p q q' : X.toScheme.Pic, sym p (q * q') = sym p q + sym p q')

include hleft in
theorem symbol_one_left (q : X.toScheme.Pic) : sym 1 q = 0 := by
  have h := hleft 1 1 q
  rw [one_mul] at h
  omega

include hleft in
theorem symbol_inv_left (p q : X.toScheme.Pic) : sym p⁻¹ q = -sym p q := by
  have h := hleft p p⁻¹ q
  rw [mul_inv_cancel, symbol_one_left X sym hleft q] at h
  omega

include hright in
theorem symbol_one_right (p : X.toScheme.Pic) : sym p 1 = 0 := by
  have h := hright p 1 1
  rw [one_mul] at h
  omega

include hright in
theorem symbol_inv_right (p q : X.toScheme.Pic) : sym p q⁻¹ = -sym p q := by
  have h := hright p q q⁻¹
  rw [mul_inv_cancel, symbol_one_right X sym hright p] at h
  omega

include hleft hright in
/-- **The sign convention**: additivity forces the symbol to be invariant under inverting both
arguments, which is what lets the second difference at `(p, q)` be compared with the accepted
pairing, taken at `(p⁻¹, q⁻¹)`. -/
theorem symbol_inv_inv (p q : X.toScheme.Pic) : sym p⁻¹ q⁻¹ = sym p q := by
  rw [symbol_inv_right X sym hright, symbol_inv_left X sym hleft, neg_neg]

end Symbol

/-- **The symbol is the second difference** `χ(pq) − χ(p) − χ(q) + χ(1)`: the algebraic half of the
former specialisation debt, applied to the polynomial of Stacks 0BEM. -/
theorem symbol_eq_secondDifference (sym : X.toScheme.Pic → X.toScheme.Pic → ℤ)
    (p q : X.toScheme.Pic)
    (hpoly : ∃ a₀₀ a₁₀ a₀₁ a₂₀ a₀₂ : ℚ, ∀ m n : ℤ,
      ((picardEulerValue X.structureMorphism (p ^ m * q ^ n) : ℤ) : ℚ) =
        a₀₀ + a₁₀ * (m : ℚ) + a₀₁ * (n : ℚ) + a₂₀ * (m : ℚ) ^ 2 +
          ((sym p q : ℤ) : ℚ) * ((m : ℚ) * (n : ℚ)) + a₀₂ * (n : ℚ) ^ 2) :
    sym p q = picardEulerValue X.structureMorphism (p * q) -
        picardEulerValue X.structureMorphism p - picardEulerValue X.structureMorphism q +
      picardEulerValue X.structureMorphism 1 := by
  obtain ⟨a₀₀, a₁₀, a₀₁, a₂₀, a₀₂, hval⟩ := hpoly
  have hmixed := mixedCoeff_eq_secondDifference
    (fun m n : ℤ => ((picardEulerValue X.structureMorphism (p ^ m * q ^ n) : ℤ) : ℚ))
    a₀₀ a₁₀ a₀₁ a₂₀ ((sym p q : ℤ) : ℚ) a₀₂ hval
  rw [secondDifference_eq] at hmixed
  simp only [zpow_one, zpow_zero, one_mul, mul_one] at hmixed
  exact_mod_cast hmixed

/-- **The accepted four-term pairing is the Stacks symbol** (former specialisation debt, discharged:
the second difference sits at `(p⁻¹, q⁻¹)`, and additivity identifies it with the value at `(p, q)`). -/
theorem picardEulerPairing_eq_symbol (sym : X.toScheme.Pic → X.toScheme.Pic → ℤ)
    (hleft : ∀ p p' q : X.toScheme.Pic, sym (p * p') q = sym p q + sym p' q)
    (hright : ∀ p q q' : X.toScheme.Pic, sym p (q * q') = sym p q + sym p q')
    (hpoly : ∀ p q : X.toScheme.Pic, ∃ a₀₀ a₁₀ a₀₁ a₂₀ a₀₂ : ℚ, ∀ m n : ℤ,
      ((picardEulerValue X.structureMorphism (p ^ m * q ^ n) : ℤ) : ℚ) =
        a₀₀ + a₁₀ * (m : ℚ) + a₀₁ * (n : ℚ) + a₂₀ * (m : ℚ) ^ 2 +
          ((sym p q : ℤ) : ℚ) * ((m : ℚ) * (n : ℚ)) + a₀₂ * (n : ℚ) ^ 2)
    (p q : X.toScheme.Pic) : X.picardEulerPairing p q = sym p q := by
  have hinv := X.symbol_eq_secondDifference sym p⁻¹ q⁻¹ (hpoly p⁻¹ q⁻¹)
  rw [symbol_inv_inv X sym hleft hright p q] at hinv
  rw [picardEulerPairing, hinv]
  ring

/-- **The E8 literal is a consequence of the faithful one**: the specialisation debt is gone. -/
theorem numericalIntersectionSurfaceLiteral_of_polynomialLiteral
    (hL : NumericalIntersectionPolynomialLiteral k) :
    NumericalIntersectionSurfaceLiteral k := by
  refine ⟨fun X => ?_⟩
  obtain ⟨sym, hleft, hright, hpoly⟩ := hL.exists_symbol X
  exact ⟨sym, hleft, hright, fun p q =>
    (X.picardEulerPairing_eq_symbol sym hleft hright hpoly p q).symm⟩

end KltDP.Geometry.NormalProjectiveSurface
