import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Support.MixedCoefficientSecondDifference

/-!
# The numerical-intersection literal in its faithful form (Stacks 33.45, nothing implicit)

`KltDP.Literature.Stacks.NumericalIntersectionSurfaceLiteral` (E8) carried one specialisation debt:
its last clause identified the intersection symbol with the accepted four-term expression
`picardEulerPairing`, which is *not* literally Definition 33.45.3. This module states the literal in
the shape the source actually has, so that **nothing is implicit**:

* the intersection number is the **coefficient of `n₁n₂`** in the function
  `(n₁, n₂) ↦ χ(X, L₁^{⊗n₁} ⊗ L₂^{⊗n₂})` (Stacks 0BEP, Definition 33.45.3), which by 0BEM
  (Lemma 33.45.1) agrees on all of `ℤ²` with a polynomial of total degree at most `dim X = 2`
  — with **rational** coefficients, since numerical polynomials are integer-valued rather than
  integer-coefficient;
* it is an **integer** (0BEQ, Lemma 33.45.4) — here, the symbol is `ℤ`-valued by construction;
* it is **additive in each argument** (0BER, Lemma 33.45.5), written multiplicatively in `Pic`
  because `L' ⊗ L''` is the product of classes.

The identification with `picardEulerPairing` is then *proved*, not assumed, in
`KltDP/Geometry/EulerPairingPolynomial.lean`: the algebraic half is
`KltDP.Support.MixedCoefficient.mixedCoeff_eq_secondDifference`, and the sign convention (the
accepted pairing uses `p⁻¹`, `q⁻¹`, whereas the second difference sits at `p`, `q`) is handled by
the additivity clause, since additivity forces `sym p⁻¹ q⁻¹ = sym p q`.

Hypotheses of Section 33.45 against the accepted class, unchanged from the E8 dossier: `k` a field,
`X` proper over `k` (accepted `IsProjectiveOverField.isProper`), `Z = X` a closed subscheme of
dimension `d = 2` (`dimension_two`, with `i_*O_Z = O_X`). **No smoothness, Cohen–Macaulay or
Gorenstein hypothesis anywhere** — unlike the duality tags 0FVV/0FVZ, which are not Riemann–Roch and
are not encoded (see `laneE/F10_LITERALS.md`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Literature.Stacks

variable (k : Type u) [Field k]

/-- **Stacks Section 33.45 at `d = 2`, `Z = X`, in the source's own shape.** For every normal
projective surface there is an integer-valued intersection symbol on pairs of Picard classes which is
additive in each argument (0BER) and which occurs as the coefficient of `m·n` in a total-degree-`≤ 2`
polynomial with rational coefficients agreeing with `(m, n) ↦ χ(X, p^m ⊗ q^n)` on all of `ℤ²`
(0BEP through 0BEM); its integrality is 0BEQ. -/
structure NumericalIntersectionPolynomialLiteral : Prop where
  exists_symbol : ∀ X : NormalProjectiveSurface k,
    ∃ sym : X.toScheme.Pic → X.toScheme.Pic → ℤ,
      (∀ p p' q : X.toScheme.Pic, sym (p * p') q = sym p q + sym p' q) ∧
      (∀ p q q' : X.toScheme.Pic, sym p (q * q') = sym p q + sym p q') ∧
      (∀ p q : X.toScheme.Pic, ∃ a₀₀ a₁₀ a₀₁ a₂₀ a₀₂ : ℚ, ∀ m n : ℤ,
        ((picardEulerValue X.structureMorphism (p ^ m * q ^ n) : ℤ) : ℚ) =
          a₀₀ + a₁₀ * (m : ℚ) + a₀₁ * (n : ℚ) + a₂₀ * (m : ℚ) ^ 2 +
            ((sym p q : ℤ) : ℚ) * ((m : ℚ) * (n : ℚ)) + a₀₂ * (n : ℚ) ^ 2)

end KltDP.Literature.Stacks
