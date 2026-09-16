import KltDP.Geometry.IntersectionPairingSymmetry

/-!
# Stacks literals for numerical intersections on a surface, and the shape of surface Riemann–Roch

**Correction to the brief's premise, recorded here and in `laneE/F10_LITERALS.md`.** Stacks 0FVV
(Lemma 48.27.1) and 0FVZ (Lemma 48.27.5) are *duality* statements — existence of a dualizing complex
for a proper scheme over a field, and Serre duality for a Cohen–Macaulay equidimensional proper
scheme. Neither is Riemann–Roch, and neither implies that `D ↦ χ(O_X(−D))` is quadratic, which is
the only thing `CartierEulerPairingAdditive` needs. They are therefore **not** encoded here: a
literal must never say more than its source.

The statement that does discharge it is Stacks Section 33.45 ("Numerical intersections"), fetched
2026-09-12:

* **0BEM (Lemma 33.45.1)**: "Let `k` be a field, `X` a proper scheme over `k`, `F` a coherent
  `O_X`-module, `L_1, …, L_r` invertible `O_X`-modules. The function
  `(n_1, …, n_r) ↦ χ(X, F ⊗ L_1^{⊗n_1} ⊗ … ⊗ L_r^{⊗n_r})` is a numerical polynomial in
  `n_1, …, n_r` of total degree at most the dimension of the support of `F`."
* **0BEP (Definition 33.45.3)**: for a closed subscheme `i : Z → X` of dimension `d` and invertible
  `L_1, …, L_d`, the intersection number `(L_1 ⋯ L_d · Z)` is "the coefficient of `n_1 … n_d` in the
  numerical polynomial `χ(X, i_*O_Z ⊗ L_1^{⊗n_1} ⊗ … ⊗ L_d^{⊗n_d}) = χ(Z, (L_1^{⊗n_1} ⊗ … ⊗
  L_d^{⊗n_d})|_Z)`"; it is an integer by 0BEQ (Lemma 33.45.4).
* **0BER (Lemma 33.45.5)**: "In the situation of Definition 33.45.3, if `L_i = L_i' ⊗ L_i''` then
  `(L_1 ⋯ L_i ⋯ L_d · Z) = (L_1 ⋯ L_i' ⋯ L_d · Z) + (L_1 ⋯ L_i'' ⋯ L_d · Z)`."

`NumericalIntersectionSurfaceLiteral` encodes 0BEP + 0BER at `d = 2`, `Z = X`, for the accepted
`NormalProjectiveSurface k` (proper over `k` through the accepted `IsProjectiveOverField.isProper`;
`dim X = 2` is a field of the class, and integrality gives equidimensionality — no Cohen–Macaulay or
smoothness hypothesis is needed anywhere in Section 33.45, unlike 0FVZ).

**Specialisation debt: discharged. This structure is not an admission candidate.** The third field
identifies the symbol with the accepted four-term expression
`picardEulerPairing p q = χ(O) − χ(p⁻¹) − χ(q⁻¹) + χ(p⁻¹q⁻¹)`. This is *not* literally Definition
33.45.3: it is the statement that, for a numerical polynomial of total degree `≤ 2` in two variables
(0BEM with `F = O_X`, `dim X = 2`), the second difference at `(0, 0)` equals the coefficient of
`n_1 n_2`, under the sign convention `p⁻¹` versus `L^{⊗n}` with `n = −1`. That is elementary
polynomial algebra, and it is now formalised: `mixedCoeff_eq_secondDifference`
(`KltDP/Support/MixedCoefficientSecondDifference.lean`) is the algebra, and
`picardEulerPairing_eq_symbol` (`KltDP/Geometry/EulerPairingPolynomial.lean`) is the specialisation,
both over the faithful ℚ-coefficient literal `NumericalIntersectionPolynomialLiteral`
(`KltDP/Literature/NumericalIntersectionPolynomial.lean`).

**`NumericalIntersectionSurfaceLiteral` must therefore never be admitted as a literal.** Its third
clause equates the existentially bound symbol with `picardEulerPairing`, which is already a total
accepted function; the existential is thus eliminable and the whole structure collapses to
biadditivity of that pairing conjoined with the unformalised cohomology-model bridge — admitting it
would axiomatise the bridge rather than record 0BEP/0BER. It is kept here only as a *derived*
statement: `numericalIntersectionSurfaceLiteral_of_polynomialLiteral` proves it from the faithful
literal, so the consumers below keep their present hypothesis unchanged. The faithful form's ℚ
coefficients are necessary for truth and not merely conservative: on `ℙ²` the Euler characteristic
`χ(O(n)) = (n+1)(n+2)/2` has leading coefficient `1/2`, so an integer-coefficient encoding of 0BEM
would be a false statement.

`SurfaceRiemannRochStatement` is **stated only, never assumed and never proved**: Stacks has
Riemann–Roch for *curves* (0BS6, Lemma 53.5.2: proper, Gorenstein, equidimensional of dimension 1 —
recorded in the dossier but deliberately **not** encoded, since neither the Gorenstein hypothesis nor
the dualizing sheaf is expressible in the accepted vocabulary), and has no surface Riemann–Roch, so the F05 block must source it elsewhere — the planning entry
`planning/LITERATURE_AXIOMS.json` lists Tanaka, *Minimal model program for excellent surfaces*,
Corollary 2.9 and Theorem 2.10 (`LIT_TANAKA_29`, `LIT_TANAKA_210`) for exactly that target.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Literature.Stacks

variable (k : Type u) [Field k]

/-- **Stacks 33.45 (0BEP, 0BER, 0BEQ) at `d = 2`, `Z = X`** for a normal projective surface: there
is an integer-valued intersection symbol on pairs of invertible classes which is additive in each
argument (0BER) and is computed by the accepted four-term Euler expression (the specialisation of
0BEP through 0BEM, discharged in `KltDP/Geometry/EulerPairingPolynomial.lean`). Per the module
docstring this structure is **not** an admission candidate; it is derivable from the faithful
ℚ-coefficient literal and is retained only so its existing consumers keep compiling. -/
structure NumericalIntersectionSurfaceLiteral : Prop where
  exists_symbol : ∀ X : NormalProjectiveSurface k,
    ∃ sym : X.toScheme.Pic → X.toScheme.Pic → ℤ,
      (∀ p p' q : X.toScheme.Pic, sym (p * p') q = sym p q + sym p' q) ∧
      (∀ p q q' : X.toScheme.Pic, sym p (q * q') = sym p q + sym p q') ∧
      (∀ p q : X.toScheme.Pic, sym p q = X.picardEulerPairing p q)

end KltDP.Literature.Stacks

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- **The shape of surface Riemann–Roch in the accepted vocabulary** (doubled to stay in `ℤ`):
`2 (χ(O_X(D)) − χ(O_X)) = D·D − D·K`, with the intersection numbers taken in the unconditional
bilinear pairing of E6/E7 and `K` an explicit Cartier divisor standing for the canonical class (the
accepted tree has no canonical divisor). **Stated only**: Stacks has no surface Riemann–Roch, and
this is never assumed nor proved here — it is the F05 target, whose planning sources are Tanaka
Corollary 2.9 / Theorem 2.10. -/
def SurfaceRiemannRochStatement (K : CartierDivisor X.toScheme) : Prop :=
  ∀ D : CartierDivisor X.toScheme,
    2 * (eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme D) -
        eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)) =
      intersectionPairing X hregular D D - intersectionPairing X hregular D K

end KltDP.Geometry.NormalProjectiveSurface
