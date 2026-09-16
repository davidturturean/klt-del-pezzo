import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
# Support obligation U-SQUARE-ONE-TYPES: the three square-one input configurations

Manuscript `source/manuscript.tex` lines 1551–1567 (§6, "Configurations with a
nef divisor of square one"): the three configurations
`(U1) A = W + P` with `W² = -2, P² = -1, W·P = 2`,
`(U2) A = U + V + P` with `U² = V² = -2, P² = -1, U·V = U·P = V·P = 1`,
`(U3) A = B + 2P` with `B² = -3, P² = -1, B·P = 2`,
where every displayed curve is smooth rational, `P` is exterior and the other
components belong to `D`.

This module records each configuration as an explicit symmetric integer
intersection matrix on the displayed curves together with the coefficient
vector of `A`, and proves the numerical consequences used by §6:
`A² = 1`, `K·A = -1` (using the adjunction values `K·C = -2 - C²` of smooth
rational curves as the canonical-degree vector), and the degree vector of `A`
on the displayed curves, namely `(A·W, A·P) = (0, 1)`, `(A·U, A·V, A·P) = (0, 0, 1)`
and `(A·B, A·P) = (1, 0)`; in particular `A` is nonnegative on every displayed
curve.

Nefness of `A` on the whole surface, the actual curves, the distinctness of the
three intersection points in (U2), and the adjunction identities themselves are
geometric obligations (F03, F04, F17) and are not proved here.
-/

namespace KltDP.Support

open Matrix

/-- Canonical degrees of smooth rational curves from their self-intersections:
`K·C = -2 - C²`. -/
def rationalCanonicalDegree {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) : Fin n → ℤ :=
  fun i => -2 - G i i

/-- (U1): intersection matrix of `(W, P)`. -/
def gramU1 : Matrix (Fin 2) (Fin 2) ℤ := !![-2, 2; 2, -1]
/-- (U1): `A = W + P`. -/
def coeffU1 : Fin 2 → ℤ := ![1, 1]

/-- (U2): intersection matrix of `(U, V, P)`. -/
def gramU2 : Matrix (Fin 3) (Fin 3) ℤ := !![-2, 1, 1; 1, -2, 1; 1, 1, -1]
/-- (U2): `A = U + V + P`. -/
def coeffU2 : Fin 3 → ℤ := ![1, 1, 1]

/-- (U3): intersection matrix of `(B, P)`. -/
def gramU3 : Matrix (Fin 2) (Fin 2) ℤ := !![-3, 2; 2, -1]
/-- (U3): `A = B + 2P`. -/
def coeffU3 : Fin 2 → ℤ := ![1, 2]

theorem gramU1_isSymm : gramU1.IsSymm := by decide
theorem gramU2_isSymm : gramU2.IsSymm := by decide
theorem gramU3_isSymm : gramU3.IsSymm := by decide

/-- (U1): `A² = 1`, `K·A = -1`, `(A·W, A·P) = (0, 1)`. -/
theorem squareOne_U1 :
    coeffU1 ⬝ᵥ (gramU1 *ᵥ coeffU1) = 1 ∧
    rationalCanonicalDegree gramU1 ⬝ᵥ coeffU1 = -1 ∧
    gramU1 *ᵥ coeffU1 = ![0, 1] := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- (U2): `A² = 1`, `K·A = -1`, `(A·U, A·V, A·P) = (0, 0, 1)`. -/
theorem squareOne_U2 :
    coeffU2 ⬝ᵥ (gramU2 *ᵥ coeffU2) = 1 ∧
    rationalCanonicalDegree gramU2 ⬝ᵥ coeffU2 = -1 ∧
    gramU2 *ᵥ coeffU2 = ![0, 0, 1] := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- (U3): `A² = 1`, `K·A = -1`, `(A·B, A·P) = (1, 0)`. -/
theorem squareOne_U3 :
    coeffU3 ⬝ᵥ (gramU3 *ᵥ coeffU3) = 1 ∧
    rationalCanonicalDegree gramU3 ⬝ᵥ coeffU3 = -1 ∧
    gramU3 *ᵥ coeffU3 = ![1, 0] := by
  refine ⟨by decide, by decide, ?_⟩
  decide

/-- The displayed self-intersections and canonical degrees: `P` is a `(-1)`-curve
with `K·P = -1`, the `(-2)`-curves have `K = 0`, and `B` has `K·B = 1`. -/
theorem displayed_canonical_degrees :
    rationalCanonicalDegree gramU1 = ![0, -1] ∧
    rationalCanonicalDegree gramU2 = ![0, 0, -1] ∧
    rationalCanonicalDegree gramU3 = ![1, -1] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `A` is nonnegative on every displayed curve in all three configurations. -/
theorem displayed_degrees_nonneg :
    (∀ i, 0 ≤ (gramU1 *ᵥ coeffU1) i) ∧ (∀ i, 0 ≤ (gramU2 *ᵥ coeffU2) i) ∧
    (∀ i, 0 ≤ (gramU3 *ᵥ coeffU3) i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **U-SQUARE-ONE-TYPES**, numerical clause: the three configurations have
`A² = 1`, `K·A = -1` and the displayed degree vectors. -/
theorem u_square_one_types :
    (coeffU1 ⬝ᵥ (gramU1 *ᵥ coeffU1) = 1 ∧ rationalCanonicalDegree gramU1 ⬝ᵥ coeffU1 = -1 ∧
      gramU1 *ᵥ coeffU1 = ![0, 1]) ∧
    (coeffU2 ⬝ᵥ (gramU2 *ᵥ coeffU2) = 1 ∧ rationalCanonicalDegree gramU2 ⬝ᵥ coeffU2 = -1 ∧
      gramU2 *ᵥ coeffU2 = ![0, 0, 1]) ∧
    (coeffU3 ⬝ᵥ (gramU3 *ᵥ coeffU3) = 1 ∧ rationalCanonicalDegree gramU3 ⬝ᵥ coeffU3 = -1 ∧
      gramU3 *ᵥ coeffU3 = ![1, 0]) :=
  ⟨squareOne_U1, squareOne_U2, squareOne_U3⟩

end KltDP.Support
