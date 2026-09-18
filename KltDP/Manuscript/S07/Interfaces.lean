import KltDP.Manuscript.Main.SevenPointBound

/-!
# Interfaces for the two inputs of Theorem 7.1 still being formalized

Theorem 7.1 (`thm:adjoint-reduction`) uses Theorem 7.5 (`thm:two-contact-ruling`, TeX 2236–2316)
and Theorem 4.6 (`thm:isolated-node-exchange`, TeX 1114–1219). These `Prop`s state exactly what
Theorem 7.1's proof consumes from them, so that the assembly can be written and checked while the
two theorems are being proved in parallel; the final unconditional theorem discharges them.

* `TwoContactRulingHyp R P`: for a shortest exterior `(-1)`-curve `P` and two disjoint weight-two
  exceptional curves `U, V` each meeting `P` once, if every exceptional curve has degree at most two
  against the fibre class `F = U + 2P + V`, then `X` has at most seven singular points.
* `IsolatedExchangeHyp R`: for an exterior `(-1)`-curve `P` meeting an isolated weight-two vertex
  `W` and a higher-weight vertex `B` once each and nothing else, there is a resolution datum with
  smaller Picard number and at least as many singular points.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The Cartier divisor `U + 2P + V` on `S`. -/
def ResolutionDatum.fibreDivisor (R : ResolutionDatum k) (U V : R.Vertices) (P : R.S.PrimeCurve) :
    CartierDivisor R.S.toScheme :=
  R.S.primeCurveCartier R.hreg U.val + (2 : ℤ) • R.S.primeCurveCartier R.hreg P +
    R.S.primeCurveCartier R.hreg V.val

/-- The conclusion of Theorem 7.5 in the form used by Theorem 7.1. -/
def TwoContactRulingHyp (R : ResolutionDatum k) (P : R.S.PrimeCurve) : Prop :=
  ∀ U V : R.Vertices, U ≠ V → R.w U = 2 → R.w V = 2 → ¬ R.graph.Adj U V →
    R.contact P U = 1 → R.contact P V = 1 →
    (∀ i : R.Vertices, (i.val).intersectionNumber (R.fibreDivisor U V P) ≤ 2) →
    R.X.singularPoints.card ≤ 7

/-- The conclusion of Theorem 4.6 in the form used by Theorem 7.1. -/
def IsolatedExchangeHyp (R : ResolutionDatum k) : Prop :=
  ∀ (W B : R.Vertices) (P : R.S.PrimeCurve), R.IsExteriorMinusOne P →
    R.w W = 2 → (∀ y, ¬ R.graph.Adj W y) → 3 ≤ R.w B →
    R.contact P W = 1 → R.contact P B = 1 → (∀ i, i ≠ W → i ≠ B → R.contact P i = 0) →
    ∃ R₁ : ResolutionDatum k, R₁.S.picardRank < R.S.picardRank ∧
      R.X.singularPoints.card ≤ R₁.X.singularPoints.card

end KltDP.Manuscript
