import KltDP.Manuscript.Datum.AnticanonicalClass

/-!
# The single exterior adjoint configuration (conclusion of Theorem 7.1)

Manuscript `source/manuscript.tex` lines 2324–2359, Theorem 7.1 (`thm:adjoint-reduction`):
for a minimal counterexample with shortest exterior `(-1)`-curve `P`, `ℓ = L·P`, `v = L²`,
there are exceptional curves `C, B₁, B₂` and a further exterior `(-1)`-curve `R'` with
`C² = -2`, `(-B₁², -B₂²) = (3, β)`, `β ∈ {3,4,5}`, `P·C = P·B₁ = P·B₂ = 1` and no other
contact of `P`; `C, B₁, B₂` pairwise disjoint, `B₁, B₂` in different exceptional components,
valency of `C` at most one; `R' ~ K_S + C + B₁ + B₂ + 2P`, `R'` disjoint from
`C ∪ B₁ ∪ B₂ ∪ P`, and `L·R' = 2ℓ - v ∈ [ℓ, 2ℓ)`.

`AdjointConfiguration` records exactly these clauses as a `Prop`. It is a *conclusion*
of Theorem 7.1 and a *hypothesis* of Theorem 8.3 (`thm:forest-exclusion`); the main theorem
assumes neither. Linear equivalence is taken in the actual Picard group of `S`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The intersection number `P · D_i` of a prime curve with an exceptional curve. -/
abbrev ResolutionDatum.contact (R : ResolutionDatum k) (P : R.S.PrimeCurve) (i : R.Vertices) : ℤ :=
  P.intersectionNumber (R.S.primeCurveCartier R.hreg i.val)

/-- `P` is an exterior `(-1)`-curve of the datum. -/
def ResolutionDatum.IsExteriorMinusOne (R : ResolutionDatum k) (P : R.S.PrimeCurve) : Prop :=
  IsMinusOneCurve R.hreg P ∧ ¬ IsExceptionalCurve R.π P

/-- `P` is a *shortest* exterior `(-1)`-curve: `ℓ = L·P` is the least `L`-degree among exterior
`(-1)`-curves. -/
def ResolutionDatum.IsShortestExteriorMinusOne (R : ResolutionDatum k) (P : R.S.PrimeCurve) : Prop :=
  R.IsExteriorMinusOne P ∧ ∀ Q : R.S.PrimeCurve, R.IsExteriorMinusOne Q → R.Ldeg P ≤ R.Ldeg Q

/-- The Picard class of the Cartier divisor of a prime curve. -/
abbrev ResolutionDatum.curvePic (R : ResolutionDatum k) (C : R.S.PrimeCurve) : R.S.toScheme.Pic :=
  cartierPicardClass R.S.toScheme (R.S.primeCurveCartier R.hreg C)

/-- The conclusion of Theorem 7.1 for a shortest exterior `(-1)`-curve `P`. -/
structure AdjointConfiguration (R : ResolutionDatum k) (P : R.S.PrimeCurve) : Prop where
  /-- The three exceptional contacts, the extra curve `R'` and the weight `β`. -/
  exists_data : ∃ (C B₁ B₂ : R.Vertices) (β : ℕ) (R' : R.S.PrimeCurve),
    (β = 3 ∨ β = 4 ∨ β = 5) ∧
    R.w C = 2 ∧ R.w B₁ = 3 ∧ R.w B₂ = β ∧
    R.contact P C = 1 ∧ R.contact P B₁ = 1 ∧ R.contact P B₂ = 1 ∧
    (∀ i : R.Vertices, i ≠ C → i ≠ B₁ → i ≠ B₂ → R.contact P i = 0) ∧
    C ≠ B₁ ∧ C ≠ B₂ ∧ B₁ ≠ B₂ ∧
    ¬ R.graph.Adj C B₁ ∧ ¬ R.graph.Adj C B₂ ∧ ¬ R.graph.Adj B₁ B₂ ∧
    ¬ R.graph.Reachable B₁ B₂ ∧
    (∀ i j : R.Vertices, R.graph.Adj C i → R.graph.Adj C j → i = j) ∧
    R.IsExteriorMinusOne R' ∧
    R.curvePic R' = cartierPicardClass R.S.toScheme R.KS * R.curvePic C.val * R.curvePic B₁.val *
      R.curvePic B₂.val * R.curvePic P ^ 2 ∧
    Disjoint (R' : Set R.S.toScheme) (C.val : Set R.S.toScheme) ∧
    Disjoint (R' : Set R.S.toScheme) (B₁.val : Set R.S.toScheme) ∧
    Disjoint (R' : Set R.S.toScheme) (B₂.val : Set R.S.toScheme) ∧
    Disjoint (R' : Set R.S.toScheme) (P : Set R.S.toScheme) ∧
    R.Ldeg R' = 2 * R.Ldeg P - R.Lsq ∧
    0 < R.Lsq ∧ R.Lsq ≤ R.Ldeg P ∧
    (∀ i : R.Vertices, i ≠ C → i ≠ B₁ → i ≠ B₂ →
      R.contact R' i = (R.w i - 2) + (R.contact C.val i + R.contact B₁.val i + R.contact B₂.val i)) ∧
    (∃ i : R.Vertices, R.graph.Adj C i ∨ R.graph.Adj B₁ i ∨ R.graph.Adj B₂ i)

end KltDP.Manuscript
