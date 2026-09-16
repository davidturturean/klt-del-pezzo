import KltDP.Geometry.Positivity
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.CharP.Defs

/-!
# Literals for the contraction direction: Stein factorization and Keel's Theorem 0.2 (F12)

`Prop`-valued structures used only as hypotheses; nothing is assumed here. Texts, tags/locators and
fetch dates are recorded in `laneE/F10_LITERALS.md`.

* `SteinFactorizationLiteral` — Stacks 03H0 (Theorem 37.53.4, "Stein factorization; Noetherian
  case"), fetched 2026-09-12. Encoded **weaker** than the source, because the pinned Mathlib has no
  geometric connectedness and no comparison `f'_*O_X = O_{S'}`: the encoded clauses are the
  factorization `f = f' ≫ π`, properness of `f'`, topological connectedness of the fibres of `f'`,
  and finiteness of `π`. Clauses (3), (4), (5) of the source and the "geometrically" in (1) are
  **not** encoded; since this is a hypothesis, the weaker form is implied by the source.
* `KeelSemiampleLiteral` — Keel, Theorem 0.2 (Annals of Mathematics 149 (1999), 253–286, page 254;
  read from the author's arXiv copy math/9901149, page 2). **Not a Stacks source**: every literal
  admitted so far in this project comes from the Stacks project, so admitting a journal article is a
  new policy question and is deliberately left unsettled — this is a hypothesis, and the planning
  entry `LIT_KEEL_02` in `planning/LITERATURE_AXIOMS.json` records
  `approved_as_lean_axiom_now: false` with an explicit admission gate.

  Source text (Keel, page 254): "**0.2 Theorem.** Let `L` be a nef line bundle on a scheme `X`,
  projective over a field of positive characteristic. `L` is semi-ample if and only if `L|_{E(L)}`
  is semi-ample." with "**0.1 Definition.** Let `L` be a nef line bundle on a scheme `X` proper over
  a field `k`. An irreducible subvariety `Z ⊂ X` is called *exceptional* for `L` if `L|_Z` is not
  big, i.e. if `L^{dim Z} · Z = 0`. If `L` is nef the *exceptional locus* of `L`, denoted by `E(L)`,
  is the closure, with reduced structure, of the union of all exceptional subvarieties."

  Encoding: `X` is a scheme with a projective structure morphism over `k` (accepted
  `IsProjectiveOverField`), positive characteristic is `[CharP k p]` with `0 < p`, `E(L)` is
  `KltDP.Geometry.Positivity.nullLocus` with its reduced structure, and `L|_{E(L)}` is
  `nullLocusRestrict`. Specialisation debt: Keel's "not big" is `L^{dim Z} · Z = 0`
  (Definition-Lemma 0.0), while `IsBig` here is the growth of `h⁰`; their equivalence for nef
  bundles on reduced projective schemes is Definition-Lemma 0.0 and is **not** proved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry KltDP.Geometry.Positivity

universe u

namespace KltDP.Literature.Stacks

/-- Stacks 03H0, Theorem 37.53.4 (Stein factorization; Noetherian case): "Let `S` be a locally
Noetherian scheme. Let `f : X → S` be a proper morphism. There exists a factorization `X → S' → S`
with the following properties: (1) the morphism `f'` is proper with geometrically connected fibres,
(2) the morphism `π : S' → S` is finite, (3) we have `f'_*O_X = O_{S'}`, (4) we have
`S' = Spec_S(f_*O_X)`, and (5) `S'` is the normalization of `S` in `X`." Encoded with clauses (1)
(properness, and connectedness of the fibres as topological spaces — the pinned Mathlib has no
geometric connectedness) and (2); (3), (4), (5) are not encoded. -/
structure SteinFactorizationLiteral : Prop where
  factor : ∀ (S X : Scheme.{u}) [IsLocallyNoetherian S] (f : X ⟶ S), IsProper f →
    ∃ (S' : Scheme.{u}) (f' : X ⟶ S') (π : S' ⟶ S), f = f' ≫ π ∧ IsProper f' ∧
      (∀ s : S', ConnectedSpace ↥(f'.base ⁻¹' {s})) ∧ IsFinite π

end KltDP.Literature.Stacks

namespace KltDP.Literature.Keel

variable (k : Type u) [Field k] (p : ℕ) [CharP k p]

/-- **Keel, Theorem 0.2** (Annals 149 (1999), page 254): "Let `L` be a nef line bundle on a scheme
`X`, projective over a field of positive characteristic. `L` is semi-ample if and only if
`L|_{E(L)}` is semi-ample", with `E(L)` as in Keel's Definition 0.1 (the closure, with reduced
structure, of the union of the exceptional subvarieties — the subvarieties on which `L` is not big).
Not a Stacks source: admission is an open policy question, and this structure is only ever a
hypothesis. -/
structure SemiampleLiteral : Prop where
  semiample_iff : 0 < p → ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)),
    IsProjectiveOverField f → ∀ L : InvertibleSheaf X, IsNef f L →
      (IsSemiample L ↔ IsSemiample (nullLocusRestrict f L))

end KltDP.Literature.Keel
