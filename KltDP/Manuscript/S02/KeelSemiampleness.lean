import KltDP.Literature.KeelLiterals

/-!
# Manuscript Theorem 2.3 (`thm:keel`): Keel's semi-ampleness criterion

Source: `source/manuscript.tex`, lines 381–383, label `thm:keel`, printed number 2.3
(`planning/THEOREM_MAP.json`, target declaration `KltDP.Manuscript.S02.keelSemiampleness`):

"**Theorem** (Keel, Theorem 0.2). Let `M` be a nef line bundle on a scheme projective over a field
of positive characteristic. Let `E(M)` be the reduced union of the positive-dimensional
subvarieties on which `M` is not big. Then `M` is semiample if and only if `M|_{E(M)}` is
semiample."

The manuscript's own scope is preserved (arbitrary field of positive characteristic, arbitrary
projective scheme, no algebraically closed / smooth / integral / surface hypothesis), as required by
the plan entry. The statement is conditional on the hypothesis
`KltDP.Literature.Keel.SemiampleLiteral`, which encodes Keel's Theorem 0.2 itself; **nothing is
admitted**: the planning entry `LIT_KEEL_02` has `approved_as_lean_axiom_now: false`, and a
non-Stacks literature source has never been admitted in this project.

`E(M)` is `KltDP.Geometry.Positivity.nullLocus` — Keel's Definition 0.1, the closure with reduced
structure of the union of the subvarieties on which `M` is not big — and `M|_{E(M)}` is
`nullLocusRestrict`. The definitions of nef, big and semi-ample are those of
`KltDP/Geometry/Positivity.lean`; their comparison with Keel's intersection-theoretic form
(`L^{dim Z} · Z = 0`, Definition-Lemma 0.0) is an open debt recorded in `laneE/F12_KEEL_PLAN.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Geometry KltDP.Geometry.Positivity

universe u

namespace KltDP.Manuscript.S02

/-- **Manuscript Theorem 2.3 (`thm:keel`)**, conditional on Keel's Theorem 0.2 as a hypothesis:
a nef line bundle on a scheme projective over a field of positive characteristic is semi-ample if
and only if its restriction to the exceptional locus `E(M)` is semi-ample. -/
theorem keelSemiampleness {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hKeel : KltDP.Literature.Keel.SemiampleLiteral.{u} k p) (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (hproj : IsProjectiveOverField f)
    (M : InvertibleSheaf X) (hnef : IsNef f M) :
    IsSemiample M ↔ IsSemiample (nullLocusRestrict f M) :=
  hKeel.semiample_iff hp X f hproj M hnef

end KltDP.Manuscript.S02
