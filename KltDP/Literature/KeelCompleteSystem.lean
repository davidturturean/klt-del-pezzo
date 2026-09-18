import KltDP.Geometry.KeelExceptionalSupport
import Mathlib.Algebra.CharP.Defs

/-!
# Keel's full Theorem 0.2, using its original complete-system definition

Seán Keel, Annals of Mathematics 149 (1999), 253–286, Theorem 0.2 on
printed p.254; definitions 0.0–0.1 on pp.253–254, conventions on p.259.
DOI: 10.2307/121025. Published PDF SHA256:
4d87c752091896d480e6fdf3829f59db4c152e26568a6eb3a4297384ee98e272.

The exact full-scope literal is approved only for this isolated candidate by
keel_complete_source_admission_review_20260913/ROOT_CANDIDATE_ADMISSION_DECISION.json.
The original complete H0 map, eventual powers, reduced exceptional scheme,
zero-dimensional filter, original-field Euler degree and actual generation
comparisons are independently proved. No growth equivalence is assumed.
Production promotion is separate from this individual source admission.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory KltDP.Geometry
universe u

namespace KltDP.Literature.Keel

/-- Keel, full Theorem 0.2: a nef line on an arbitrary projective scheme in
positive characteristic is semiample exactly when its actual exceptional
restriction is semiample. The ambient scheme need not be reduced or integral. -/
axiom semiampleness_completeSystem_literal
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (hproj : IsProjectiveOverField f)
    (L : InvertibleSheaf X) (hnef : Positivity.IsNef f L) :
    letI : IsProper f := hproj.isProper
    Positivity.IsSemiample L ↔
      Positivity.IsSemiample (KeelCompleteSystem.exceptionalRestrict f L)

end KltDP.Literature.Keel
