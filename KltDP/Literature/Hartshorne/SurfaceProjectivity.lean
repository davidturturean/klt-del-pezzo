import KltDP.Geometry.Surface
import KltDP.Geometry.SingularPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Hartshorne's nonsingular complete surface projectivity statement

Robin Hartshorne, Algebraic Geometry, GTM 52, Springer, first edition 1977,
II Remark 4.10.2(b), printed p.105. The selected scan is the softcover
reprint, DOI 10.1007/978-1-4757-3849-0, SHA-256
55cee9c730cfb03ed9ecac25444c87579fe411077ddb14bc4b31c98cc3be2d5e.

This is the entire standalone assertion, with its variety/completeness
definitions on p.105, regular-stalk convention on pp.32/130, and projective
embedding definition on p.103 expanded. No characteristic restriction is
added. Specializations to the original constructed surfaces are proved
separately. Root approved this exact literal for an isolated candidate in
hartshorne_surface_admission/ROOT_CANDIDATE_ADMISSION_DECISION.json.
It is not yet part of the accepted production checkpoint.
-/

universe u

namespace KltDP.Literature.Hartshorne

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry

axiom nonsingular_complete_surface_projective_literal :
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)),
    IsIntegral X →
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsProper f →
    (∀ x : X, RegularPoint X x) →
    topologicalKrullDim X = 2 →
    ∃ (n : ℕ) (i : X ⟶ projectiveSpace k n),
      IsClosedImmersion i ∧ i ≫ projectiveSpaceToSpec k n = f

end KltDP.Literature.Hartshorne
