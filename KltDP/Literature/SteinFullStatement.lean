import KltDP.Geometry.PushforwardNormalizationConstruction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Full existential statement of Stacks 03H0

This module defines a proposition only. The original locally Noetherian
base and proper morphism are arbitrary, including empty and nonreduced
schemes. The two output isomorphisms preserve the original source and base
maps of the constructed relative spectrum and relative normalization.

Source: Stacks 03H0, with normalization as in 035H, at revision
`540451b3e79a131df8eca4c4187448e49dcb262d`. The saved source correspondence
review is `stein_full_source_admission_review_20260914/FULL_SOURCE_REVIEW.md`.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Literature.Stacks.Stein03H0

open KltDP.Geometry.PushforwardRelativeSpec

/-- The full factorization statement, retaining all five published clauses
and canonical comparisons with both actual constructed targets. -/
def FullStatement : Prop :=
  ∀ (S X : Scheme.{u}) [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f],
    ∃ (T : Scheme.{u}) (f' : X ⟶ T) (π : T ⟶ S),
      f' ≫ π = f ∧
      IsProper f' ∧
      (∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ T),
        ConnectedSpace (pullback f' q : Scheme.{u})) ∧
      IsFinite π ∧
      IsIso f'.c ∧
      (∃ eR : T ≅ relativeSpec f,
        f' ≫ eR.hom = fromSource f ∧
        eR.hom ≫ toBase f = π) ∧
      (∃ eN : T ≅ normalization f,
        f' ≫ eN.hom = toNormalization f ∧
        eN.hom ≫ normalizationToBase f = π)

end KltDP.Literature.Stacks.Stein03H0
