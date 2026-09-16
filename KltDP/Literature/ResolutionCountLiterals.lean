import KltDP.Geometry.Resolution

/-!
# Stacks literal: a birational morphism is an isomorphism over a dense open (F10, E3)

`BirationalIsoOverDenseOpenLiteral` — Stacks 0BAJ (Lemma 29.52.6), encoded for birational (Definition 29.51.1,
tag 01RO) morphisms over `k` between normal projective surfaces. It is used only as a hypothesis; nothing is
assumed. The exact text, tag and fetch date (2026-09-11) are in `laneE/F10_LITERALS.md`. Its consumer is the
finiteness of the exceptional prime curves of a resolution in `KltDP.Geometry.MinimalResolutionCount`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry

universe u

namespace KltDP.Literature.Stacks

variable (k : Type u) [Field k]

/-- Stacks 0BAJ, Lemma 29.52.6: "Let `X`, `Y` be schemes. Let `f : X → Y` be a birational morphism between schemes
which have finitely many irreducible components. Assume either `f` is quasi-compact or `f` is separated, and either
`f` is locally of finite type and `Y` is reduced or `f` is locally of finite presentation. Then there exists a dense
open `V ⊂ Y` such that `f⁻¹(V) → V` is an isomorphism." Encoded for a morphism `π` over `k` between normal
projective surfaces (integral, hence one irreducible component each and reduced target; `π` is separated and locally
of finite type, being a morphism of projective `k`-schemes over `k`) which is birational in the sense of 01RO. -/
structure BirationalIsoOverDenseOpenLiteral : Prop where
  exists_dense_open : ∀ (S X : NormalProjectiveSurface k) (π : S.toScheme ⟶ X.toScheme),
    π ≫ X.structureMorphism = S.structureMorphism → IsBirational π →
      ∃ V : X.toScheme.Opens, Dense (V : Set X.toScheme) ∧ IsIso (π ∣_ V)

end KltDP.Literature.Stacks
