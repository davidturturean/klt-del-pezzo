import KltDP.Geometry.LipmanIdentityNormalizationClause
import KltDP.Geometry.LipmanIdentityNormalizationZariski
import KltDP.Geometry.LipmanGeneratorRegularity
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# An ordinary consumer of the entire raw Lipman implication

The proposed native source statement is an explicit universally quantified
argument. The original target supplies its actual identity normalization.
The existing input's finite singular set and actual completion proofs are
translated by proved adapters. The returned integral source and proper
birational morphism are retained unchanged when converting regularity.
No literature axiom, new source predicate, or resolution assertion is added.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.LipmanIdentityNormalization

variable (hLipman :
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y],
    topologicalKrullDim Y = 2 →
    ∀ (N : Scheme.{u}) (ν : N ⟶ Y),
      IsNormalizationInFunctionField ν →
      IsFinite ν →
      {n : N | ¬ RegularLocalByGenerators (N.presheaf.stalk n)}.Finite →
      (∀ n ∈ {n : N | ¬ RegularLocalByGenerators (N.presheaf.stalk n)},
        IsNormalRingStacks (localCompletion (N.presheaf.stalk n))) →
      ∃ (S : Scheme.{u}) (π : S ⟶ Y) (_ : IsIntegral S),
        IsLocallyNoetherian S ∧
        (∀ s : S, RegularLocalByGenerators (S.presheaf.stalk s)) ∧
        IsProper π ∧ IsBirationalScheme π)

variable {k : Type u} [Field k] [IsAlgClosed k]

include hLipman in
/-- The full raw source yields the existing conditional modification
interface, using its original finite set and completion hypotheses. -/
theorem lipmanModificationLiteral_of_raw_source : LipmanModificationLiteral k := by
  constructor
  intro X hfin hcomp
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  letI : IsNoetherian X.toScheme := ⟨⟩
  have hsing := singularByGenerators_eq_original_singularLocus X
  have hfinNative :
      {x : X.toScheme | ¬ RegularLocalByGenerators (X.toScheme.presheaf.stalk x)}.Finite := by
    rw [hsing]
    exact hfin
  have hcompNative :
      ∀ x ∈ {x : X.toScheme | ¬ RegularLocalByGenerators (X.toScheme.presheaf.stalk x)},
        IsNormalRingStacks (localCompletion (X.toScheme.presheaf.stalk x)) := by
    rw [hsing]
    intro x hx
    obtain ⟨hD, hI⟩ := hcomp x hx
    letI : IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) := hD
    letI : IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x)) := hI
    exact normalRing_of_normalDomain _
  obtain ⟨S, π, hS, _, hreg, hπ, hbir⟩ :=
    hLipman X.toScheme X.dimension_two X.toScheme (𝟙 X.toScheme)
      (isNormalizationInFunctionField_id X.toScheme X.normal)
      (inferInstance : IsFinite (𝟙 X.toScheme)) hfinNative hcompNative
  letI : IsIntegral S := hS
  letI : IsProper π := hπ
  exact ⟨S, π, hS,
    regularPoint_of_generatorRegular_proper_birational X S π hbir hreg, hπ, hbir⟩

end KltDP.Geometry.LipmanIdentityNormalization

#check @KltDP.Geometry.LipmanIdentityNormalization.lipmanModificationLiteral_of_raw_source
#print axioms KltDP.Geometry.LipmanIdentityNormalization.lipmanModificationLiteral_of_raw_source
