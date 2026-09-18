import KltDP.Geometry.FunctionFieldNormalization
import KltDP.Literature.ResolutionDebtLiterals

/-!
The entire implication (4) => (2) of Stacks 0BGP, Theorem 54.14.5.
Normalization is presented by coherent integral-closure charts in the
original function field. See the separate root admission and dictionary.
This isolated literature candidate does not alter the production allowlist.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KltDP.Geometry
universe u
namespace KltDP.Literature.Stacks

axiom lipman_resolution_of_normal_completions_literal :
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
        IsProper π ∧ IsBirationalScheme π

end KltDP.Literature.Stacks
#check @KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal
#print axioms KltDP.Literature.Stacks.lipman_resolution_of_normal_completions_literal
