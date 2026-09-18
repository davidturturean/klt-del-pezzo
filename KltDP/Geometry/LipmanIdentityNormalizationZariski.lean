import KltDP.Geometry.LipmanIdentityNormalizationClause
import KltDP.Geometry.SingularStalkCompletionNormal
import KltDP.Geometry.RegularLocalDimensionTwo

/-!
# Original identity normalization with the explicit Zariski source

The entire proposed closed-point source statement is an explicit argument.
The actual original singular-point completion result supplies the native
normal-ring condition. The generator definition of singularity is compared
with the project's cotangent definition by an existing proved equivalence.
No resolution input, source predicate, or literature axiom is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.LipmanIdentityNormalization

variable (hZariski :
  ∀ (k : Type u) [Field k]
    (B : Type u) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B]
    (p : Ideal B) [p.IsMaximal]
    [IsIntegrallyClosed (Localization.AtPrime p)],
    IsLocalRing
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ∧
      IsDomain
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)) ∧
      IsIntegrallyClosed
        (AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)))

variable {k : Type u} [Field k]

include hZariski in
/-- The original singular-point stalk completion satisfies normality in
the source's prime-localization sense, conditional on the full source. -/
theorem singularStalk_normalRing_of_zariski
    (X : NormalProjectiveSurface k) (x : X.Point)
    (hx : x ∈ singularLocus X.toScheme) :
    IsNormalRingStacks (localCompletion (X.toScheme.presheaf.stalk x)) := by
  have hnormal := localCompletion_singularStalk_normal_of_zariski hZariski X x hx
  letI : IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) := hnormal.2.1
  letI : IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x)) := hnormal.2.2
  exact normalRing_of_normalDomain _

include hZariski in
/-- Clause (4) for the same original identity morphism and original
singular locus, conditional on the entire explicit Zariski statement. -/
theorem original_identity_clause_four_of_zariski
    (X : NormalProjectiveSurface k) :
    IsNormalizationInFunctionField (𝟙 X.toScheme) ∧
      IsFinite (𝟙 X.toScheme) ∧ (singularLocus X.toScheme).Finite ∧
        (∀ x ∈ singularLocus X.toScheme,
          IsNormalRingStacks (localCompletion (X.toScheme.presheaf.stalk x))) := by
  obtain ⟨hν, hfinite, hsingular⟩ := identity_finite_normalization_and_singular_locus X
  exact ⟨hν, hfinite, hsingular, singularStalk_normalRing_of_zariski hZariski X⟩

/-- The literal generator-defined singular set is the original singular
locus; every point and local ring is preserved. -/
theorem singularByGenerators_eq_original_singularLocus
    (X : NormalProjectiveSurface k) :
    {x : X.toScheme | ¬ RegularLocalByGenerators (X.toScheme.presheaf.stalk x)} =
      singularLocus X.toScheme := by
  ext x
  exact not_congr (normalSurface_regularLocalByGenerators_iff X x)

include hZariski in
/-- The complete native clause (4), including the generator-defined
singular set, holds for the original identity under the full source. -/
theorem original_identity_native_clause_four_of_zariski
    (X : NormalProjectiveSurface k) :
    IsNormalizationInFunctionField (𝟙 X.toScheme) ∧
      IsFinite (𝟙 X.toScheme) ∧
        {x : X.toScheme | ¬ RegularLocalByGenerators (X.toScheme.presheaf.stalk x)}.Finite ∧
          (∀ x ∈ {x : X.toScheme | ¬ RegularLocalByGenerators (X.toScheme.presheaf.stalk x)},
            IsNormalRingStacks (localCompletion (X.toScheme.presheaf.stalk x))) := by
  rw [singularByGenerators_eq_original_singularLocus X]
  exact original_identity_clause_four_of_zariski hZariski X

end KltDP.Geometry.LipmanIdentityNormalization

#print axioms KltDP.Geometry.LipmanIdentityNormalization.singularStalk_normalRing_of_zariski
#print axioms KltDP.Geometry.LipmanIdentityNormalization.singularByGenerators_eq_original_singularLocus
#print axioms KltDP.Geometry.LipmanIdentityNormalization.original_identity_native_clause_four_of_zariski
