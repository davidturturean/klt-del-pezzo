import KltDP.Geometry.FunctionFieldNormalization
import KltDP.Geometry.MinimalResolutionDebts

/-!
# Original identity-normalization inputs for Lipman's clause (4)

The original identity map supplies finite normalization and the original
finite singular locus.  The completion clause uses the published normal-ring
predicate.  Its adapter remains conditional on the two existing explicit
commutative-algebra hypotheses; no resolution theorem is assumed or added.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory KltDP.Literature.Stacks

universe u

namespace KltDP.Geometry.LipmanIdentityNormalization

/-- A normal domain is a normal ring in the prime-localization definition. -/
theorem normalRing_of_normalDomain (A : Type u) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] : IsNormalRingStacks A := by
  intro P hP
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization
    (Localization.AtPrime P) P.primeCompl P.primeCompl_le_nonZeroDivisors⟩

variable {k : Type u} [Field k]

/-- The existing actual-stalk completion result implies the published
normal-ring condition, without assuming locality of the completion. -/
theorem localCompletion_stalk_normalRing
    (hE : FiniteTypeExcellentFormalFibresLiteral k) (hC : CompletionNormalLiteral.{u})
    (X : NormalProjectiveSurface k) (x : X.Point) :
    IsNormalRingStacks (localCompletion (X.toScheme.presheaf.stalk x)) := by
  obtain ⟨hD, hI⟩ := localCompletion_stalk_normal hE hC X x
  letI : IsDomain (localCompletion (X.toScheme.presheaf.stalk x)) := hD
  letI : IsIntegrallyClosed (localCompletion (X.toScheme.presheaf.stalk x)) := hI
  exact normalRing_of_normalDomain _

/-- The original identity is a finite actual normalization, and its
singular locus is the original finite singular locus. -/
theorem identity_finite_normalization_and_singular_locus
    (X : NormalProjectiveSurface k) :
    IsNormalizationInFunctionField (𝟙 X.toScheme) ∧
      IsFinite (𝟙 X.toScheme) ∧ (singularLocus X.toScheme).Finite :=
  ⟨isNormalizationInFunctionField_id X.toScheme X.normal,
    inferInstance, normalSurface_singularLocus_finite X⟩

/-- All three parts of clause (4) hold for the same original identity map,
conditional only on the existing completion-source hypotheses. -/
theorem original_identity_clause_four
    (hE : FiniteTypeExcellentFormalFibresLiteral k) (hC : CompletionNormalLiteral.{u})
    (X : NormalProjectiveSurface k) :
    IsNormalizationInFunctionField (𝟙 X.toScheme) ∧
      IsFinite (𝟙 X.toScheme) ∧ (singularLocus X.toScheme).Finite ∧
        (∀ x ∈ singularLocus X.toScheme,
          IsNormalRingStacks (localCompletion (X.toScheme.presheaf.stalk x))) := by
  obtain ⟨hν, hfinite, hsingular⟩ := identity_finite_normalization_and_singular_locus X
  exact ⟨hν, hfinite, hsingular, fun x _ => localCompletion_stalk_normalRing hE hC X x⟩

end KltDP.Geometry.LipmanIdentityNormalization

#print axioms KltDP.Geometry.LipmanIdentityNormalization.normalRing_of_normalDomain
#print axioms KltDP.Geometry.LipmanIdentityNormalization.identity_finite_normalization_and_singular_locus
#print axioms KltDP.Geometry.LipmanIdentityNormalization.original_identity_clause_four
