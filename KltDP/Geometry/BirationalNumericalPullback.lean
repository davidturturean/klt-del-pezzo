import KltDP.Geometry.BirationalRationalPicardPullback
import KltDP.Geometry.BirationalRationalWeilSupport

/-!
# Injective pullback on the original numerical Picard quotients

Every original source prime is either contracted or the original prime
above an actual target prime. The proved degree formulas therefore give
the exact preimage of the numerical kernel. The actual rational Picard
pullback descends through that kernel, and original target curve tests
prove the descended map injective. Its image annihilates all exceptional
curve tests; surjectivity onto that annihilator is not asserted here.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalNumericalPullback

open BirationalPrimeCorrespondence BirationalWeilPushforward

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)

include hπ hbir

theorem mem_numericallyTrivial_iff (v : X.RationalPicard) :
    rationalPullback π v ∈ S.numericallyTrivialSubmodule ↔
      v ∈ X.numericallyTrivialSubmodule := by
  rw [S.mem_numericallyTrivialSubmodule_iff, X.mem_numericallyTrivialSubmodule_iff]
  constructor
  · intro h C
    exact (degree_above π hπ hbir C v).symm.trans (h (abovePrimeCurve π hbir C))
  · intro h D
    by_cases hD : IsExceptionalCurve π D
    · exact degree_exceptional π hπ D hD v
    · obtain ⟨C, rfl⟩ := exists_abovePrimeCurve_of_not_exceptional π hbir D hD
      exact (degree_above π hπ hbir C v).trans (h C)

/-- The original pullback on the actual numerical quotient. -/
def pullback : X.NumericalClassGroup →ₗ[ℚ] S.NumericalClassGroup :=
  X.numericallyTrivialSubmodule.liftQ
    (S.rationalPicardNumericalMap.comp (rationalPullback π)) (by
      intro v hv
      change S.rationalPicardNumericalMap (rationalPullback π v) = 0
      apply (S.rationalPicardNumericalMap_eq_zero_iff _).mpr
      apply (S.mem_numericallyTrivialSubmodule_iff _).mp
      exact (mem_numericallyTrivial_iff π hπ hbir v).mpr hv)

@[simp]
theorem pullback_mk (v : X.RationalPicard) :
    pullback π hπ hbir (X.rationalPicardNumericalMap v) =
      S.rationalPicardNumericalMap (rationalPullback π v) := rfl

theorem degree_pullback_above (C : X.PrimeCurve) (c : X.NumericalClassGroup) :
    S.numericalRestrictionDegree (abovePrimeCurve π hbir C) (pullback π hπ hbir c) =
      X.numericalRestrictionDegree C c := by
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  rw [pullback_mk, S.numericalRestrictionDegree_mk, X.numericalRestrictionDegree_mk]
  exact degree_above π hπ hbir C v

theorem pullback_injective : Function.Injective (pullback π hπ hbir) := by
  intro a b hab
  apply (X.numericalClass_eq_iff a b).mpr
  intro C
  have h := congrArg (S.numericalRestrictionDegree (abovePrimeCurve π hbir C)) hab
  simpa only [degree_pullback_above π hπ hbir C] using h

/-- Every original exceptional curve annihilates the actual pullback image. -/
theorem degree_pullback_exceptional (C : S.PrimeCurve) (hC : IsExceptionalCurve π C)
    (c : X.NumericalClassGroup) :
    S.numericalRestrictionDegree C (pullback π hπ hbir c) = 0 := by
  obtain ⟨v, rfl⟩ := X.rationalPicardNumericalMap_surjective c
  rw [pullback_mk, S.numericalRestrictionDegree_mk]
  exact degree_exceptional π hπ C hC v

end KltDP.Geometry.BirationalNumericalPullback

#check @KltDP.Geometry.BirationalNumericalPullback.pullback
#check @KltDP.Geometry.BirationalNumericalPullback.pullback_injective
#print axioms KltDP.Geometry.BirationalNumericalPullback.pullback_injective
#print axioms KltDP.Geometry.BirationalNumericalPullback.degree_pullback_exceptional
