import KltDP.Examples.FrobeniusMultiCentreContractedWeilClasses
import KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

/-!
# Actual old-exceptional classes vanish under the original contraction

The retained old exceptional primes have the already proved actual M-degree
zero. The original all-prime criterion gives their factorizations through
k-points, and the original birational class pushforward kills their singleton
classes. The endpoint supplies original source projectivity and keeps the
same original line, map, field triangle and prime criterion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreOldExceptionalWeilClasses

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

section General

variable (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Every retained old exceptional prime has actual contracting-line degree zero. -/
theorem old_exceptional_restrictionDegree_eq_zero (i : Fin n) (j : Fin q) :
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj).restrictionDegree
      (contractingLine q n a ha hproj) = 0 := by
  have h := exceptionalPrimeCurve_degree q n a ha hproj i (.inl j)
  rw [← contractingLine_class q n a ha hproj] at h
  change (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj).picardRestrictionDegree
    (contractingLine q n a ha hproj).toPic = 0 at h
  simpa only [(exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj).picardRestrictionDegree_toPic] using h

variable {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha hproj).toScheme ⟶ Y.toScheme) [IsProper π]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha hproj).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (contractingLine q n a ha hproj) = 0)

include hπ hcriterion in
/-- The original map kills every integer singleton on an actual old exceptional prime. -/
theorem old_exceptional_class_pushforward_eq_zero (i : Fin n) (j : Fin q) (z : ℤ) :
    BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha hproj) (X := Y) π hbir
      ((sourceSurface q n a ha hproj).weilClassMap
        (Finsupp.single (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj) z)) = 0 := by
  obtain ⟨p, hp, hpk⟩ :=
    (hcriterion (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)).mpr
      (old_exceptional_restrictionDegree_eq_zero q n a ha hproj i j)
  exact BirationalWeilClassPushforward.pushforward_weilClassMap_single_contracted
    π hbir (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj) z p hp hpk

end General

section Original

variable {Y : NormalProjectiveSurface k}
    (π : (sourceSurface q n a ha
      (originalMultiStructureProjective k (q + 1) n a)).toScheme ⟶ Y.toScheme) [IsProper π]
    (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
    (hbir : IsBirationalScheme π)
    (hcriterion : ∀ C : (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
      (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
        C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
      C.restrictionDegree (originalLine q n a ha) = 0)

include hπ hcriterion in
/-- Original projectivity is supplied, and the original line criterion is retained. -/
theorem original_old_exceptional_class_pushforward_eq_zero
    (i : Fin n) (j : Fin q) (z : ℤ) :
    let hproj := originalMultiStructureProjective k (q + 1) n a
    BirationalWeilClassPushforward.pushforward
      (S := sourceSurface q n a ha hproj) (X := Y) π hbir
      ((sourceSurface q n a ha hproj).weilClassMap
        (Finsupp.single (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj) z)) = 0 :=
  old_exceptional_class_pushforward_eq_zero q n a ha
    (originalMultiStructureProjective k (q + 1) n a) π hπ hbir hcriterion i j z

end Original

end KltDP.Examples.FrobeniusMultiCentreOldExceptionalWeilClasses
