import KltDP.Geometry.CanonicalWeilBirational
import KltDP.Geometry.FrobeniusTargetCanonicalWeil
import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives

/-!
# Canonical Weil-class pushforward for the original Frobenius contraction

The source canonical representative and the target smooth-open canonical
representative are the independently constructed original divisors. All open
geometry needed by the generic differential comparison is derived here from
the actual contraction, its field triangle, and its all-prime criterion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalWeilPushforward

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]

/-- Pushforward of the actual source canonical Weil class is the independently
constructed canonical class on the same original target. -/
theorem canonicalWeil_pushforward :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∀ (hπ : π ≫ Y.structureMorphism = multiStructure (q + 1) n a)
      (hbir : IsBirationalScheme π)
      (hconnected : ∀ y : Y.toScheme, IsConnected (π.base ⁻¹' {y}))
      (hcriterion : ∀ C : (sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
          C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      BirationalWeilClassPushforward.pushforward
          (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
          (X := Y) π hbir
          ((sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)).weilClassMap
            (canonicalWeil q n a ha (originalMultiStructureProjective k (q + 1) n a))) =
        Y.weilClassMap (targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hπ hbir hconnected hcriterion
  letI : IsSmoothOfRelativeDimension 2 (multiStructure (q + 1) n a) :=
    multiStructure_smoothTwo (q + 1) n a ha
  letI : IsSmoothOfRelativeDimension 2
      (sourceSurface q n a ha
        (originalMultiStructureProjective k (q + 1) n a)).structureMorphism := by
    change IsSmoothOfRelativeDimension 2 (multiStructure (q + 1) n a)
    exact multiStructure_smoothTwo (q + 1) n a ha
  letI : Nonempty (nullImageComplement q n a ha π).toScheme :=
    nullImageComplement_nonempty q n a ha hn Y π hcriterion
  letI : IsIso (π ∣_ nullImageComplement q n a ha π) :=
    isIso_restrict_nullImageComplement q n a ha hn Y π hπ hbir hconnected hcriterion
  letI : IsSmoothOfRelativeDimension 2
      ((nullImageComplement q n a ha π).ι ≫ Y.structureMorphism) :=
    (nullImageComplement_smoothTwo_contains_primeGenericPoints
      q n a ha hn Y π hπ hbir hconnected hcriterion).1
  exact CanonicalWeilBirational.pushforward_canonical_weilClass
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    Y π hπ (nullImageComplement q n a ha π) hbir
    (fun C => genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C)

end KltDP.Examples.FrobeniusMultiCentreCanonicalWeilPushforward
