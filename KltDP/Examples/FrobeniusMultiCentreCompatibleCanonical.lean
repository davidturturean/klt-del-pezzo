import KltDP.Geometry.CanonicalCartierRepresentativePushforward
import KltDP.Geometry.FrobeniusTargetCanonicalWeil
import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives

/-!
# An exact compatible canonical Cartier divisor on the original Frobenius source

The original contraction determines a source Cartier divisor whose module is
the actual second exterior sheaf of relative differentials and whose integral
Weil pushforward is the independently constructed target canonical divisor.
All geometry of the original null-image complement is derived from the same
contraction. No canonical compatibility is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCompatibleCanonical

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved FrobeniusMultiCentreCanonicalWeilRepresentatives
open KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (Y : NormalProjectiveSurface k)
    (π : multiSurface (q + 1) n a ⟶ Y.toScheme)
    [IsProper π] [Surjective π] [IsIso π.c]

/-- An actual source canonical Cartier divisor whose Weil divisor pushes
forward exactly to the original target canonical Weil divisor. -/
theorem exists_compatible_canonical_cartier :
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
      ∃ D : CartierDivisor (sourceSurface q n a ha
          (originalMultiStructureProjective k (q + 1) n a)).toScheme,
        Nonempty (cartierDivisorModule (sourceSurface q n a ha
            (originalMultiStructureProjective k (q + 1) n a)).toScheme D ≅
          SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            (multiStructure (q + 1) n a) 2) ∧
        BirationalWeilPushforward.pushforward
            (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
            (X := Y) π hbir
            ((sourceSurface q n a ha
              (originalMultiStructureProjective k (q + 1) n a)).cartierToWeilHom D) =
          targetCanonicalWeil q n a ha hn Y π hπ hbir hconnected hcriterion := by
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
  exact CanonicalWeilBirational.exists_compatible_canonical_cartier
    (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
    Y π hπ (nullImageComplement q n a ha π) hbir
    (fun C => genericPoint_mem_nullImageComplement q n a ha hn Y π hcriterion C)

end KltDP.Examples.FrobeniusMultiCentreCompatibleCanonical
