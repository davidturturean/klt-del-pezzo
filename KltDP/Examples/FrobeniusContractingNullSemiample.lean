import KltDP.Examples.FrobeniusContractingNullRestriction
import KltDP.Geometry.TrivialInvertibleSheafSemiample

/-!
# Semiampleness of M on its actual reduced null locus

The constructed unit frame supplies global generation and a positive
power witnessing semiampleness of the original restriction. No version
of Keel's theorem is assumed or applied here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingNullSemiample

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusContractingNullRestriction

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (hn : 2 < n)

include hn

/-- The original restriction of M to the entire null locus is globally generated. -/
theorem contractingNullRestriction_globallyGenerated :
    Positivity.IsGloballyGenerated
      (pullbackInvertibleSheaf
        (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
          (contractingLine q n a ha hproj)) (contractingLine q n a ha hproj)).obj :=
  Positivity.isGloballyGenerated_of_unitIso _
    (contractingNullRestrictionUnitIso q n a ha hproj hn)

/-- A positive actual tensor power witnesses semiampleness on the entire null locus. -/
theorem contractingNullRestriction_semiample :
    Positivity.IsSemiample
      (pullbackInvertibleSheaf
        (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
          (contractingLine q n a ha hproj)) (contractingLine q n a ha hproj)) :=
  Positivity.isSemiample_of_unitIso _
    (contractingNullRestrictionUnitIso q n a ha hproj hn)

end KltDP.Examples.FrobeniusContractingNullSemiample
