import KltDP.Examples.FrobeniusContractingNullRestriction
import KltDP.Geometry.InvertibleSheafSectionPowersPullback

/-!
# Frames for all actual powers along the original contracting locus

The proved restriction frames of the original contracting sheaf tensor
to frames of each actual power. The existing pullback-power comparison
preserves the original graph, fiber, chain and full null-locus inclusions.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingNullPowers

open KltDP.Geometry InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
open FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreContractingRestrictions
open FrobeniusMultiCentreOldChain FrobeniusContractingOldChainRestriction
open FrobeniusContractingNullRestriction

private def powerRestrictionFrame {X Y : Scheme.{u}} (j : Y ⟶ X)
    (L : InvertibleSheaf X)
    (e : (pullbackInvertibleSheaf j L).obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (m : ℕ) : (pullbackInvertibleSheaf j (power L m)).obj ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
  powerPullbackIso j L m ≪≫ powerFrame (pullbackInvertibleSheaf j L) e m

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Every actual power restricts trivially to the original strict graph. -/
def graphPowerRestrictionUnitIso (m : ℕ) :
    (pullbackInvertibleSheaf (graphStrictι (q + 1) n a)
      (power (contractingLine q n a ha hproj) m)).obj ≅
        _root_.SheafOfModules.unit (graphStrict (q + 1) n a).ringCatSheaf :=
  powerRestrictionFrame _ _ (graphRestrictionUnitIso q n a ha hproj) m

/-- Every actual power restricts trivially to each original strict special fiber. -/
def fiberPowerRestrictionUnitIso (i : Fin n) (m : ℕ) :
    (pullbackInvertibleSheaf (fiberStrictι (q + 1) n a i)
      (power (contractingLine q n a ha hproj) m)).obj ≅
        _root_.SheafOfModules.unit (fiberStrict (q + 1) n a i).ringCatSheaf :=
  powerRestrictionFrame _ _ (fiberRestrictionUnitIso q n a ha hproj i) m

/-- Every actual power restricts trivially to each original reduced old chain. -/
def oldChainPowerRestrictionUnitIso (i : Fin n) (m : ℕ) :
    (pullbackInvertibleSheaf (oldChainInclusion q n a ha i)
      (power (contractingLine q n a ha hproj) m)).obj ≅
        _root_.SheafOfModules.unit (oldChain q n a ha i).ringCatSheaf :=
  powerRestrictionFrame _ _ (oldChainRestrictionUnitIso q n a ha hproj i) m

/-- Every actual power is trivial on the entire independently defined reduced null locus. -/
def nullPowerRestrictionUnitIso (hn : 2 < n) (m : ℕ) :
    (pullbackInvertibleSheaf
      (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj))
      (power (contractingLine q n a ha hproj) m)).obj ≅
        _root_.SheafOfModules.unit
          (Positivity.nullLocusScheme (multiStructure (q + 1) n a)
            (contractingLine q n a ha hproj)).ringCatSheaf :=
  powerRestrictionFrame _ _ (contractingNullRestrictionUnitIso q n a ha hproj hn) m

end KltDP.Examples.FrobeniusContractingNullPowers
