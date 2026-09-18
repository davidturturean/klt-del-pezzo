import KltDP.Examples.FrobeniusMultiCentreOldChainTrivial
import KltDP.Examples.FrobeniusMultiCentreContractingRestrictions

/-!
# M is trivial on each original old exceptional chain

The separately proved original component frames discharge the exact
old-chain component-unit criterion. The original newest exceptional curve
is excluded from that reduced chain by its construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingOldChainRestriction

open KltDP.Geometry FrobeniusMultiCentreSurface
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreContractingRestrictions
open FrobeniusMultiCentreOldChain

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- An actual frame of M on the original reduced old exceptional chain. -/
def oldChainRestrictionUnitIso (i : Fin n) :
    (schemeModulePullback (oldChainInclusion q n a ha i)).obj
      (contractingLine q n a ha hproj).obj ≅
      _root_.SheafOfModules.unit (oldChain q n a ha i).ringCatSheaf :=
  (oldChain_trivial_of_component_units q n a ha i (contractingLine q n a ha hproj)
    (fun j => ⟨oldExceptionalRestrictionUnitIso q n a ha hproj i j⟩)).some

end KltDP.Examples.FrobeniusContractingOldChainRestriction
