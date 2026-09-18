import KltDP.Examples.FrobeniusContractingConnectedBlocks
import KltDP.Topology.ConnectedClosedPartition
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-!
# The exact number of connected components of the original null locus

The constructed equivalence sends the actual connected-component quotient
to the original graph/fiber/old-chain labels. Thus the null locus has 2n+1
connected components. This counts the null scheme; no contraction or
identification with singular points is assumed here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusContractingConnectedComponentCount

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusContractingNullRestriction FrobeniusContractingBlockSupports
open FrobeniusContractingConnectedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (hn : 2 < n)

/-- The actual connected components are indexed by the original disjoint blocks. -/
def nullLocusConnectedComponentsEquiv :
    ConnectedComponents
      (Positivity.nullLocusScheme (multiStructure (q + 1) n a) (contractingLine q n a ha hproj)) ≃
        BlockIndex n :=
  KltDP.Topology.ConnectedClosedPartition.connectedComponentsEquiv
    (fun r => Set.range (blockToNullLocus q n a ha hproj hn r).base)
    (blockRange_isClosed q n a ha hproj hn)
    (blockRange_isConnected q n a ha hproj hn)
    (blockRange_pairwise q n a ha hproj hn)
    (iUnion_blockRange q n a ha hproj hn)

include hn

/-- The original reduced null locus has exactly one graph, n fiber and n old-chain components. -/
theorem natCard_nullLocus_connectedComponents :
    Nat.card (ConnectedComponents
      (Positivity.nullLocusScheme (multiStructure (q + 1) n a) (contractingLine q n a ha hproj))) =
        2 * n + 1 := by
  calc
    _ = Nat.card (BlockIndex n) := Nat.card_congr (nullLocusConnectedComponentsEquiv q n a ha hproj hn)
    _ = 2 * n + 1 := by simp [BlockIndex, Nat.card_eq_fintype_card, two_mul]

end KltDP.Examples.FrobeniusContractingConnectedComponentCount
