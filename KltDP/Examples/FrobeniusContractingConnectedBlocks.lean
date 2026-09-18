import KltDP.Examples.FrobeniusContractingNullRestriction
import KltDP.Examples.FrobeniusMultiCentreOldChainConnected

/-!
# The original contracting blocks form a connected closed partition

Each original graph, strict fiber and old chain is connected and nonempty.
Its actual closed immersion into the independently defined null-locus scheme
therefore has connected closed range. The original support formulas retain
the disjointness and cover needed to count connected components.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Examples.FrobeniusContractingConnectedBlocks

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreOldChain
open FrobeniusContractingNullRestriction FrobeniusContractingBlockSupports
open FrobeniusContractingBlockCover

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (hn : 2 < n)

/-- Every original block has connected range inside the actual null locus. -/
theorem blockRange_isConnected (r : BlockIndex n) :
    IsConnected (Set.range (blockToNullLocus q n a ha hproj hn r).base) := by
  haveI : ConnectedSpace (blockScheme q n a ha r) := by
    cases r with
    | none =>
        change ConnectedSpace (graphStrict (q + 1) n a)
        letI := graphStrict_isIntegral (q + 1) n a
        infer_instance
    | some r =>
        cases r with
        | inl i =>
            change ConnectedSpace (fiberStrict (q + 1) n a i)
            letI := fiberStrict_isIntegral (q + 1) n a i
            infer_instance
        | inr i =>
            change ConnectedSpace (oldChain q n a ha i)
            infer_instance
  exact isConnected_range (blockToNullLocus q n a ha hproj hn r).base.hom.continuous

/-- The original closed immersions give closed ranges inside the actual null locus. -/
theorem blockRange_isClosed (r : BlockIndex n) :
    IsClosed (Set.range (blockToNullLocus q n a ha hproj hn r).base) :=
  (blockToNullLocus q n a ha hproj hn r).isClosedEmbedding.isClosed_range

/-- Distinct original blocks have disjoint ranges inside the actual null locus. -/
theorem blockRange_pairwise : Pairwise (fun r t : BlockIndex n =>
    Disjoint (Set.range (blockToNullLocus q n a ha hproj hn r).base)
      (Set.range (blockToNullLocus q n a ha hproj hn t).base)) := by
  intro r t hrt
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := (congrArg (fun T => x ∈ T)
    (range_blockToNullLocus q n a ha hproj hn r)).mp hx
  have hy' := (congrArg (fun T => x ∈ T)
    (range_blockToNullLocus q n a ha hproj hn t)).mp hy
  exact (Set.disjoint_left.mp (blockSupport_pairwise q n a ha hrt)) hx' hy'

/-- Every point of the actual null locus belongs to an original connected block. -/
theorem iUnion_blockRange :
    (⋃ r : BlockIndex n, Set.range (blockToNullLocus q n a ha hproj hn r).base) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨r, hr⟩ := nullLocus_point_mem_block q n a ha hproj hn x
  exact Set.mem_iUnion.mpr ⟨r, (congrArg (fun T => x ∈ T)
    (range_blockToNullLocus q n a ha hproj hn r)).mpr hr⟩

end KltDP.Examples.FrobeniusContractingConnectedBlocks
