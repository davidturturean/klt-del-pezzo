import KltDP.Geometry.ClosedImmersionOpenRange
import KltDP.Examples.FrobeniusContractingNullRestriction

/-!
# The original null blocks are open charts of the actual reduced null locus

The original graph, special fibers, and old chains give a finite disjoint
closed partition. Each original factor map is therefore also an open
immersion. In particular it preserves the actual null-locus stalks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusNullBlocksOpen

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
  FrobeniusContractingBlockSupports FrobeniusContractingBlockCover
  FrobeniusContractingNullRestriction

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (hn : 2 < n)

/-- The actual factor map of every original null block is an open immersion. -/
theorem blockToNullLocus_isOpenImmersion (r : BlockIndex n) :
    IsOpenImmersion (blockToNullLocus q n a ha hproj hn r) := by
  classical
  let Y : ULift.{u} (BlockIndex n) → Scheme.{u} := fun s => blockScheme q n a ha s.down
  let i := fun s : ULift.{u} (BlockIndex n) => blockToNullLocus q n a ha hproj hn s.down
  have hdisj : ∀ s t, s ≠ t → Disjoint (Set.range (i s).base) (Set.range (i t).base) := by
    intro s t hst
    have hst' : s.down ≠ t.down := fun h => hst (ULift.ext s t h)
    have h := blockSupport_pairwise q n a ha hst'
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' := (congrArg (fun T => x ∈ T)
      (range_blockToNullLocus q n a ha hproj hn s.down)).mp hx
    have hy' := (congrArg (fun T => x ∈ T)
      (range_blockToNullLocus q n a ha hproj hn t.down)).mp hy
    exact (Set.disjoint_left.mp h) hx' hy'
  have hcover : ∀ x, ∃ s, x ∈ Set.range (i s).base := by
    intro x
    obtain ⟨s, hs⟩ := nullLocus_point_mem_block q n a ha hproj hn x
    refine ⟨ULift.up s, ?_⟩
    exact (congrArg (fun T => x ∈ T)
      (range_blockToNullLocus q n a ha hproj hn s)).mpr hs
  exact isOpenImmersion_of_closedImmersion_of_openRange _
    (ClosedPartitionUnitTriviality.range_isOpen Y i hdisj hcover (ULift.up r))

/-- The original null-block map gives an isomorphism on every actual stalk. -/
theorem blockToNullLocus_stalkMap_isIso (r : BlockIndex n) (z : blockScheme q n a ha r) :
    IsIso ((blockToNullLocus q n a ha hproj hn r).stalkMap z) := by
  letI := blockToNullLocus_isOpenImmersion q n a ha hproj hn r
  exact RationalTreePicard.isIso_stalkMap_of_isOpenImmersion _ z

end KltDP.Examples.FrobeniusNullBlocksOpen
