import KltDP.Support.SmallTableEightTotal

/-!
# The eight-vertex determinant table with total isolated-node counts

The finite forest determines its own component counts through the existing
matrix decomposition. The total number of isolated vertices, rather than a
chosen isolated subset, occurs in the three surviving index/count pairs and
in the strict inequality against the index's two-adic exponent.

The determinant-square equation is the explicit arithmetic premise of this
support result. Its geometric Picard-lattice justification is not assumed
to have been proved here.
-/

namespace KltDP.Support.SmallTableEightTotal

open Matrix SimpleGraph
open KltDP.Lattices.SmallADEPartitions KltDP.Lattices.SmallADEMatrices
open KltDP.Lattices.SmallADEGraphs KltDP.Lattices.SmallADEForestDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype G.ConnectedComponent]
variable [∀ c : G.ConnectedComponent, Fintype c.supp]

/-- The existing decomposition also identifies the total isolated-vertex
cardinality of the original forest. All counts are derived from that graph. -/
theorem smallADEForest_decomposition_total_isolated
    (hG : G.IsAcyclic) (hvertices : Fintype.card V ≤ 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent) :
    ∃ counts : Counts, ∃ e : V ≃ Vertex counts,
      counts.rank = Fintype.card V ∧
      counts.components = Fintype.card G.ConnectedComponent ∧
      (cartanMatrix counts).submatrix e e = graphCartanMatrix G ∧
      (graphCartanMatrix G).det = (counts.rootDet : ℤ) ∧
      Nat.card {v : V // v ∉ G.support} = counts.a1 := by
  obtain ⟨counts, e, hrank, hcount, hmatrix, hdet⟩ :=
    smallADEForest_decomposition G hG hvertices hcomponents
  exact ⟨counts, e, hrank, hcount, hmatrix, hdet,
    total_isolated_card_eq_a1 G counts e hmatrix⟩

/-- All eight count/determinant rows apply to an actual eight-vertex forest,
with `a1` identified as its total isolated-node count. -/
theorem eight_vertex_forest_total_node_table
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent) :
    ∃ counts : Counts, ∃ e : V ≃ Vertex counts,
      (cartanMatrix counts).submatrix e e = graphCartanMatrix G ∧
      counts ∈ rankEightRows ∧
      (counts, counts.rootDet) ∈
        ({(⟨2, 3, 0, 0, 0⟩, 108), (⟨3, 1, 1, 0, 0⟩, 96),
          (⟨4, 0, 0, 0, 1⟩, 64), (⟨4, 0, 0, 1, 0⟩, 80),
          (⟨4, 2, 0, 0, 0⟩, 144), (⟨5, 0, 1, 0, 0⟩, 128),
          (⟨6, 1, 0, 0, 0⟩, 192), (⟨8, 0, 0, 0, 0⟩, 256)} : Finset (Counts × ℕ)) ∧
      (graphCartanMatrix G).det = (counts.rootDet : ℤ) ∧
      Nat.card {v : V // v ∉ G.support} = counts.a1 := by
  obtain ⟨counts, e, hrank, hcount, hmatrix, hdet, htotal⟩ :=
    smallADEForest_decomposition_total_isolated G hG hvertices.le hcomponents
  have hrank8 : counts.rank = 8 := hrank.trans hvertices
  have hcount5 : 5 ≤ counts.components := by omega
  exact ⟨counts, e, hmatrix, rankEight_classification counts hrank8 hcount5,
    rankEight_rootDet_table counts hrank8 hcount5, hdet, htotal⟩

/-- The determinant-square condition leaves precisely the stated index and
TOTAL isolated-node count pairs for the original eight-vertex forest. -/
theorem eight_vertex_square_total_node_pairs
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent)
    (I : ℕ) (hsquare : (graphCartanMatrix G).det.natAbs = I ^ 2) :
    (I = 8 ∧ Nat.card {v : V // v ∉ G.support} = 4) ∨
    (I = 12 ∧ Nat.card {v : V // v ∉ G.support} = 4) ∨
    (I = 16 ∧ Nat.card {v : V // v ∉ G.support} = 8) := by
  obtain ⟨counts, e, hrank, hcount, hmatrix, hdet, htotal⟩ :=
    smallADEForest_decomposition_total_isolated G hG hvertices.le hcomponents
  have hsquareCounts : counts.rootDet = I ^ 2 := by
    simpa [hdet] using hsquare
  rw [htotal]
  exact rankEight_square_index_node_pairs counts I
    (hrank.trans hvertices) (by omega) hsquareCounts

/-- Every square row has strictly more actual isolated vertices than the
exponent of two in its natural index. -/
theorem eight_vertex_square_factorization_lt_total
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent)
    (I : ℕ) (hsquare : (graphCartanMatrix G).det.natAbs = I ^ 2) :
    I.factorization 2 < Nat.card {v : V // v ∉ G.support} := by
  obtain ⟨counts, e, hrank, hcount, hmatrix, hdet, htotal⟩ :=
    smallADEForest_decomposition_total_isolated G hG hvertices.le hcomponents
  have hsquareCounts : counts.rootDet = I ^ 2 := by
    simpa [hdet] using hsquare
  rw [htotal]
  exact rankEight_square_factorization_lt_nodes counts I
    (hrank.trans hvertices) (by omega) hsquareCounts

end KltDP.Support.SmallTableEightTotal
