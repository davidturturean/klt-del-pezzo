import KltDP.LinearAlgebra.RootedTreeBudgets
import KltDP.LinearAlgebra.RootedTreePositiveDefinite

/-!
# Manuscript Lemma 9.1: inverse entries of small rooted trees

Source: `source/manuscript.tex`, lines 2456–2511, `lem:rooted-trees`.
The matrix is defined from an arbitrary finite simple graph, with diagonal
`b` at the root and two elsewhere. Coefficients are rational numbers, as for
the manuscript's integral intersection matrices; `b : ℚ` includes every
integer weight. Every entry and every edge count below is an actual matrix
entry or graph cardinality.

The main theorem retains the source's positive-definiteness premise. The
valency bound follows from the edge bound and is proved in the conclusion.
The exact-value assertions include converse witnesses that are actual
positive-definite trees, rather than only arithmetic members of a table.
The isolated vertex is included in the distinguished-leaf clause by using
degree at most one. This module asserts no geometric realization by curves.
-/

namespace KltDP.Manuscript.S09

open Matrix SimpleGraph KltDP.LinearAlgebra

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
/-- Three edges already imply the manuscript's valency bound. -/
theorem rootedTrees_valency (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) (v : V) : G.degree v ≤ 3 := by
  have hcard := smallTree_vertex_bound hG hedges
  have hdegree := G.degree_lt_card_verts v
  omega

/-- Each displayed graph really is a tree; connectedness and its actual
edge/vertex counts supply the proof, independently of its shape name. -/
theorem rootedTrees_listed_isTree (choice : RootedBlockChoice) :
    (rootedBlockGraph choice).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨rootedBlockGraph_connected choice, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    rootedBlockGraph_edge_count, Nat.card_eq_fintype_card, rootedBlock_vertex_count]

private theorem listed_edges_le_three (choice : RootedBlockChoice) :
    rootedBlockEdges choice ≤ 3 := by
  cases choice with
  | arms shape =>
    cases shape <;> norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ]
  | leafStar => norm_num [rootedBlockEdges]

/-- The eight rows, with both their exact edge counts and their symbolic
inverse expressions, in the order printed in the source. -/
theorem rootedTrees_table (b : ℚ) :
    (rootedBlockEdges (.arms .point) = 0 ∧ rootedBlockGreen (.arms .point) b = 1 / b) ∧
    (rootedBlockEdges (.arms .endEdge) = 1 ∧
      rootedBlockGreen (.arms .endEdge) b = 2 / (2 * b - 1)) ∧
    (rootedBlockEdges (.arms .endTwo) = 2 ∧
      rootedBlockGreen (.arms .endTwo) b = 3 / (3 * b - 2)) ∧
    (rootedBlockEdges (.arms .middleTwo) = 2 ∧
      rootedBlockGreen (.arms .middleTwo) b = 1 / (b - 1)) ∧
    (rootedBlockEdges (.arms .endThree) = 3 ∧
      rootedBlockGreen (.arms .endThree) b = 4 / (4 * b - 3)) ∧
    (rootedBlockEdges (.arms .innerThree) = 3 ∧
      rootedBlockGreen (.arms .innerThree) b = 6 / (6 * b - 7)) ∧
    (rootedBlockEdges (.arms .centerStar) = 3 ∧
      rootedBlockGreen (.arms .centerStar) b = 2 / (2 * b - 3)) ∧
    (rootedBlockEdges .leafStar = 3 ∧ rootedBlockGreen .leafStar b = 1 / (b - 1)) := by
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]

/-- Exhaustion of the eight rooted shapes, their inverse root entries, and
the canonical-degree coefficient and correction for the actual input matrix.
Positive definiteness is a source premise, not an oracle for the conclusion. -/
theorem rootedTrees (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) {b : ℚ} (hb : 3 ≤ b)
    (_hA : (rootedGraphMatrix G root b).PosDef) :
    (∀ v, G.degree v ≤ 3) ∧
      ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
        e root = rootedBlockRoot choice ∧
        rootedBlockEdges choice = G.edgeFinset.card ∧
        (rootedBlockMatrixAt choice b).submatrix e.toEquiv e.toEquiv =
          rootedGraphMatrix G root b ∧
        rootedTreeGreen G root b = rootedBlockGreen choice b ∧
        (fun v => rootedGraphMatrix G root b v v - 2) =
          Pi.single (f := fun _ : V => ℚ) root (b - 2) ∧
        ((rootedGraphMatrix G root b)⁻¹ *ᵥ
          Pi.single (f := fun _ : V => ℚ) root (b - 2)) root =
            (b - 2) * rootedBlockGreen choice b ∧
        dotProduct (Pi.single (f := fun _ : V => ℚ) root (b - 2))
          ((rootedGraphMatrix G root b)⁻¹ *ᵥ
            Pi.single (f := fun _ : V => ℚ) root (b - 2)) =
              (b - 2) ^ 2 * rootedBlockGreen choice b := by
  refine ⟨rootedTrees_valency G hG hedges, ?_⟩
  obtain ⟨choice, e, hroot⟩ := smallRootedTree_classification hG hedges root
  have hgreen : (rootedGraphMatrix G root b)⁻¹ root root = rootedBlockGreen choice b := by
    rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot b,
      ← rootedBlockMatrixAt_eq_graph choice b, rootedBlockMatrixAt_inverse_root choice hb]
  refine ⟨choice, e, hroot, rootedBlockEdges_eq_of_iso e, ?_, hgreen,
    rootedGraphMatrix_diagonal_source G root b, ?_, ?_⟩
  · rw [rootedBlockMatrixAt_eq_graph]
    exact rootedGraphMatrix_submatrix e root (rootedBlockRoot choice) hroot b
  · rw [rootedGraphMatrix_source_root, hgreen]
  · rw [rootedGraphMatrix_source_correction, hgreen]

/-- Every row is realized by an actual positive-definite rooted tree at every
rational source weight. Thus the list contains no extraneous shape. -/
theorem rootedTrees_table_realized (choice : RootedBlockChoice) {b : ℚ} (hb : 3 ≤ b) :
    (rootedBlockGraph choice).IsTree ∧
    (rootedGraphMatrix (rootedBlockGraph choice) (rootedBlockRoot choice) b).PosDef ∧
    (rootedBlockGraph choice).edgeFinset.card = rootedBlockEdges choice ∧
    (∀ v, (rootedBlockGraph choice).degree v ≤ 3) ∧
    rootedTreeGreen (rootedBlockGraph choice) (rootedBlockRoot choice) b =
      rootedBlockGreen choice b := by
  have hG := rootedTrees_listed_isTree choice
  refine ⟨hG, ?_, rootedBlockGraph_edge_count choice, ?_, ?_⟩
  · rw [← rootedBlockMatrixAt_eq_graph]
    exact rootedBlockMatrixAt_posDef choice (by linarith)
  · apply rootedTrees_valency _ hG
    rw [rootedBlockGraph_edge_count]
    exact listed_edges_le_three choice
  · change (rootedGraphMatrix _ _ b)⁻¹ _ _ = _
    rw [← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root choice hb]

/-- Explicit occurrence witnesses for the paired charge sets. Each pair is
two independent actual trees; disjoint copies have the same entries and edge
budget. The predicate includes positive definiteness of both block matrices. -/
def RootedPairRealization (budget : ℕ) (charge : ℚ) : Prop :=
  ∃ left right : RootedBlockChoice,
    (rootedBlockGraph left).IsTree ∧ (rootedBlockGraph right).IsTree ∧
    (rootedGraphMatrix (rootedBlockGraph left) (rootedBlockRoot left) (3 : ℚ)).PosDef ∧
    (rootedGraphMatrix (rootedBlockGraph right) (rootedBlockRoot right) (3 : ℚ)).PosDef ∧
    (rootedBlockGraph left).edgeFinset.card +
      (rootedBlockGraph right).edgeFinset.card ≤ budget ∧
    rootedTreeGreen (rootedBlockGraph left) (rootedBlockRoot left) 3 +
      rootedTreeGreen (rootedBlockGraph right) (rootedBlockRoot right) 3 = charge

private theorem listed_green_three (choice : RootedBlockChoice) :
    rootedTreeGreen (rootedBlockGraph choice) (rootedBlockRoot choice) 3 =
      rootedBlockActualCharge choice := by
  rw [rootedBlockActualCharge_eq]
  exact (rootedTrees_table_realized choice (b := 3) (le_refl 3)).2.2.2.2.trans
    (rootedBlockGreen_three choice)

/-- Exact set membership has actual positive-definite graph witnesses in the
reverse direction. Arbitrary input graphs are handled by the following three
theorems, so this occurrence certificate is not a family-membership premise. -/
theorem rootedTrees_pair_realization_iff (budget : ℕ) (charge : ℚ) :
    RootedPairRealization budget charge ↔ charge ∈ rootedPairCharges budget := by
  constructor
  · rintro ⟨left, right, _, _, _, _, hbudget, hcharge⟩
    apply (mem_rootedPairCharges_iff budget charge).mpr
    refine ⟨left, right, ?_, ?_⟩
    · simpa only [rootedBlockGraph_edge_count] using hbudget
    · simpa only [listed_green_three] using hcharge
  · intro h
    obtain ⟨left, right, hbudget, hcharge⟩ := (mem_rootedPairCharges_iff budget charge).mp h
    have hleft := rootedTrees_table_realized left (b := 3) (le_refl 3)
    have hright := rootedTrees_table_realized right (b := 3) (le_refl 3)
    refine ⟨left, right, hleft.1, hright.1, hleft.2.1, hright.2.1, ?_, ?_⟩
    · simpa only [rootedBlockGraph_edge_count] using hbudget
    · simpa only [listed_green_three] using hcharge

/-- The first paired set, for arbitrary trees, with converse occurrence. -/
theorem rootedTrees_pairs_one (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 1) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15} : Finset ℚ) ∧
    ∀ charge : ℚ, RootedPairRealization 1 charge ↔ charge ∈ ({2 / 3, 11 / 15} : Finset ℚ) := by
  refine ⟨pairedRootedTree_one G H rootG rootH hG hH hbudget, ?_⟩
  intro charge
  rw [rootedTrees_pair_realization_iff, rootedPairCharges_one]

/-- The second paired set, for arbitrary trees, with converse occurrence. -/
theorem rootedTrees_pairs_two (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 2) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5} : Finset ℚ) ∧
    ∀ charge : ℚ, RootedPairRealization 2 charge ↔
      charge ∈ ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5} : Finset ℚ) := by
  refine ⟨pairedRootedTree_two G H rootG rootH hG hH hbudget, ?_⟩
  intro charge
  rw [rootedTrees_pair_realization_iff, rootedPairCharges_two]

/-- The half-open interval at three total edges, including occurrence of
both values by source-admissible block pairs. -/
theorem rootedTrees_pairs_three_interval (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 3)
    (hlow : 13 / 15 < rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3)
    (hhigh : rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ≤ 14 / 15) :
    (rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 = 29 / 33 ∨
      rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 = 9 / 10) ∧
    ∀ charge : ℚ,
      (RootedPairRealization 3 charge ∧ 13 / 15 < charge ∧ charge ≤ 14 / 15) ↔
        charge ∈ ({29 / 33, 9 / 10} : Finset ℚ) := by
  refine ⟨pairedRootedTree_three_interval G H rootG rootH hG hH hbudget hlow hhigh, ?_⟩
  intro charge
  rw [rootedTrees_pair_realization_iff, ← rootedPairCharges_three_interval]
  simp only [Finset.mem_filter]

/-- The complete three-edge set computed in the source proof, before the
half-open interval restriction. -/
theorem rootedTrees_pairs_three (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 3) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} :
        Finset ℚ) ∧
    ∀ charge : ℚ, RootedPairRealization 3 charge ↔
      charge ∈ ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} :
        Finset ℚ) := by
  refine ⟨pairedRootedTree_three G H rootG rootH hG hH hbudget, ?_⟩
  intro charge
  rw [rootedTrees_pair_realization_iff, rootedPairCharges_three]

/-- Occurrence at a distinguished leaf in an actual all-weight-two tree.
Degree zero permits the isolated vertex, exactly as in the source. -/
def CanonicalLeafRealization (edges : ℕ) (charge : ℚ) : Prop :=
  ∃ choice : RootedBlockChoice,
    (rootedBlockGraph choice).IsTree ∧
    (rootedGraphMatrix (rootedBlockGraph choice) (rootedBlockRoot choice) (2 : ℚ)).PosDef ∧
    (rootedBlockGraph choice).degree (rootedBlockRoot choice) ≤ 1 ∧
    (rootedBlockGraph choice).edgeFinset.card = edges ∧
    rootedTreeGreen (rootedBlockGraph choice) (rootedBlockRoot choice) 2 = charge

private theorem listed_green_two (choice : RootedBlockChoice) :
    rootedTreeGreen (rootedBlockGraph choice) (rootedBlockRoot choice) 2 =
      rootedBlockGreen choice 2 := by
  change (rootedGraphMatrix _ _ (2 : ℚ))⁻¹ _ _ = _
  rw [← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root_two]

/-- The finite distinguished-leaf set is exactly realized by actual trees. -/
theorem rootedTrees_leaf_realization_iff (edges : ℕ) (charge : ℚ) :
    CanonicalLeafRealization edges charge ↔ charge ∈ canonicalLeafCharges edges := by
  constructor
  · rintro ⟨choice, _, _, hleaf, hedges, hcharge⟩
    apply Finset.mem_image.mpr
    refine ⟨choice, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hleaf⟩, ?_⟩
    · simpa only [rootedBlockGraph_edge_count] using hedges
    · simpa only [listed_green_two] using hcharge
  · intro h
    obtain ⟨choice, hchoice, hcharge⟩ := Finset.mem_image.mp h
    obtain ⟨_, hedges, hleaf⟩ := Finset.mem_filter.mp hchoice
    refine ⟨choice, rootedTrees_listed_isTree choice, ?_, hleaf, ?_, ?_⟩
    · rw [← rootedBlockMatrixAt_eq_graph]
      exact rootedBlockMatrixAt_posDef choice (le_refl 2)
    · simpa only [rootedBlockGraph_edge_count] using hedges
    · simpa only [listed_green_two] using hcharge

/-- Every distinguished-leaf conclusion, for an arbitrary all-weight-two
tree with at most three edges. Exact edge counts retain their source meaning. -/
theorem rootedTrees_canonical_leaf (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) (hleaf : G.degree root ≤ 1) :
    rootedTreeGreen G root 2 ∈ canonicalLeafCharges G.edgeFinset.card ∧
    (G.edgeFinset.card = 0 → rootedTreeGreen G root 2 = 1 / 2) ∧
    (G.edgeFinset.card = 1 → rootedTreeGreen G root 2 = 2 / 3) ∧
    (G.edgeFinset.card = 2 → rootedTreeGreen G root 2 = 3 / 4) ∧
    (G.edgeFinset.card = 3 →
      rootedTreeGreen G root 2 = 4 / 5 ∨ rootedTreeGreen G root 2 = 1) :=
  ⟨canonicalLeaf_tree_mem G root hG hedges hleaf,
    fun h => canonicalLeaf_tree_zero G root hG h hleaf,
    fun h => canonicalLeaf_tree_one G root hG h hleaf,
    fun h => canonicalLeaf_tree_two G root hG h hleaf,
    fun h => canonicalLeaf_tree_three G root hG h hleaf⟩

/-- No entry in the distinguished-leaf list is merely a formal arithmetic
candidate: each occurs for a positive-definite tree with the exact edge count. -/
theorem rootedTrees_canonical_leaf_exact (charge : ℚ) :
    (CanonicalLeafRealization 0 charge ↔ charge = 1 / 2) ∧
    (CanonicalLeafRealization 1 charge ↔ charge = 2 / 3) ∧
    (CanonicalLeafRealization 2 charge ↔ charge = 3 / 4) ∧
    (CanonicalLeafRealization 3 charge ↔ charge = 4 / 5 ∨ charge = 1) := by
  simp only [rootedTrees_leaf_realization_iff, canonicalLeafCharges_zero,
    canonicalLeafCharges_one, canonicalLeafCharges_two, canonicalLeafCharges_three,
    Finset.mem_insert, Finset.mem_singleton, and_self]

end KltDP.Manuscript.S09
