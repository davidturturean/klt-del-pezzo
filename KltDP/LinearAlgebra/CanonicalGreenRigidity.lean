import KltDP.LinearAlgebra.RootedTreeBudgets

/-!
# A canonical tree with diagonal Green entry two thirds

For an actual tree with at most three edges and every weight equal to two,
the diagonal inverse entry two thirds characterizes the two-vertex path.
The conclusion is a root-preserving graph isomorphism, rather than numerical
membership in the rooted table. It also gives the actual edge cardinality.

This is the component-shape step used after the scalar rigidity for family D
in manuscript Lemma 9.2. Applying it to a component of a larger graph still
requires the component inverse and its edge bound to be identified.

Reuse: the existing `smallRootedTree_classification`, actual matrix reindexing,
and `rootedBlockMatrixAt_inverse_root_two` provide all mathematical inputs.
No new graph-classification or inverse-matrix foundation is introduced.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- Among the actual small canonical trees, Green entry two thirds occurs
only at an endpoint of the two-vertex path. -/
theorem canonical_tree_iso_edge_of_green_two_thirds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3)
    (hgreen : rootedTreeGreen G root 2 = 2 / 3) :
    ∃ e : G ≃g rootedBlockGraph (.arms .endEdge),
      e root = rootedBlockRoot (.arms .endEdge) := by
  obtain ⟨choice, e, hroot⟩ := smallRootedTree_classification hG hedges root
  have hvalue : rootedBlockGreen choice 2 = 2 / 3 := by
    calc
      rootedBlockGreen choice 2 = rootedTreeGreen G root 2 := by
        change _ = (rootedGraphMatrix G root (2 : ℚ))⁻¹ root root
        rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot (2 : ℚ),
          ← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root_two]
      _ = 2 / 3 := hgreen
  have hchoice : choice = .arms .endEdge := by
    cases choice with
    | arms shape =>
      cases shape <;>
        norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator] at hvalue ⊢
    | leafStar => norm_num [rootedBlockGreen] at hvalue
  subst choice
  exact ⟨e, hroot⟩

/-- The inverse entry determines the actual component edge count. -/
theorem canonical_tree_edge_count_of_green_two_thirds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3)
    (hgreen : rootedTreeGreen G root 2 = 2 / 3) :
    G.edgeFinset.card = 1 := by
  obtain ⟨e, _⟩ := canonical_tree_iso_edge_of_green_two_thirds G root hG hedges hgreen
  rw [← rootedBlockEdges_eq_of_iso e]
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ]

end KltDP.LinearAlgebra
