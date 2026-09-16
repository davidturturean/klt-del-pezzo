import KltDP.LinearAlgebra.RootedTreeBudgets

/-!
# The remaining beta-five tree charge cases

After the two core vertices have been proved isolated, the source volume
is the extra-component charge minus 13/15. A canonical boundary component
uses at least one of the four available edges. The actual rooted-tree
charge theorems exclude one extra immediately, and force a single-edge
canonical component for two extras. Its actual Green value and the
projection identity then require charge 8/9, absent from the complete
three-edge pair list.

These theorems reuse the already proved arbitrary-tree classification,
not an assumed list of candidate matrices. Transport of the component
budget and the source equations from the ambient forest is separate.
Source: `lem:ten-forests`, beta-five paragraph, manuscript lines 2750–2764.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- Every actual single-source rooted tree with at most three edges has
Green charge at most two thirds. -/
theorem rootedTreeGreen_three_le_two_thirds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    rootedTreeGreen G root 3 ≤ 2 / 3 := by
  obtain ⟨choice, _, hgreen⟩ := rootedTreeGreen_three_choice G root hG hedges
  rw [hgreen, rootedBlockActualCharge_eq]
  rcases (exists_rootedBlockChoice (fun c => choice = c)).mp ⟨choice, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockCharge, rootedArmGreenNumerator, rootedArmDenominator,
      rootedArmLengths, Fin.sum_univ_succ]

/-- Actual extra trees sharing at most two edges have charge at most 5/6. -/
theorem pairedRootedTree_two_le_five_sixths
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 2) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ≤ 5 / 6 := by
  have hmem := pairedRootedTree_two G H rootG rootH hG hH hbudget
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h <;> rw [h] <;> norm_num

/-- The canonical matrix of any actual one-edge tree has root Green 2/3.
The root need not be separately assumed to be a leaf. -/
theorem canonical_one_edge_tree_green
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card = 1) :
    rootedTreeGreen G root 2 = 2 / 3 := by
  obtain ⟨choice, hcount, _, hgreen⟩ := rootedTreeGreen_two_choice G root hG (by omega)
  rw [hedges] at hcount
  rw [hgreen]
  rcases (exists_rootedBlockChoice (fun c => choice = c)).mp ⟨choice, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
      rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator] at hcount ⊢

/-- The beta-five one-extra volume is strictly negative on every actual
extra component with the remaining three-edge allowance. -/
theorem betaFive_one_extra_volume_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    rootedTreeGreen G root 3 - 13 / 15 < 0 := by
  have h := rootedTreeGreen_three_le_two_thirds G root hG hedges
  linarith

/-- Two actual extra components cannot satisfy the remaining beta-five
projection identity and positive volume. The canonical component is
required only to have an edge; its shape and Green value are derived. -/
theorem betaFive_two_extra_trees_impossible
    {A V W : Type*} [Fintype A] [Fintype V] [Fintype W]
    [DecidableEq A] [DecidableEq V] [DecidableEq W]
    (C : SimpleGraph A) (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel C.Adj] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (rootC : A) (rootG : V) (rootH : W)
    (hC : C.IsTree) (hG : G.IsTree) (hH : H.IsTree)
    (hboundary : 0 < C.edgeFinset.card)
    (hbudget : C.edgeFinset.card + G.edgeFinset.card + H.edgeFinset.card ≤ 4)
    (hvolume : 0 < rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 - 13 / 15)
    (hprojection :
      (rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 - 13 / 15) *
        (rootedTreeGreen C rootC 2 + 8 / 15 - 1) = (1 / 15 : ℚ)^2) : False := by
  have hcanonical : C.edgeFinset.card = 1 := by
    by_contra hnot
    have ht := pairedRootedTree_two_le_five_sixths G H rootG rootH hG hH (by omega)
    linarith
  have hc := canonical_one_edge_tree_green C rootC hC hcanonical
  rw [hc] at hprojection
  have htau : rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 = 8 / 9 := by
    nlinarith only [hprojection]
  have hmem := pairedRootedTree_three G H rootG rootH hG hH (by omega)
  rw [htau] at hmem
  norm_num at hmem

end KltDP.LinearAlgebra
