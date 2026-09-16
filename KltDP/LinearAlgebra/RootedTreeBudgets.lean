import KltDP.LinearAlgebra.RootedTreeTransport
import Mathlib.Tactic

/-!
# Edge budgets for actual rooted tree matrices

The pair theorems apply the exact finite charge sets to arbitrary finite rooted
trees. The generic theorem states each three-edge bound and the combined edge
budget explicitly; the one-, two-, and three-edge consequences derive the
individual bounds from the combined bound.

The final part treats all-weight-two matrices with a distinguished leaf,
allowing the single isolated vertex when the edge count is zero. The leaf
condition is stated using the degree in the actual graph.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- Root Green entry of the actual graph-defined rational weighted matrix. -/
noncomputable def rootedTreeGreen {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (b : ℚ) : ℚ :=
  (rootedGraphMatrix G root b)⁻¹ root root

/-- The variable-weight table specializes to the charge used in the finite
two-block calculations when the weight is three. -/
theorem rootedBlockGreen_three : ∀ choice : RootedBlockChoice,
    rootedBlockGreen choice 3 = rootedBlockCharge choice := by
  intro choice
  cases choice with
  | arms shape => rfl
  | leafStar => norm_num [rootedBlockGreen, rootedBlockCharge]

/-- An arbitrary small rooted tree supplies a listed actual inverse entry and
preserves its exact edge count. -/
theorem rootedTreeGreen_three_choice {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    ∃ choice : RootedBlockChoice,
      rootedBlockEdges choice = G.edgeFinset.card ∧
        rootedTreeGreen G root 3 = rootedBlockActualCharge choice := by
  obtain ⟨choice, hcount, hgreen⟩ :=
    smallRootedTree_inverse_root G root hG hedges (b := 3) (le_refl 3)
  refine ⟨choice, hcount, ?_⟩
  rw [rootedBlockActualCharge_eq]
  simpa only [rootedTreeGreen, rootedBlockGreen_three] using hgreen

/-- Exact finite charge-set membership for two arbitrary rooted trees. Each
tree has at most three actual edges, and the stated budget bounds their sum. -/
theorem pairedRootedTree_charge_mem {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hedgesG : G.edgeFinset.card ≤ 3) (hedgesH : H.edgeFinset.card ≤ 3)
    (budget : ℕ) (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ budget) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈ rootedPairCharges budget := by
  obtain ⟨choiceG, hcountG, hgreenG⟩ := rootedTreeGreen_three_choice G rootG hG hedgesG
  obtain ⟨choiceH, hcountH, hgreenH⟩ := rootedTreeGreen_three_choice H rootH hH hedgesH
  apply (mem_rootedPairCharges_iff budget _).mpr
  refine ⟨choiceG, choiceH, ?_, ?_⟩
  · simpa only [hcountG, hcountH] using hbudget
  · rw [← hgreenG, ← hgreenH]

/-- The set `S₁` for actual rooted trees sharing at most one edge in total. -/
theorem pairedRootedTree_one {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 1) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15} : Finset ℚ) := by
  have h := pairedRootedTree_charge_mem G H rootG rootH hG hH
    (by omega) (by omega) 1 hbudget
  simpa only [rootedPairCharges_one] using h

/-- The set `S₂` for actual rooted trees sharing at most two edges in total. -/
theorem pairedRootedTree_two {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 2) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5} : Finset ℚ) := by
  have h := pairedRootedTree_charge_mem G H rootG rootH hG hH
    (by omega) (by omega) 2 hbudget
  simpa only [rootedPairCharges_two] using h

/-- The complete three-edge charge set for two arbitrary rooted trees. -/
theorem pairedRootedTree_three {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 3) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      ({2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} :
        Finset ℚ) := by
  have h := pairedRootedTree_charge_mem G H rootG rootH hG hH
    (by omega) (by omega) 3 hbudget
  simpa only [rootedPairCharges_three] using h

/-- The source's half-open interval leaves exactly the two stated values for
actual trees satisfying the combined three-edge budget. -/
theorem pairedRootedTree_three_interval {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card ≤ 3)
    (hlow : 13 / 15 < rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3)
    (hhigh : rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ≤ 14 / 15) :
    rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 = 29 / 33 ∨
      rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 = 9 / 10 := by
  have hmem := pairedRootedTree_charge_mem G H rootG rootH hG hH
    (by omega) (by omega) 3 hbudget
  have hfilter : rootedTreeGreen G rootG 3 + rootedTreeGreen H rootH 3 ∈
      (rootedPairCharges 3).filter (fun charge => 13 / 15 < charge ∧ charge ≤ 14 / 15) :=
    Finset.mem_filter.mpr ⟨hmem, hlow, hhigh⟩
  rw [rootedPairCharges_three_interval] at hfilter
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hfilter

/-- The raw inverse formulas also apply when every weight is two. Each of
the eight denominators is checked to be nonzero at this specialization. -/
theorem rootedBlockMatrixAt_inverse_root_two (choice : RootedBlockChoice) :
    (rootedBlockMatrixAt choice 2)⁻¹ (rootedBlockRoot choice) (rootedBlockRoot choice) =
      rootedBlockGreen choice 2 := by
  cases choice with
  | arms shape =>
    apply rootedArmMatrix_inverse_root shape (2 : ℚ)
    cases shape <;> norm_num [rootedArmDenominator]
  | leafStar =>
    apply leafRootedStarMatrix_inverse_root (2 : ℚ)
    norm_num

/-- For an arbitrary small tree, transport both the actual root degree and
the all-weight-two inverse entry to a listed shape. -/
theorem rootedTreeGreen_two_choice {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    ∃ choice : RootedBlockChoice,
      rootedBlockEdges choice = G.edgeFinset.card ∧
        (rootedBlockGraph choice).degree (rootedBlockRoot choice) = G.degree root ∧
          rootedTreeGreen G root 2 = rootedBlockGreen choice 2 := by
  obtain ⟨choice, e, hroot⟩ := smallRootedTree_classification hG hedges root
  have hdegree : (rootedBlockGraph choice).degree (rootedBlockRoot choice) = G.degree root := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree, hroot] using
      (Fintype.card_congr (e.mapNeighborSet root)).symm
  refine ⟨choice, rootedBlockEdges_eq_of_iso e, hdegree, ?_⟩
  change (rootedGraphMatrix G root (2 : ℚ))⁻¹ root root = _
  rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot (2 : ℚ),
    ← rootedBlockMatrixAt_eq_graph choice 2, rootedBlockMatrixAt_inverse_root_two]

/-- All-weight-two entries from the listed graphs with an actual root degree
at most one and an exact edge count. Degree zero includes the isolated point. -/
def canonicalLeafCharges (edges : ℕ) : Finset ℚ :=
  ((Finset.univ : Finset RootedBlockChoice).filter
    (fun choice => rootedBlockEdges choice = edges ∧
      (rootedBlockGraph choice).degree (rootedBlockRoot choice) ≤ 1)).image
        (fun choice => rootedBlockGreen choice 2)

private def listedRootDegree : RootedBlockChoice → ℕ
  | .arms .point => 0
  | .arms .endEdge | .arms .endTwo | .arms .endThree | .leafStar => 1
  | .arms .middleTwo | .arms .innerThree => 2
  | .arms .centerStar => 3

/-- Compute the actual graph degrees before evaluating rational charge sets. -/
private theorem rootedBlockGraph_root_degree : ∀ choice : RootedBlockChoice,
    (rootedBlockGraph choice).degree (rootedBlockRoot choice) = listedRootDegree choice := by
  decide

theorem canonicalLeafCharges_zero : canonicalLeafCharges 0 = {1 / 2} := by
  ext charge
  simp only [canonicalLeafCharges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, rootedBlockGraph_root_degree, exists_rootedBlockChoice]
  norm_num [listedRootDegree, rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]
  simp only [eq_comm]

theorem canonicalLeafCharges_one : canonicalLeafCharges 1 = {2 / 3} := by
  ext charge
  simp only [canonicalLeafCharges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, rootedBlockGraph_root_degree, exists_rootedBlockChoice]
  norm_num [listedRootDegree, rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]
  simp only [eq_comm]

theorem canonicalLeafCharges_two : canonicalLeafCharges 2 = {3 / 4} := by
  ext charge
  simp only [canonicalLeafCharges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, rootedBlockGraph_root_degree, exists_rootedBlockChoice]
  norm_num [listedRootDegree, rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]
  simp only [eq_comm]

theorem canonicalLeafCharges_three : canonicalLeafCharges 3 = {4 / 5, 1} := by
  ext charge
  simp only [canonicalLeafCharges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, rootedBlockGraph_root_degree, exists_rootedBlockChoice]
  norm_num [listedRootDegree, rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]
  simp only [eq_comm]

/-- The canonical leaf list applies to an arbitrary actual tree, not only to
one of the shape names used to compute the finite set. -/
theorem canonicalLeaf_tree_mem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) (hleaf : G.degree root ≤ 1) :
    rootedTreeGreen G root 2 ∈ canonicalLeafCharges G.edgeFinset.card := by
  obtain ⟨choice, hcount, hdegree, hgreen⟩ := rootedTreeGreen_two_choice G root hG hedges
  apply Finset.mem_image.mpr
  refine ⟨choice, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount, ?_⟩, hgreen.symm⟩
  simpa only [hdegree] using hleaf

/-- The isolated all-weight-two vertex has inverse entry one half. -/
theorem canonicalLeaf_tree_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card = 0) (hleaf : G.degree root ≤ 1) :
    rootedTreeGreen G root 2 = 1 / 2 := by
  have h := canonicalLeaf_tree_mem G root hG (by omega) hleaf
  rw [hedges, canonicalLeafCharges_zero] at h
  exact Finset.mem_singleton.mp h

/-- One edge gives inverse entry two thirds at its distinguished leaf. -/
theorem canonicalLeaf_tree_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card = 1) (hleaf : G.degree root ≤ 1) :
    rootedTreeGreen G root 2 = 2 / 3 := by
  have h := canonicalLeaf_tree_mem G root hG (by omega) hleaf
  rw [hedges, canonicalLeafCharges_one] at h
  exact Finset.mem_singleton.mp h

/-- Two edges give inverse entry three quarters at a distinguished leaf. -/
theorem canonicalLeaf_tree_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card = 2) (hleaf : G.degree root ≤ 1) :
    rootedTreeGreen G root 2 = 3 / 4 := by
  have h := canonicalLeaf_tree_mem G root hG (by omega) hleaf
  rw [hedges, canonicalLeafCharges_two] at h
  exact Finset.mem_singleton.mp h

/-- With three edges the distinguished-leaf inverse entry is four fifths or
one, corresponding to the path and three-leaf star. -/
theorem canonicalLeaf_tree_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card = 3) (hleaf : G.degree root ≤ 1) :
    rootedTreeGreen G root 2 = 4 / 5 ∨ rootedTreeGreen G root 2 = 1 := by
  have h := canonicalLeaf_tree_mem G root hG (by omega) hleaf
  rw [hedges, canonicalLeafCharges_three] at h
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

end KltDP.LinearAlgebra
