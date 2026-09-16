import KltDP.LinearAlgebra.GraphGreenComponents
import KltDP.LinearAlgebra.CanonicalGreenRigidity
import KltDP.Lattices.SmallForestComponents

/-!
# Restricting a graph inverse to an actual component

The full weighted graph matrix has no edges between different connected
components. Its inverse restricted to a component is the inverse of that
component's actual induced weighted graph matrix.

Reuse: pinned Mathlib `Matrix.BlockTriangular.inv_toBlock` gives precisely
the inverse restriction identity. The graph-specific work identifies its
cut predicate with actual reachability and uses the existing graph-embedding
matrix transport. No inverse equality or block classification is assumed.

The final theorem transports diagonal entry two thirds to the small
canonical component classification, deriving the component tree and edge
bounds from the ambient forest. Identifying a geometric exceptional
configuration with that actual weighted graph remains a separate obligation.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inducing a graph cannot increase its actual number of edges. -/
theorem graph_induce_edge_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (fun v => v ∈ s)] :
    (G.induce s).edgeFinset.card ≤ G.edgeFinset.card := by
  classical
  rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
  exact Fintype.card_le_of_injective
    (SimpleGraph.Embedding.induce s).mapEdgeSet
    (SimpleGraph.Embedding.induce s).mapEdgeSet.injective

/-- The graph on vertices reachable from a specified vertex is an actual
tree whenever the ambient graph is a forest. -/
theorem graph_reachable_component_isTree (G : SimpleGraph V)
    (root : V) (hG : G.IsAcyclic) :
    (G.induce {v | G.Reachable root v}).IsTree := by
  have hsupp : (G.connectedComponentMk root).supp = {v | G.Reachable root v} := by
    ext v
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq, Set.mem_setOf_eq]
    exact SimpleGraph.reachable_comm
  have h := KltDP.Lattices.SmallForestComponents.component_isTree
    G hG (G.connectedComponentMk root)
  rw [hsupp] at h
  exact h

/-- The inverse of the actual component matrix is the corresponding block
of the full inverse, over any field. -/
theorem graph_component_inverse_eq
    {𝕜 : Type*} [Field 𝕜]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜) (root : V)
    [DecidablePred (G.Reachable root)]
    (hA : IsUnit (graphWeightMatrix G weight)) :
    (graphWeightMatrix (G.induce {v | G.Reachable root v})
      (fun v => weight v.val))⁻¹ =
        (graphWeightMatrix G weight)⁻¹.submatrix Subtype.val Subtype.val := by
  classical
  letI : Invertible (graphWeightMatrix G weight) := hA.invertible
  have hcut (p : Prop) [Decidable p] :
      ((if p then (0 : ℕ) else 1) < 1) ↔ p := by
    by_cases hp : p <;> simp [hp]
  have hinv := (graphWeightMatrix_component_triangular G weight root).inv_toBlock 1
  let p : V → Prop := fun v =>
    (@ite ℕ (G.Reachable root v) (G.instDecidableRelReachable root v) 0 1) < 1
  let e : {v | G.Reachable root v} ≃ {v | p v} :=
    (Equiv.subtypeEquivRight (fun v =>
      @hcut (G.Reachable root v) (G.instDecidableRelReachable root v))).symm
  change ((graphWeightMatrix G weight).toBlock p p)⁻¹ =
    (graphWeightMatrix G weight)⁻¹.toBlock p p at hinv
  have htransport : (((graphWeightMatrix G weight).toBlock p p).submatrix e e)⁻¹ =
      ((graphWeightMatrix G weight)⁻¹.toBlock p p).submatrix e e := by
    exact (Matrix.inv_submatrix_equiv ((graphWeightMatrix G weight).toBlock p p) e e).trans
      (congrArg (fun M : Matrix {v | p v} {v | p v} 𝕜 => M.submatrix e e) hinv)
  have hmatrix := graphWeightMatrix_submatrix
    (SimpleGraph.Embedding.induce (G := G) {v | G.Reachable root v}) weight
  change (graphWeightMatrix G weight).submatrix Subtype.val Subtype.val =
    graphWeightMatrix (G.induce {v | G.Reachable root v})
      (fun v => weight v.val) at hmatrix
  change ((graphWeightMatrix G weight).submatrix Subtype.val Subtype.val)⁻¹ =
    (graphWeightMatrix G weight)⁻¹.submatrix Subtype.val Subtype.val at htransport
  exact (congrArg
    (fun M : Matrix {v | G.Reachable root v} {v | G.Reachable root v} 𝕜 => M⁻¹)
    hmatrix).symm.trans htransport

/-- A wholly canonical component whose full diagonal Green entry is two
thirds is the two-vertex path, once its actual small-tree hypotheses hold. -/
theorem graph_canonical_component_iso_edge_of_green_two_thirds
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (root : V)
    [DecidablePred (G.Reachable root)]
    (hA : IsUnit (graphWeightMatrix G weight))
    (hcanonical : ∀ v, G.Reachable root v → weight v = 2)
    (hG : (G.induce {v | G.Reachable root v}).IsTree)
    (hedges : (G.induce {v | G.Reachable root v}).edgeFinset.card ≤ 3)
    (hgreen : (graphWeightMatrix G weight)⁻¹ root root = 2 / 3) :
    ∃ e : G.induce {v | G.Reachable root v} ≃g rootedBlockGraph (.arms .endEdge),
      e ⟨root, SimpleGraph.Reachable.refl root⟩ = rootedBlockRoot (.arms .endEdge) := by
  classical
  let root' : {v | G.Reachable root v} := ⟨root, SimpleGraph.Reachable.refl root⟩
  have hmatrix : graphWeightMatrix (G.induce {v | G.Reachable root v})
      (fun v => weight v.val) =
      rootedGraphMatrix (G.induce {v | G.Reachable root v}) root' (2 : ℚ) := by
    ext i j
    simp only [graphWeightMatrix_apply, rootedGraphMatrix, hcanonical i.val i.property,
      ite_self]
  have hinv := graph_component_inverse_eq G weight root hA
  have hentry := congrArg (fun M => M root' root') hinv
  rw [hmatrix] at hentry
  apply canonical_tree_iso_edge_of_green_two_thirds _ root' hG hedges
  exact hentry.trans hgreen

/-- The ambient forest hypotheses themselves supply the component tree
and edge bounds required by the canonical Green classification. -/
theorem graph_forest_canonical_component_iso_edge_of_green_two_thirds
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (root : V)
    [DecidablePred (G.Reachable root)]
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hedges : G.edgeFinset.card ≤ 3)
    (hcanonical : ∀ v, G.Reachable root v → weight v = 2)
    (hgreen : (graphWeightMatrix G weight)⁻¹ root root = 2 / 3) :
    (∃ e : G.induce {v | G.Reachable root v} ≃g rootedBlockGraph (.arms .endEdge),
      e ⟨root, SimpleGraph.Reachable.refl root⟩ = rootedBlockRoot (.arms .endEdge)) ∧
      (G.induce {v | G.Reachable root v}).edgeFinset.card = 1 := by
  obtain ⟨e, he⟩ := graph_canonical_component_iso_edge_of_green_two_thirds
    G weight root hA hcanonical (graph_reachable_component_isTree G root hG)
    ((graph_induce_edge_card_le G _).trans hedges) hgreen
  refine ⟨⟨e, he⟩, ?_⟩
  rw [← rootedBlockEdges_eq_of_iso e]
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ]

end KltDP.LinearAlgebra
