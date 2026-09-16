import KltDP.LinearAlgebra.GraphComponentInverse
import KltDP.LinearAlgebra.SingleExtraComponent

/-!
# The actual closed edge forced by a canonical Green entry

The small-tree inverse classification supplies an isomorphism of an actual
connected component. This file recovers its two vertices inside the original
graph, their singleton neighbor finsets, and the exact reachability set.

The degree transport uses pinned Mathlib's `Iso.mapNeighborSet` and
`degree_induce_of_neighborSet_subset`. The numerical value two thirds is
used through the preceding component classification; no component shape or
absence of further neighbors is assumed.
-/

namespace KltDP.LinearAlgebra

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both vertices of the concrete two-vertex rooted path have degree one. -/
theorem rootedBlock_endEdge_degree_one :
    ∀ v, (rootedBlockGraph (.arms .endEdge)).degree v = 1 := by
  decide

/-- An actual component isomorphic to the two-vertex path determines a
closed edge in the ambient graph, including all of its neighbors. -/
theorem component_iso_edge_has_mutual_singleton_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    [DecidablePred (G.Reachable root)]
    (e : G.induce {v | G.Reachable root v} ≃g rootedBlockGraph (.arms .endEdge)) :
    ∃ M, G.Adj root M ∧ G.neighborFinset root = {M} ∧
      G.neighborFinset M = {root} ∧
      ∀ v, G.Reachable root v ↔ v = root ∨ v = M := by
  classical
  have hdegree (v : V) (hv : G.Reachable root v) : G.degree v = 1 := by
    have hinside : (G.induce {w | G.Reachable root w}).degree ⟨v, hv⟩ = 1 := by
      calc
        _ = (rootedBlockGraph (.arms .endEdge)).degree (e ⟨v, hv⟩) := by
          simpa only [SimpleGraph.card_neighborSet_eq_degree] using
            Fintype.card_congr (e.mapNeighborSet ⟨v, hv⟩)
        _ = 1 := rootedBlock_endEdge_degree_one _
    have hneighbors : G.neighborSet v ⊆ {w | G.Reachable root w} := by
      intro w hw
      exact hv.trans hw.reachable
    exact (G.degree_induce_of_neighborSet_subset (v := ⟨v, hv⟩) hneighbors).symm.trans
      hinside
  have hroot : (G.neighborFinset root).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hdegree root (SimpleGraph.Reachable.refl root)
  obtain ⟨M, hM⟩ := Finset.card_eq_one.mp hroot
  have hadj : G.Adj root M :=
    (G.mem_neighborFinset root M).mp (by rw [hM]; simp)
  have hMcard : (G.neighborFinset M).card = 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hdegree M hadj.reachable
  obtain ⟨C, hC⟩ := Finset.card_eq_one.mp hMcard
  have hrootC : root = C := by
    have h := (G.mem_neighborFinset M root).mpr hadj.symm
    rwa [hC, Finset.mem_singleton] at h
  have hnM : G.neighborFinset M = {root} := by
    simpa only [hrootC] using hC
  exact ⟨M, hadj, hM, hnM,
    reachable_iff_of_mutual_singleton_neighbors G root M hadj hM hnM⟩

/-- In the small ambient forest, a canonical component with diagonal
Green entry two thirds consists of one actual closed canonical edge. -/
theorem graph_canonical_green_two_thirds_closed_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (root : V)
    [DecidablePred (G.Reachable root)]
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hedges : G.edgeFinset.card ≤ 3)
    (hcanonical : ∀ v, G.Reachable root v → weight v = 2)
    (hgreen : (graphWeightMatrix G weight)⁻¹ root root = 2 / 3) :
    ∃ M, G.Adj root M ∧ weight root = 2 ∧ weight M = 2 ∧
      G.neighborFinset root = {M} ∧ G.neighborFinset M = {root} ∧
      ∀ v, G.Reachable root v ↔ v = root ∨ v = M := by
  obtain ⟨⟨e, _⟩, _⟩ :=
    graph_forest_canonical_component_iso_edge_of_green_two_thirds
      G weight root hA hG hedges hcanonical hgreen
  obtain ⟨M, hadj, hroot, hM, hreach⟩ :=
    component_iso_edge_has_mutual_singleton_neighbors G root e
  exact ⟨M, hadj, hcanonical root (SimpleGraph.Reachable.refl root),
    hcanonical M hadj.reachable, hroot, hM, hreach⟩

end KltDP.LinearAlgebra
