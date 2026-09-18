import KltDP.Geometry.CurveIncidenceGraph
import KltDP.Topology.ConnectedClosedPartition

/-!
# Components of an actual intersection graph and of the original union

For a finite family of nonempty connected closed subsets, the connected
components of its intersection graph index the actual topological connected
components of the union. The blocks are constructed from graph reachability;
no partition, graph component count, or geometric fiber correspondence is
assumed. This applies in particular to actual exceptional prime curves.
-/

noncomputable section

open Set SimpleGraph

universe u v

namespace KltDP.Topology.IncidenceGraphComponents

variable {X : Type u} [TopologicalSpace X] {I : Type v} (s : I → Set X)

/-- The actual union of all pieces in one graph component. -/
def block (c : (incidenceGraph s).ConnectedComponent) : Set X :=
  ⋃ i : c.supp, s i.val

theorem block_subset_union (c : (incidenceGraph s).ConnectedComponent) :
    block s c ⊆ ⋃ i, s i := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i.val, hi⟩

/-- Intersections between two constructed blocks force their graph
components to be identical. -/
theorem blocks_disjoint :
    Pairwise (fun c d : (incidenceGraph s).ConnectedComponent =>
      Disjoint (block s c) (block s d)) := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hy
  have hi : (incidenceGraph s).connectedComponentMk i.val = c := i.property
  have hj : (incidenceGraph s).connectedComponentMk j.val = d := j.property
  have hij := incidenceGraph_reachable_of_inter s ⟨x, hxi, hxj⟩
  exact hcd (hi.symm.trans ((SimpleGraph.ConnectedComponent.sound hij).trans hj))

/-- Every constructed block is connected, by actual graph paths and the
connectedness of the original pieces. Finiteness is unnecessary here. -/
theorem block_connected (hs : ∀ i, IsConnected (s i))
    (c : (incidenceGraph s).ConnectedComponent) : IsConnected (block s c) := by
  letI : Nonempty c.supp := c.nonempty_supp.to_subtype
  change IsConnected (⋃ i : c.supp, s i.val)
  apply IsConnected.iUnion_of_reflTransGen (fun i : c.supp => hs i.val)
  intro i j
  exact Relation.ReflTransGen.mono
    (r := ((incidenceGraph s).induce c.supp).Adj)
    (fun _ _ h => h.2)
    ((((incidenceGraph s).induce c.supp).reachable_iff_reflTransGen i j).mp
      (c.connected_induce_supp i j))

/-- The same block viewed inside the original union with its induced topology. -/
def blockInUnion (c : (incidenceGraph s).ConnectedComponent) : Set (⋃ i, s i) :=
  Subtype.val ⁻¹' block s c

theorem blockInUnion_image (c : (incidenceGraph s).ConnectedComponent) :
    (Subtype.val : (⋃ i, s i) → X) '' blockInUnion s c = block s c := by
  rw [blockInUnion, Subtype.image_preimage_val,
    Set.inter_eq_right.mpr (block_subset_union s c)]

theorem blockInUnion_connected (hs : ∀ i, IsConnected (s i))
    (c : (incidenceGraph s).ConnectedComponent) : IsConnected (blockInUnion s c) := by
  have h : IsConnected ((Subtype.val : (⋃ i, s i) → X) '' blockInUnion s c) := by
    rw [blockInUnion_image]
    exact block_connected s hs c
  exact ⟨Set.image_nonempty.mp h.nonempty,
    _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp h.isPreconnected⟩

theorem blocksInUnion_disjoint :
    Pairwise (fun c d : (incidenceGraph s).ConnectedComponent =>
      Disjoint (blockInUnion s c) (blockInUnion s d)) := by
  intro c d hcd
  exact (blocks_disjoint s hcd).preimage Subtype.val

theorem blocksInUnion_cover :
    ⋃ c : (incidenceGraph s).ConnectedComponent, blockInUnion s c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp x.property
  refine Set.mem_iUnion.mpr ⟨(incidenceGraph s).connectedComponentMk i, ?_⟩
  exact Set.mem_iUnion.mpr ⟨⟨i, rfl⟩, hxi⟩

variable [Finite I]

theorem finite_graphComponents : Finite (incidenceGraph s).ConnectedComponent :=
  Finite.of_surjective (incidenceGraph s).connectedComponentMk (fun c => c.exists_rep)

theorem blockInUnion_closed (hc : ∀ i, IsClosed (s i))
    (c : (incidenceGraph s).ConnectedComponent) : IsClosed (blockInUnion s c) :=
  (isClosed_iUnion_of_finite (fun i : c.supp => hc i.val)).preimage continuous_subtype_val

/-- The finite graph-component partition yields a bijection with the
original topological connected-component quotient of the curve union. -/
def equiv (hc : ∀ i, IsClosed (s i)) (hs : ∀ i, IsConnected (s i)) :
    ConnectedComponents (⋃ i, s i) ≃ (incidenceGraph s).ConnectedComponent := by
  letI : Finite (incidenceGraph s).ConnectedComponent := finite_graphComponents s
  exact ConnectedClosedPartition.connectedComponentsEquiv (blockInUnion s)
    (blockInUnion_closed s hc) (blockInUnion_connected s hs)
    (blocksInUnion_disjoint s) (blocksInUnion_cover s)

/-- A point on an original piece goes to that piece's original graph component. -/
theorem equiv_mk (hc : ∀ i, IsClosed (s i)) (hs : ∀ i, IsConnected (s i))
    (i : I) (x : (⋃ i, s i)) (hx : x.val ∈ s i) :
    equiv s hc hs (ConnectedComponents.mk x) = (incidenceGraph s).connectedComponentMk i := by
  letI : Finite (incidenceGraph s).ConnectedComponent := finite_graphComponents s
  exact ConnectedClosedPartition.connectedComponentsEquiv_mk (blockInUnion s)
    (blockInUnion_closed s hc) (blockInUnion_connected s hs)
    (blocksInUnion_disjoint s) (blocksInUnion_cover s)
    ((incidenceGraph s).connectedComponentMk i) x
    (Set.mem_iUnion.mpr ⟨⟨i, rfl⟩, hx⟩)

theorem natCard_eq (hc : ∀ i, IsClosed (s i)) (hs : ∀ i, IsConnected (s i)) :
    Nat.card (ConnectedComponents (⋃ i, s i)) =
      Nat.card (incidenceGraph s).ConnectedComponent :=
  Nat.card_congr (equiv s hc hs)

end KltDP.Topology.IncidenceGraphComponents

#print axioms KltDP.Topology.IncidenceGraphComponents.equiv
