import KltDP.LinearAlgebra.RootedTreeCharges
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Exhaustion of rooted trees with at most three edges

The target graphs use Boolean adjacency on the vertices of the actual eight
matrices in `RootedTreeCharges`. A proved entrywise bridge identifies their
edges with the minus-one matrix entries. Their edge counts are proved to equal
the construction counts used there.

For an arbitrary finite tree, Mathlib's tree edge-count theorem bounds its
vertex count by four. Relabeling then reduces the classification to graphs on
`Fin n`, for `1 ≤ n ≤ 4`. An upper-triangular Boolean mask encodes every such
graph. The largest enumeration has six bits, hence 64 masks; it does not use
the much larger enumeration of arbitrary Boolean adjacency matrices.

The resulting isomorphism preserves the distinguished root. No assumption of
membership in the eight-element family occurs in the classification theorem.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- Computable adjacency of the listed constructions, using only arm labels
and natural-number positions. Its agreement with the rational matrices is
proved below, so finite graph searches do not evaluate matrix arithmetic. -/
def rootedBlockEdge : (choice : RootedBlockChoice) →
    RootedBlockVertex choice → RootedBlockVertex choice → Bool
  | .arms _, Sum.inl _, Sum.inl _ => false
  | .arms _, Sum.inl _, Sum.inr j => j.2.val == 0
  | .arms _, Sum.inr i, Sum.inl _ => i.2.val == 0
  | .arms _, Sum.inr i, Sum.inr j =>
      (i.1.val == j.1.val) && (i.2.val + 1 == j.2.val || j.2.val + 1 == i.2.val)
  | .leafStar, Sum.inl _, Sum.inl _ => false
  | .leafStar, Sum.inl _, Sum.inr j => j.val == 1
  | .leafStar, Sum.inr i, Sum.inl _ => i.val == 1
  | .leafStar, Sum.inr i, Sum.inr j => i.val + 1 == j.val || j.val + 1 == i.val

/-- The actual graph underlying a listed rational matrix, expressed through
the computable construction adjacency. -/
def rootedBlockGraph (choice : RootedBlockChoice) :
    SimpleGraph (RootedBlockVertex choice) :=
  SimpleGraph.fromRel (fun v w => rootedBlockEdge choice v w = true)

instance rootedBlockGraphDecidable (choice : RootedBlockChoice) :
    DecidableRel (rootedBlockGraph choice).Adj := by
  intro v w
  change Decidable (v ≠ w ∧
    (rootedBlockEdge choice v w = true ∨ rootedBlockEdge choice w v = true))
  infer_instance

/-- The Boolean graph has exactly the minus-one entries of the actual matrix
as its adjacencies. This also checks symmetry and the absence of loops. -/
theorem rootedBlockGraph_adj_iff :
    ∀ (choice : RootedBlockChoice) (v w : RootedBlockVertex choice),
      (rootedBlockGraph choice).Adj v w ↔ rootedBlockMatrix choice v w = (-1 : ℚ) := by
  intro choice
  cases choice with
  | arms shape =>
    cases shape <;> intro v w
    all_goals
      fin_cases v <;> fin_cases w <;>
        norm_num [rootedBlockGraph, rootedBlockEdge, rootedBlockMatrix,
          rootedArmMatrix, rootedStarMatrix, armSpokes, chainArms,
          weightTwoChain_apply, Matrix.blockDiagonal'_apply,
          Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals
      simp [Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inr.injEq,
        Sigma.mk.inj_iff, Fin.ext_iff, rootedArmLengths]
    all_goals
      intro h
      have hpos := congrArg (fun (p : ArmIndex _) => p.2.val) (Sum.inr.inj h)
      norm_num [rootedArmLengths] at hpos
  | leafStar =>
    intro v w
    fin_cases v <;> fin_cases w <;>
      norm_num [rootedBlockGraph, rootedBlockEdge, rootedBlockMatrix,
        leafRootedStarMatrix, weightTwoChain_apply, Pi.single_apply,
        Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals
      try simp [Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inr.injEq, Fin.ext_iff]
    all_goals
      first
      | decide
      | intro h
        have hpos := congrArg (fun (i : Fin 3) => i.val) (Sum.inr.inj h)
        norm_num at hpos

/-- The construction-edge budget is the cardinality of the actual graph's
edge set, rather than merely a count assigned to a shape name. -/
theorem rootedBlockGraph_edge_count : ∀ choice : RootedBlockChoice,
    (rootedBlockGraph choice).edgeFinset.card = rootedBlockEdges choice := by
  decide

/-- Every listed graph is connected, including the one-vertex graph. -/
theorem rootedBlockGraph_connected : ∀ choice : RootedBlockChoice,
    (rootedBlockGraph choice).Connected := by
  decide

/-- An upper-triangular coordinate represents one unordered non-loop edge. -/
abbrev UpperEdge (n : ℕ) := {pair : Fin n × Fin n // pair.1 < pair.2}

/-- At four vertices this is a Boolean function on six edge coordinates. -/
abbrev UpperEdgeMask (n : ℕ) := UpperEdge n → Bool

/-- The graph encoded by a Boolean choice for each upper-triangular edge. -/
def upperEdgeMaskGraph {n : ℕ} (mask : UpperEdgeMask n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun v w =>
    if h : v < w then mask ⟨(v, w), h⟩ = true else False)

instance upperEdgeMaskGraphDecidable {n : ℕ} (mask : UpperEdgeMask n) :
    DecidableRel (upperEdgeMaskGraph mask).Adj := by
  intro v w
  change Decidable (v ≠ w ∧
    ((if h : v < w then mask ⟨(v, w), h⟩ = true else False) ∨
      (if h : w < v then mask ⟨(w, v), h⟩ = true else False)))
  infer_instance

/-- Read every upper-triangular adjacency of an arbitrary finite graph. -/
def upperEdgeMaskOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    UpperEdgeMask n := fun edge => decide (G.Adj edge.1.1 edge.1.2)

/-- The mask representation includes every graph, with an equality proof.
It is not a restriction to a preselected family of examples. -/
theorem upperEdgeMaskGraph_of_graph {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : upperEdgeMaskGraph (upperEdgeMaskOfGraph G) = G := by
  ext v w
  by_cases hvw : v = w
  · subst w
    simp [upperEdgeMaskGraph, upperEdgeMaskOfGraph]
  · rcases lt_or_gt_of_ne hvw with hlt | hgt
    · have hnlt : ¬w < v := not_lt_of_ge (le_of_lt hlt)
      simp [upperEdgeMaskGraph, upperEdgeMaskOfGraph, hvw, hlt, hnlt]
    · have hnlt : ¬v < w := not_lt_of_ge (le_of_lt hgt)
      simpa [upperEdgeMaskGraph, upperEdgeMaskOfGraph, hvw, hgt, hnlt] using
        (show G.Adj w v ↔ G.Adj v w from ⟨fun h => G.symm h, fun h => G.symm h⟩)

/-- A finite search proposition with a genuine bijection and all adjacency
equivalences, including the distinguished root equation. -/
def HasListedRootedIso {n : ℕ} (mask : UpperEdgeMask n) (root : Fin n) : Prop :=
  ∃ choice : RootedBlockChoice, ∃ e : Fin n ≃ RootedBlockVertex choice,
    e root = rootedBlockRoot choice ∧
      ∀ v w, (upperEdgeMaskGraph mask).Adj v w ↔
        (rootedBlockGraph choice).Adj (e v) (e w)

instance hasListedRootedIsoDecidable {n : ℕ} (mask : UpperEdgeMask n) (root : Fin n) :
    Decidable (HasListedRootedIso mask root) := by
  unfold HasListedRootedIso
  infer_instance

private theorem classify_upper_mask_one : ∀ mask : UpperEdgeMask 1,
    (upperEdgeMaskGraph mask).edgeFinset.card + 1 = 1 →
      (upperEdgeMaskGraph mask).Connected → ∀ root : Fin 1, HasListedRootedIso mask root := by
  decide

private theorem classify_upper_mask_two : ∀ mask : UpperEdgeMask 2,
    (upperEdgeMaskGraph mask).edgeFinset.card + 1 = 2 →
      (upperEdgeMaskGraph mask).Connected → ∀ root : Fin 2, HasListedRootedIso mask root := by
  decide

private theorem classify_upper_mask_three : ∀ mask : UpperEdgeMask 3,
    (upperEdgeMaskGraph mask).edgeFinset.card + 1 = 3 →
      (upperEdgeMaskGraph mask).Connected → ∀ root : Fin 3, HasListedRootedIso mask root := by
  decide

private theorem classify_upper_mask_four : ∀ mask : UpperEdgeMask 4,
    (upperEdgeMaskGraph mask).edgeFinset.card + 1 = 4 →
      (upperEdgeMaskGraph mask).Connected → ∀ root : Fin 4, HasListedRootedIso mask root := by
  decide

/-- Exhaustive finite certificate on all masks at every allowed vertex count.
Connectedness and the tree cardinality identity are checked hypotheses. -/
theorem classify_upper_mask {n : ℕ} (hpos : 0 < n) (hn : n ≤ 4)
    (mask : UpperEdgeMask n) (hcard : (upperEdgeMaskGraph mask).edgeFinset.card + 1 = n)
    (hconn : (upperEdgeMaskGraph mask).Connected) (root : Fin n) :
    HasListedRootedIso mask root := by
  interval_cases n
  · exact classify_upper_mask_one mask hcard hconn root
  · exact classify_upper_mask_two mask hcard hconn root
  · exact classify_upper_mask_three mask hcard hconn root
  · exact classify_upper_mask_four mask hcard hconn root

/-- Finite graph isomorphisms transport the tree property via connectedness
and the edge/vertex cardinality identity. -/
theorem isTree_of_graphIso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (hG : G.IsTree) : H.IsTree := by
  have hcardG := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨e.connected_iff.mp hG.isConnected, ?_⟩
  rw [← Nat.card_congr e.mapEdgeSet, ← Nat.card_congr e.toEquiv]
  exact hcardG

/-- The vertex bound is derived from the actual tree and its actual edges. -/
theorem smallTree_vertex_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    Fintype.card V ≤ 4 := by
  have hcard := hG.card_edgeFinset
  omega

/-- Every finite rooted tree with at most three edges is root-preservingly
isomorphic to one of the eight graphs from the actual manuscript matrices. -/
theorem smallRootedTree_classification {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) (root : V) :
    ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
      e root = rootedBlockRoot choice := by
  classical
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  have hbound := smallTree_vertex_bound hG hedges
  let H := G.overFin (rfl : Fintype.card V = Fintype.card V)
  let e : G ≃g H := G.overFinIso rfl
  let mask := upperEdgeMaskOfGraph H
  have hdecode : upperEdgeMaskGraph mask = H := upperEdgeMaskGraph_of_graph H
  have hTreeH : H.IsTree := isTree_of_graphIso e hG
  have hTreeMask : (upperEdgeMaskGraph mask).IsTree := by
    rw [hdecode]
    exact hTreeH
  have hcard : (upperEdgeMaskGraph mask).edgeFinset.card + 1 = Fintype.card V := by
    simpa only [Fintype.card_fin] using hTreeMask.card_edgeFinset
  obtain ⟨choice, f, hroot, hadj⟩ :=
    classify_upper_mask hpos hbound mask hcard hTreeMask.isConnected (e root)
  let g : H ≃g rootedBlockGraph choice :=
    { toEquiv := f
      map_rel_iff' := by
        intro v w
        have h := hadj v w
        rw [hdecode] at h
        exact h.symm }
  refine ⟨choice, e.trans g, ?_⟩
  exact hroot

/-- An isomorphism to a listed graph also preserves the exact edge budget
used by the charge-set calculations. -/
theorem rootedBlockEdges_eq_of_iso {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] {choice : RootedBlockChoice} (e : G ≃g rootedBlockGraph choice) :
    rootedBlockEdges choice = G.edgeFinset.card := by
  rw [← rootedBlockGraph_edge_count, SimpleGraph.edgeFinset_card,
    SimpleGraph.edgeFinset_card]
  exact (Fintype.card_congr e.mapEdgeSet).symm

end KltDP.LinearAlgebra
