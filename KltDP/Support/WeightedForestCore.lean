import KltDP.Lattices.SmallADEForestDecomposition
import KltDP.Manuscript.S09.RootedTrees
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Tactic

/-!
# A01: the independent finite weighted-forest core

Supporting obligation A01 (`planning/AUTOFORMALIZATION_PLAN.md` §6 "A01",
`planning/THEOREM_MAP.json` id A01; the planned export `KltDP.Arithmetic.a01`
is provided here as `KltDP.Support.a01`). Everything is finite graph
combinatorics on Mathlib's `SimpleGraph`; no surface, divisor, or incidence
graph is constructed or assumed.

* `WeightedForest V`: a simple graph on the finite type `V` with decidable
  adjacency, natural weights `≥ 2`, a proof of acyclicity, and three
  distinguished pairwise distinct vertices `mark : Fin 3 → V`.
* `LabeledIso F F'`: a graph isomorphism preserving weights and the three
  marks. `LabeledIso.refl`, `symm`, `trans` and `labeledIsomorphic_equivalence`
  make labeled isomorphism an equivalence relation; `LabeledIso.card_vertices`,
  `card_edges`, `card_components`, `weight_multiset`, `card_weight_fiber` are
  the invariants (vertex count, edge count, connected-component count, the
  multiset of weights, and each weight fiber).
* `forest_card_edges`: for an acyclic finite simple graph,
  `#edges + #components = #vertices`, derived from the pinned tree edge count
  (`SimpleGraph.isTree_iff_connected_and_card`) applied to each component
  through the accepted `component_isTree`; the edges are distributed over the
  components by counting darts (`componentDartEquiv`, pinned
  `dart_card_eq_twice_card_edges`).
* `deleteVertex_card_components`: deleting a vertex `v` from a forest gives
  `#components(G - v) + 1 = #components(G) + degree v` (the `s_C` pieces of
  manuscript Theorem 4.5, `thm:one-component-replacement`, `source/manuscript.tex`
  line 1034), with `G - v := G.induce {v}ᶜ`; `deleteVertex_card_edges` is the
  edge count `#edges(G - v) + degree v = #edges(G)`.
* Re-exports of the accepted rooted-tree shape classification
  (`rootedTree_shapes_le_three_edges`, `rootedTree_shapes_isTree_le_three_edges`,
  `card_rootedTree_shapes`, `smallTree_component_classification`) and of the
  rank/partition enumeration (`rankPartition_enumeration`,
  `rankPartition_count_bounds`, `forest_rankPartition_rows`).
* `a01` bundles the clauses.

Not proved here: nothing of the A01 goal is omitted. The structure carries
`[Fintype V]` as a parameter; decidable equality of vertices is assumed only
where edge finsets or component counts are formed.
-/

universe u w

namespace KltDP.Support

open SimpleGraph Finset

/-! ### Weighted forests with three marks -/

/-- A finite simple weighted forest with three distinguished vertices: a
simple graph with decidable adjacency on the finite type `V`, natural weights
at least two, a proof of acyclicity, and an injective `mark : Fin 3 → V`. -/
structure WeightedForest (V : Type u) [Fintype V] where
  /-- The underlying simple graph (symmetric, irreflexive adjacency). -/
  graph : SimpleGraph V
  /-- Adjacency is decidable. -/
  decAdj : DecidableRel graph.Adj
  /-- The weight of each vertex. -/
  weight : V → ℕ
  /-- Every weight is at least two. -/
  two_le_weight : ∀ v, 2 ≤ weight v
  /-- The graph is a forest. -/
  acyclic : graph.IsAcyclic
  /-- The three distinguished vertices. -/
  mark : Fin 3 → V
  /-- The three distinguished vertices are pairwise distinct. -/
  mark_injective : Function.Injective mark

/-- Adjacency in a weighted forest is decidable (the structure field as an instance). -/
instance WeightedForest.instDecidableRelAdj {V : Type u} [Fintype V] (F : WeightedForest V) :
    DecidableRel F.graph.Adj :=
  F.decAdj

namespace WeightedForest

variable {V : Type u} [Fintype V] (F : WeightedForest V)

theorem mark_ne {i j : Fin 3} (h : i ≠ j) : F.mark i ≠ F.mark j :=
  fun h' => h (F.mark_injective h')

theorem mark_zero_ne_one : F.mark 0 ≠ F.mark 1 := F.mark_ne (by decide)

theorem mark_zero_ne_two : F.mark 0 ≠ F.mark 2 := F.mark_ne (by decide)

theorem mark_one_ne_two : F.mark 1 ≠ F.mark 2 := F.mark_ne (by decide)

include F in
/-- The three marks force at least three vertices. -/
theorem three_le_card : 3 ≤ Fintype.card V :=
  le_of_eq_of_le (Fintype.card_fin 3).symm (Fintype.card_le_of_injective _ F.mark_injective)

end WeightedForest

/-- A labeled isomorphism of weighted forests: a graph isomorphism preserving
the weights and the three marks. -/
structure LabeledIso {V : Type u} {W : Type w} [Fintype V] [Fintype W]
    (F : WeightedForest V) (F' : WeightedForest W) where
  /-- The underlying graph isomorphism. -/
  toIso : F.graph ≃g F'.graph
  /-- Weights are preserved. -/
  weight_map : ∀ v, F'.weight (toIso v) = F.weight v
  /-- The three marks are preserved in order. -/
  mark_map : ∀ i, toIso (F.mark i) = F'.mark i

namespace LabeledIso

variable {V : Type u} {W : Type w} {X : Type*} [Fintype V] [Fintype W] [Fintype X]
  {F : WeightedForest V} {F' : WeightedForest W} {F'' : WeightedForest X}

/-- The identity labeled isomorphism. -/
def refl (F : WeightedForest V) : LabeledIso F F :=
  ⟨Iso.refl, fun _ => rfl, fun _ => rfl⟩

/-- The inverse of a labeled isomorphism. -/
def symm (e : LabeledIso F F') : LabeledIso F' F where
  toIso := e.toIso.symm
  weight_map w := by
    rw [← e.weight_map (e.toIso.symm w), RelIso.apply_symm_apply]
  mark_map i := by
    rw [← e.mark_map i, RelIso.symm_apply_apply]

/-- Composition of labeled isomorphisms. -/
def trans (e : LabeledIso F F') (e' : LabeledIso F' F'') : LabeledIso F F'' where
  toIso := e.toIso.trans e'.toIso
  weight_map v := by
    show F''.weight (e'.toIso (e.toIso v)) = F.weight v
    rw [e'.weight_map, e.weight_map]
  mark_map i := by
    show e'.toIso (e.toIso (F.mark i)) = F''.mark i
    rw [e.mark_map, e'.mark_map]

/-- Labeled isomorphism preserves the vertex count. -/
theorem card_vertices (e : LabeledIso F F') : Fintype.card V = Fintype.card W :=
  Fintype.card_congr e.toIso.toEquiv

/-- Labeled isomorphism preserves the edge count. -/
theorem card_edges [DecidableEq V] [DecidableEq W] (e : LabeledIso F F') :
    F.graph.edgeFinset.card = F'.graph.edgeFinset.card := by
  rw [edgeFinset_card, edgeFinset_card]
  exact Fintype.card_congr e.toIso.mapEdgeSet

/-- Labeled isomorphism preserves the number of connected components. -/
theorem card_components [DecidableEq V] [DecidableEq W] (e : LabeledIso F F') :
    Fintype.card F.graph.ConnectedComponent = Fintype.card F'.graph.ConnectedComponent :=
  Fintype.card_congr e.toIso.connectedComponentEquiv

/-- Labeled isomorphism preserves each weight fiber. -/
theorem card_weight_fiber (e : LabeledIso F F') (n : ℕ) :
    Fintype.card {v : V // F.weight v = n} = Fintype.card {w : W // F'.weight w = n} :=
  Fintype.card_congr (e.toIso.toEquiv.subtypeEquiv fun v => by
    rw [RelIso.coe_fn_toEquiv, e.weight_map])

/-- Labeled isomorphism preserves the multiset of weights. -/
theorem weight_multiset (e : LabeledIso F F') :
    (Finset.univ : Finset V).val.map F.weight = (Finset.univ : Finset W).val.map F'.weight := by
  have h1 : (Finset.univ : Finset V).val.map F.weight =
      (Finset.univ : Finset V).val.map (fun v => F'.weight (e.toIso v)) :=
    Multiset.map_congr rfl (fun v _ => (e.weight_map v).symm)
  have h2 : ((Finset.univ : Finset V).map e.toIso.toEquiv.toEmbedding).val =
      (Finset.univ : Finset W).val := by
    rw [Finset.map_univ_equiv]
  rw [Finset.map_val] at h2
  rw [h1, ← h2, Multiset.map_map]
  rfl

end LabeledIso

/-- Two weighted forests on the same vertex type are labeled isomorphic when a
labeled isomorphism exists. -/
def LabeledIsomorphic {V : Type u} [Fintype V] (F F' : WeightedForest V) : Prop :=
  Nonempty (LabeledIso F F')

/-- Labeled isomorphism is an equivalence relation. -/
theorem labeledIsomorphic_equivalence {V : Type u} [Fintype V] :
    Equivalence (LabeledIsomorphic (V := V)) where
  refl F := ⟨LabeledIso.refl F⟩
  symm := fun ⟨e⟩ => ⟨e.symm⟩
  trans := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩

/-- An explicit weighted forest: three isolated vertices of weight two, each
marked. -/
def threeIsolatedPoints : WeightedForest (Fin 3) where
  graph := ⊥
  decAdj := inferInstance
  weight := fun _ => 2
  two_le_weight := fun _ => le_rfl
  acyclic := isAcyclic_bot
  mark := id
  mark_injective := Function.injective_id

/-! ### Edge counting in a forest -/

namespace WeightedForestCore

variable {V : Type u} (G : SimpleGraph V)

/-- The darts of `G` with tail in the component `c`, as darts of the graph
induced on the support of `c`. -/
def componentDartEquiv (c : G.ConnectedComponent) :
    {d : G.Dart // G.connectedComponentMk d.fst = c} ≃ (G.induce c.supp).Dart where
  toFun d := ⟨(⟨d.1.fst, d.2⟩, ⟨d.1.snd, (ConnectedComponent.sound d.1.adj.reachable).symm.trans d.2⟩),
    d.1.adj⟩
  invFun d := ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The darts of `G` avoiding the vertex `v`, as darts of `G - v`. -/
def deleteVertexDartEquiv (v : V) :
    {d : G.Dart // d.fst ≠ v ∧ d.snd ≠ v} ≃ (G.induce ({v}ᶜ : Set V)).Dart where
  toFun d := ⟨(⟨d.1.fst, d.2.1⟩, ⟨d.1.snd, d.2.2⟩), d.1.adj⟩
  invFun d := ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2, d.snd.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Twice the edge count is the dart count (pinned `dart_card_eq_twice_card_edges`),
in instance-free form. -/
theorem natCard_dart : Nat.card G.Dart = 2 * Nat.card G.edgeSet := by
  have h := dart_card_eq_twice_card_edges (G := G)
  rw [edgeFinset_card] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h using 3

/-- Darts are distributed over the connected components. -/
theorem natCard_dart_eq_sum :
    Nat.card G.Dart = ∑ c : G.ConnectedComponent, Nat.card (G.induce c.supp).Dart := by
  classical
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv fun d : G.Dart => G.connectedComponentMk d.fst),
    Nat.card_sigma]
  exact Finset.sum_congr rfl fun c _ => Nat.card_congr (componentDartEquiv G c)

/-- Vertices are distributed over the connected components. -/
theorem natCard_vertices_eq_sum :
    Nat.card V = ∑ c : G.ConnectedComponent, Nat.card c.supp := by
  classical
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk), Nat.card_sigma]
  exact Finset.sum_congr rfl fun c _ =>
    Nat.card_congr (Equiv.subtypeEquivRight fun v => (ConnectedComponent.mem_supp_iff c v).symm)

/-- `#edges + #components = #vertices` for a finite forest, in `Nat.card` form. -/
theorem forest_natCard_edges (hG : G.IsAcyclic) :
    Nat.card G.edgeSet + Nat.card G.ConnectedComponent = Nat.card V := by
  classical
  have hdart := natCard_dart_eq_sum G
  have hsum : ∀ c : G.ConnectedComponent,
      Nat.card (G.induce c.supp).Dart = 2 * Nat.card (G.induce c.supp).edgeSet :=
    fun c => natCard_dart (G.induce c.supp)
  have htree : ∀ c : G.ConnectedComponent,
      Nat.card (G.induce c.supp).edgeSet + 1 = Nat.card c.supp :=
    fun c => (isTree_iff_connected_and_card.mp
      (KltDP.Lattices.SmallForestComponents.component_isTree G hG c)).2
  have hV := natCard_vertices_eq_sum G
  have hE : Nat.card G.edgeSet =
      ∑ c : G.ConnectedComponent, Nat.card (G.induce c.supp).edgeSet := by
    have h2 : 2 * Nat.card G.edgeSet =
        2 * ∑ c : G.ConnectedComponent, Nat.card (G.induce c.supp).edgeSet := by
      rw [← natCard_dart G, hdart, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => hsum c
    omega
  have hsumtree : ∑ c : G.ConnectedComponent, (Nat.card (G.induce c.supp).edgeSet + 1) =
      ∑ c : G.ConnectedComponent, Nat.card c.supp :=
    Finset.sum_congr rfl fun c _ => htree c
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsumtree
  rw [hE, hV, Nat.card_eq_fintype_card]
  exact hsumtree

/-- **Forest edge count.** For an acyclic finite simple graph,
`#edges + #components = #vertices`. -/
theorem forest_card_edges (hG : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V := by
  have h := forest_natCard_edges G hG
  simp only [Nat.card_eq_fintype_card] at h
  rw [edgeFinset_card]
  convert h using 3

omit [DecidableEq V] in
/-- A tree has one component, so the forest count specializes to the pinned
tree edge count. -/
theorem tree_card_edges (hG : G.IsTree) : G.edgeFinset.card + 1 = Fintype.card V :=
  hG.card_edgeFinset

/-! ### Deleting a vertex -/

/-- The darts of `G` split into those avoiding `v` and the `2 · degree v` darts
incident to `v`. -/
theorem card_dart_deleteVertex (v : V) :
    Fintype.card G.Dart = Fintype.card (G.induce ({v}ᶜ : Set V)).Dart + 2 * G.degree v := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset G.Dart)) (fun d : G.Dart => d.fst ≠ v ∧ d.snd ≠ v)
  rw [Finset.card_univ] at hsplit
  have havoid : (Finset.univ.filter fun d : G.Dart => d.fst ≠ v ∧ d.snd ≠ v).card =
      Fintype.card (G.induce ({v}ᶜ : Set V)).Dart := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (deleteVertexDartEquiv G v)
  have hinc : (Finset.univ.filter fun d : G.Dart => ¬ (d.fst ≠ v ∧ d.snd ≠ v)).card =
      2 * G.degree v := by
    have hor : (Finset.univ.filter fun d : G.Dart => ¬ (d.fst ≠ v ∧ d.snd ≠ v)) =
        (Finset.univ.filter fun d : G.Dart => d.fst = v) ∪
          (Finset.univ.filter fun d : G.Dart => d.snd = v) := by
      rw [← Finset.filter_or]
      exact Finset.filter_congr fun d _ => by simp only [not_and_or, ne_eq, not_not]
    have hdisj : Disjoint (Finset.univ.filter fun d : G.Dart => d.fst = v)
        (Finset.univ.filter fun d : G.Dart => d.snd = v) := by
      rw [Finset.disjoint_filter]
      intro d _ h1 h2
      exact d.fst_ne_snd (h1.trans h2.symm)
    have hsnd : (Finset.univ.filter fun d : G.Dart => d.snd = v).card = G.degree v := by
      rw [← G.dart_fst_fiber_card_eq_degree v, ← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr
        ((Function.Involutive.toPerm _ (Dart.symm_involutive (G := G))).subtypeEquiv
          fun d => Iff.rfl)
    rw [hor, Finset.card_union_of_disjoint hdisj, G.dart_fst_fiber_card_eq_degree v, hsnd]
    ring
  omega

/-- Deleting a vertex removes exactly its `degree v` incident edges. -/
theorem deleteVertex_card_edges (v : V) :
    (G.induce ({v}ᶜ : Set V)).edgeFinset.card + G.degree v = G.edgeFinset.card := by
  have h := card_dart_deleteVertex G v
  rw [dart_card_eq_twice_card_edges, dart_card_eq_twice_card_edges] at h
  omega

/-- Deleting a vertex from a finite type removes one element. -/
theorem card_compl_singleton_add_one (v : V) :
    Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
  have h1 : Fintype.card ({v} : Set V) = 1 := by
    convert Set.card_singleton v
  have h2 := Fintype.card_compl_set ({v} : Set V)
  have h3 : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- **Subtree contraction count.** Deleting a vertex `v` of a forest leaves a
forest with `degree v - 1` more components:
`#components(G - v) + 1 = #components(G) + degree v`. -/
theorem deleteVertex_card_components (hG : G.IsAcyclic) (v : V) :
    Fintype.card (G.induce ({v}ᶜ : Set V)).ConnectedComponent + 1 =
      Fintype.card G.ConnectedComponent + G.degree v := by
  have h1 := forest_card_edges G hG
  have h2 := forest_card_edges (G.induce ({v}ᶜ : Set V))
    (KltDP.Lattices.SmallForestComponents.isAcyclic_induce G hG _)
  have h3 := deleteVertex_card_edges G v
  have h4 := card_compl_singleton_add_one v
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The deleted graph is again a forest (accepted `isAcyclic_induce`). -/
theorem deleteVertex_isAcyclic (hG : G.IsAcyclic) (v : V) :
    (G.induce ({v}ᶜ : Set V)).IsAcyclic :=
  KltDP.Lattices.SmallForestComponents.isAcyclic_induce G hG _

end WeightedForestCore

namespace WeightedForest

variable {V : Type u} [Fintype V] [DecidableEq V] (F : WeightedForest V)

/-- `#edges + #components = #vertices` for a weighted forest. -/
theorem card_edges_add_card_components :
    F.graph.edgeFinset.card + Fintype.card F.graph.ConnectedComponent = Fintype.card V :=
  WeightedForestCore.forest_card_edges F.graph F.acyclic

/-- Vertex deletion in a weighted forest. -/
theorem deleteVertex_card_components (v : V) :
    Fintype.card (F.graph.induce ({v}ᶜ : Set V)).ConnectedComponent + 1 =
      Fintype.card F.graph.ConnectedComponent + F.graph.degree v :=
  WeightedForestCore.deleteVertex_card_components F.graph F.acyclic v

end WeightedForest

/-! ### Re-exports: rooted tree shapes with at most three edges -/

open KltDP.LinearAlgebra in
/-- Every finite rooted tree with at most three edges is root-preservingly
isomorphic to one of the eight listed shapes (accepted
`KltDP.LinearAlgebra.smallRootedTree_classification`). -/
theorem rootedTree_shapes_le_three_edges {V : Type*} [Fintype V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) (root : V) :
    ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
      e root = rootedBlockRoot choice :=
  smallRootedTree_classification hG hedges root

open KltDP.LinearAlgebra in
/-- Each listed shape has at most three edges. -/
theorem rootedBlockEdges_le_three (choice : RootedBlockChoice) : rootedBlockEdges choice ≤ 3 := by
  cases choice with
  | arms shape =>
    cases shape <;> norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ]
  | leafStar => norm_num [rootedBlockEdges]

open KltDP.LinearAlgebra in
/-- Each listed shape is a tree with at most three edges (accepted
`KltDP.Manuscript.S09.rootedTrees_listed_isTree`, `rootedBlockGraph_edge_count`). -/
theorem rootedTree_shapes_isTree_le_three_edges (choice : RootedBlockChoice) :
    (rootedBlockGraph choice).IsTree ∧ (rootedBlockGraph choice).edgeFinset.card ≤ 3 :=
  ⟨KltDP.Manuscript.S09.rootedTrees_listed_isTree choice,
    (rootedBlockGraph_edge_count choice).le.trans (rootedBlockEdges_le_three choice)⟩

open KltDP.LinearAlgebra in
/-- There are exactly eight listed shapes. -/
theorem card_rootedTree_shapes : Fintype.card RootedBlockChoice = 8 := by
  decide

open KltDP.LinearAlgebra in
/-- A tree with at most three edges has at most four vertices and valency at
most three (accepted `smallTree_vertex_bound`, `rootedTrees_valency`). -/
theorem rootedTree_le_three_edges_bounds {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    Fintype.card V ≤ 4 ∧ ∀ v, G.degree v ≤ 3 :=
  ⟨smallTree_vertex_bound hG hedges, fun v => KltDP.Manuscript.S09.rootedTrees_valency G hG hedges v⟩

/-- Every finite tree with at most four vertices is isomorphic to one of the five
`A1, A2, A3, A4, D4` component graphs (accepted
`KltDP.Lattices.SmallADEGraphs.smallTree_component_classification`). -/
theorem smallTree_component_classification {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (hcard : Fintype.card V ≤ 4) :
    ∃ k : KltDP.Lattices.SmallADEMatrices.Kind,
      Nonempty (G ≃g KltDP.Lattices.SmallADEGraphs.componentGraph k) :=
  KltDP.Lattices.SmallADEGraphs.smallTree_component_classification G hG hcard

/-! ### Re-exports: rank/partition enumeration -/

open KltDP.Lattices.SmallADEPartitions in
/-- The eight rank-eight count partitions with at least five components
(accepted `mem_rankEightRows_iff`). -/
theorem rankPartition_enumeration (c : Counts) :
    c ∈ rankEightRows ↔ c.rank = 8 ∧ 5 ≤ c.components :=
  mem_rankEightRows_iff c

open KltDP.Lattices.SmallADEPartitions in
/-- Rank at most eight and at least five components bound every count
(accepted `count_bounds_of_small_rank`). -/
theorem rankPartition_count_bounds (c : Counts) (hrank : c.rank ≤ 8) (hcomp : 5 ≤ c.components) :
    c.a1 < 9 ∧ c.a2 < 4 ∧ c.a3 < 2 ∧ c.a4 < 2 ∧ c.d4 < 2 :=
  count_bounds_of_small_rank c hrank hcomp

open KltDP.Lattices KltDP.Lattices.SmallADEPartitions KltDP.Lattices.SmallADEGraphs
  KltDP.Lattices.SmallADEMatrices in
/-- An actual eight-vertex forest with at least five components realizes one of
the eight rank partitions, with its graph Cartan matrix and determinant
(accepted `SmallADEForestDecomposition.eight_vertex_forest_determinant_rows`). -/
theorem forest_rankPartition_rows {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ c : G.ConnectedComponent, Fintype c.supp]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V = 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent) :
    ∃ counts : Counts, ∃ e : V ≃ Vertex counts,
      (cartanMatrix counts).submatrix e e = graphCartanMatrix G ∧
      counts ∈ rankEightRows ∧
      (graphCartanMatrix G).det = (counts.rootDet : ℤ) :=
  SmallADEForestDecomposition.eight_vertex_forest_determinant_rows G hG hvertices hcomponents

/-! ### The bundle -/

open KltDP.LinearAlgebra KltDP.Lattices.SmallADEPartitions in
/-- **A01 core.** Labeled isomorphism of weighted forests is an equivalence
relation preserving vertex, edge and component counts and the weight multiset;
a finite forest satisfies `#edges + #components = #vertices`; deleting a vertex
`v` from a forest changes the component count by `degree v - 1`; every rooted
tree with at most three edges is one of the eight listed shapes, each of which
is a tree with at most three edges; and the rank-eight count partitions with at
least five components are exactly the eight listed rows. -/
theorem a01 :
    (∀ {V : Type u} [Fintype V], Equivalence (LabeledIsomorphic (V := V))) ∧
    (∀ {V : Type u} {W : Type w} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      (F : WeightedForest V) (F' : WeightedForest W), LabeledIso F F' →
        Fintype.card V = Fintype.card W ∧
        F.graph.edgeFinset.card = F'.graph.edgeFinset.card ∧
        Fintype.card F.graph.ConnectedComponent = Fintype.card F'.graph.ConnectedComponent ∧
        (Finset.univ : Finset V).val.map F.weight = (Finset.univ : Finset W).val.map F'.weight) ∧
    (∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card V) ∧
    (∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → ∀ v : V,
        Fintype.card (G.induce ({v}ᶜ : Set V)).ConnectedComponent + 1 =
          Fintype.card G.ConnectedComponent + G.degree v) ∧
    (∀ {V : Type u} [Fintype V] {G : SimpleGraph V} [Fintype G.edgeSet], G.IsTree →
      G.edgeFinset.card ≤ 3 → ∀ root : V,
        ∃ choice : RootedBlockChoice, ∃ e : G ≃g rootedBlockGraph choice,
          e root = rootedBlockRoot choice) ∧
    (∀ choice : RootedBlockChoice,
      (rootedBlockGraph choice).IsTree ∧ (rootedBlockGraph choice).edgeFinset.card ≤ 3) ∧
    Fintype.card RootedBlockChoice = 8 ∧
    (∀ c : Counts, c ∈ rankEightRows ↔ c.rank = 8 ∧ 5 ≤ c.components) :=
  ⟨fun {_} [_] => labeledIsomorphic_equivalence,
    fun _ _ e => ⟨e.card_vertices, e.card_edges, e.card_components, e.weight_multiset⟩,
    fun G _ hG => WeightedForestCore.forest_card_edges G hG,
    fun G _ hG v => WeightedForestCore.deleteVertex_card_components G hG v,
    fun hG hedges root => rootedTree_shapes_le_three_edges hG hedges root,
    fun choice => rootedTree_shapes_isTree_le_three_edges choice,
    card_rootedTree_shapes,
    fun c => rankPartition_enumeration c⟩

end KltDP.Support
