import KltDP.Lattices.SmallADEMatrices
import KltDP.Lattices.SmallForestComponents
import KltDP.LinearAlgebra.SmallRootedTrees
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Actual small-tree graphs and their integral Cartan matrices

This supplies the graph step in manuscript `lem:eight-curve-forest`, lines
1454–1456, and the analogous step in `prop:zero-adjoint`, lines 1522–1524.
An arbitrary finite tree with at most four vertices is isomorphic to one of
the actual `A1`, `A2`, `A3`, `A4`, or `D4` component graphs. Its integral
graph-defined matrix is identified with the corresponding existing matrix,
so its determinant is derived from that matrix rather than supplied as data.

The four path graphs reuse Mathlib's `pathGraph`; the `D4` graph is defined
from the integral star matrix. Exhaustion reuses the proved arbitrary rooted
tree classification and a finite certificate forgetting each of its eight
root placements. No geometric forest, count partition, Picard embedding,
or node-exclusion assertion is assumed or claimed in this module.

Reuse review: pinned Mathlib `SimpleGraph/Hasse.lean` supplies the path graphs
and their adjacency formula; `Acyclic.lean` supplies the edge/vertex identity;
`Matrix/Determinant/Basic.lean` supplies determinant invariance under an actual
equivalence. The newer official Hasse/Acyclic sources and the related
`iiis-lean/PositiveDefiniteTreeLattice` library were checked before this adapter.
This bounded search identified no compatible replacement for this five-shape
matrix classification at the current pin. No new external library or toolchain is imported.
All reused Mathlib sources are Apache 2.0.
-/

namespace KltDP.Lattices.SmallADEGraphs

open Matrix SimpleGraph KltDP.LinearAlgebra SmallADEMatrices

/-- The actual unrooted component graphs. The four paths are Mathlib graphs;
the star has the same center-and-leaf coordinates as the existing D4 matrix. -/
def componentGraph : (k : Kind) → SimpleGraph (KindVertex k)
  | .a1 => SimpleGraph.pathGraph 1
  | .a2 => SimpleGraph.pathGraph 2
  | .a3 => SimpleGraph.pathGraph 3
  | .a4 => SimpleGraph.pathGraph 4
  | .d4 => SimpleGraph.fromRel (fun v w => integerD4 v w = (-1 : ℤ))

instance componentGraphDecidable (k : Kind) : DecidableRel (componentGraph k).Adj := by
  cases k
  all_goals
    first
    | exact fun v w => decidable_of_iff
        (v.val + 1 = w.val ∨ w.val + 1 = v.val) SimpleGraph.pathGraph_adj.symm
    | intro v w
      change Decidable (v ≠ w ∧ (integerD4 v w = (-1 : ℤ) ∨ integerD4 w v = (-1 : ℤ)))
      infer_instance

/-- Each graph edge is exactly an entry minus one of its integral matrix. -/
theorem componentGraph_adj_iff : ∀ (k : Kind) (v w : KindVertex k),
    (componentGraph k).Adj v w ↔ componentMatrix k v w = (-1 : ℤ) := by
  decide

/-- The integral weight-two matrix defined from any actual simple graph. -/
def graphCartanMatrix {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Matrix V V ℤ :=
  fun v w => if v = w then 2 else if G.Adj v w then -1 else 0

/-- The full matrix, including zeros at every nonedge, agrees with the
existing component matrix. This is an entrywise finite integer certificate. -/
theorem graphCartanMatrix_componentGraph : ∀ k : Kind,
    graphCartanMatrix (componentGraph k) = componentMatrix k := by
  decide

/-- Forgetting the distinguished root identifies the eight rooted shapes
with the five unrooted shapes; both star root positions give D4. -/
def unrootedKind : RootedBlockChoice → Kind
  | .arms .point => .a1
  | .arms .endEdge => .a2
  | .arms .endTwo | .arms .middleTwo => .a3
  | .arms .endThree | .arms .innerThree => .a4
  | .arms .centerStar | .leafStar => .d4

private def HasComponentIso (choice : RootedBlockChoice) : Prop :=
  ∃ e : RootedBlockVertex choice ≃ KindVertex (unrootedKind choice),
    ∀ v w, (rootedBlockGraph choice).Adj v w ↔
      (componentGraph (unrootedKind choice)).Adj (e v) (e w)

private instance hasComponentIsoDecidable (choice : RootedBlockChoice) :
    Decidable (HasComponentIso choice) := by
  unfold HasComponentIso
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem all_rooted_choices_have_componentIso :
    ∀ choice : RootedBlockChoice, HasComponentIso choice := by
  decide

/-- The finite certificate produces a genuine graph isomorphism; no root
preservation is required when identifying the unrooted ADE component. -/
theorem rootedBlock_componentIso (choice : RootedBlockChoice) :
    Nonempty (rootedBlockGraph choice ≃g componentGraph (unrootedKind choice)) := by
  obtain ⟨e, hadj⟩ := all_rooted_choices_have_componentIso choice
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro v w
  exact (hadj v w).symm

/-- Graph isomorphisms preserve the actual integral weight-two matrices. -/
theorem graphCartanMatrix_submatrix {V W : Type*} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) :
    (graphCartanMatrix H).submatrix e.toEquiv e.toEquiv = graphCartanMatrix G := by
  ext v w
  have heq : e v = e w ↔ v = w := e.toEquiv.injective.eq_iff
  change graphCartanMatrix H (e v) (e w) = graphCartanMatrix G v w
  simp only [graphCartanMatrix, heq, e.map_adj_iff]

/-- Every actual finite tree on at most four vertices belongs to one of the
five component isomorphism classes, including the trivalent D4 star. -/
theorem smallTree_component_classification {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hcard : Fintype.card V ≤ 4) :
    ∃ k : Kind, Nonempty (G ≃g componentGraph k) := by
  obtain ⟨root⟩ := hG.isConnected.nonempty
  have hedges : G.edgeFinset.card ≤ 3 := by
    have h := hG.card_edgeFinset
    omega
  obtain ⟨choice, e, _⟩ := smallRootedTree_classification hG hedges root
  obtain ⟨f⟩ := rootedBlock_componentIso choice
  exact ⟨unrootedKind choice, ⟨e.trans f⟩⟩

/-- The graph classification identifies the actual integral matrix, its
rank/cardinality, and its determinant with the existing component matrix. -/
theorem smallTree_matrix_classification {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hcard : Fintype.card V ≤ 4) :
    ∃ k : Kind, ∃ e : G ≃g componentGraph k,
      (componentMatrix k).submatrix e.toEquiv e.toEquiv = graphCartanMatrix G ∧
      Fintype.card V = kindRank k ∧
      (graphCartanMatrix G).det = (kindDet k : ℤ) := by
  obtain ⟨k, ⟨e⟩⟩ := smallTree_component_classification G hG hcard
  have hmatrix : (componentMatrix k).submatrix e.toEquiv e.toEquiv = graphCartanMatrix G := by
    rw [← graphCartanMatrix_componentGraph]
    exact graphCartanMatrix_submatrix e
  refine ⟨k, e, hmatrix, ?_, ?_⟩
  · exact (Fintype.card_congr e.toEquiv).trans (card_kindVertex k)
  · rw [← hmatrix, Matrix.det_submatrix_equiv_self, det_componentMatrix]

/-- The five determinant rows now apply to an arbitrary actual small tree,
not only to natural counts or separately supplied chain blocks. -/
theorem smallTree_rank_determinant_table {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hcard : Fintype.card V ≤ 4) :
    (Fintype.card V, (graphCartanMatrix G).det) ∈
      ({(1, 2), (2, 3), (3, 4), (4, 5), (4, 4)} : Finset (ℕ × ℤ)) := by
  obtain ⟨k, _, _, hrank, hdet⟩ := smallTree_matrix_classification G hG hcard
  rw [hrank, hdet]
  cases k <;> norm_num [kindRank, kindDet]

/-- The negative intersection-sign matrix has the same absolute determinant. -/
theorem smallTree_negative_determinant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (hcard : Fintype.card V ≤ 4) :
    ∃ k : Kind, Nonempty (G ≃g componentGraph k) ∧
      Fintype.card V = kindRank k ∧ (-graphCartanMatrix G).det.natAbs = kindDet k := by
  obtain ⟨k, e, _, hrank, hdet⟩ := smallTree_matrix_classification G hG hcard
  refine ⟨k, ⟨e⟩, hrank, ?_⟩
  rw [Matrix.det_neg, hdet, Int.natAbs_mul, Int.natAbs_pow]
  simp

/-- Every actual connected component of an at-most-eight-vertex forest with
at least five actual components has one of the five ADE matrices. Both the
component-size bound and its tree property are derived from the input graph. -/
theorem forest_component_matrix_classification {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    (hG : G.IsAcyclic) (hvertices : Fintype.card V ≤ 8)
    (hcomponents : 5 ≤ Fintype.card G.ConnectedComponent)
    (c : G.ConnectedComponent) [Fintype c.supp] :
    ∃ k : Kind, ∃ e : G.induce c.supp ≃g componentGraph k,
      (componentMatrix k).submatrix e.toEquiv e.toEquiv = graphCartanMatrix (G.induce c.supp) ∧
      Fintype.card c.supp = kindRank k ∧
      (graphCartanMatrix (G.induce c.supp)).det = (kindDet k : ℤ) := by
  exact smallTree_matrix_classification (G.induce c.supp)
    (SmallForestComponents.component_isTree G hG c)
    (SmallForestComponents.component_card_le_four G hvertices hcomponents c)

end KltDP.Lattices.SmallADEGraphs
