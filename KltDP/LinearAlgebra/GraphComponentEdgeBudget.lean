import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Edge budgets for actual distinct connected components

The edges of induced graphs on pairwise disjoint vertex sets map injectively
into disjoint subsets of the ambient edge finset. Their total cardinality
therefore cannot exceed the ambient edge count. Applying this to actual
reachability sets gives the component budget without acyclicity or a supplied
partition of the ambient graph.

Reuse: pinned Mathlib's `SimpleGraph.map_edgeFinset_induce` identifies the
actual mapped edge sets, and `Finset.card_biUnion` counts their disjoint union.
The current official finite-graph and connected-component sources and the
cached tree library were checked as well; no additional component-edge
cardinality theorem was found in those checked sources. No source port is
needed for this adapter.
-/

namespace KltDP.LinearAlgebra

open SimpleGraph
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]

/-- Summing the actual induced edge counts over pairwise disjoint vertex
sets is bounded by the actual ambient edge count. The sets need not cover
the vertices, and there may be edges between different sets. -/
theorem sum_induce_edgeFinset_card_le_of_disjoint
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (sets : I → Set V) [∀ i, DecidablePred (fun v => v ∈ sets i)]
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (sets i) (sets j)) :
    (∑ i, (G.induce (sets i)).edgeFinset.card) ≤ G.edgeFinset.card := by
  classical
  let edges : I → Finset (Sym2 V) := fun i => G.edgeFinset ∩ (sets i).toFinset.sym2
  have hcard (i : I) : (G.induce (sets i)).edgeFinset.card = (edges i).card := by
    have h := congrArg Finset.card
      (SimpleGraph.map_edgeFinset_induce (G := G) (s := sets i))
    simpa only [Finset.card_map] using h
  have hpairwise : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint edges := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro edge hi hj
    revert hi hj
    refine Sym2.inductionOn edge ?_
    intro v w hi hj
    have hvi : v ∈ sets i := Set.mem_toFinset.mp
      (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hi).2).1
    have hvj : v ∈ sets j := Set.mem_toFinset.mp
      (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hj).2).1
    exact Set.disjoint_left.mp (hdisjoint i j hij) hvi hvj
  have hsubset : Finset.univ.biUnion edges ⊆ G.edgeFinset := by
    intro edge he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp hi).1
  calc
    (∑ i, (G.induce (sets i)).edgeFinset.card) = ∑ i, (edges i).card :=
      Finset.sum_congr rfl (fun i _ => hcard i)
    _ = (Finset.univ.biUnion edges).card := (Finset.card_biUnion hpairwise).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsubset

/-- Pairwise nonreachable roots select actual distinct connected components.
The sum of their actual induced edge counts is bounded by the ambient graph's
edge count, with no acyclicity assumption or supplied component budget. -/
theorem sum_component_edgeFinset_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : I → V)
    [∀ i, DecidablePred (G.Reachable (r i))]
    (hseparate : ∀ i j, i ≠ j → ¬ G.Reachable (r i) (r j)) :
    (∑ i, (G.induce {v | G.Reachable (r i) v}).edgeFinset.card) ≤
      G.edgeFinset.card := by
  apply sum_induce_edgeFinset_card_le_of_disjoint G (fun i => {v | G.Reachable (r i) v})
  intro i j hij
  refine Set.disjoint_left.mpr ?_
  intro v hi hj
  exact hseparate i j hij (SimpleGraph.Reachable.trans hi (SimpleGraph.Reachable.symm hj))

end KltDP.LinearAlgebra
