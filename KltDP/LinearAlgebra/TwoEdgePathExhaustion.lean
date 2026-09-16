import KltDP.LinearAlgebra.NearestHigherWeightPath
import Mathlib.Tactic

/-!
# Exhaustion of a graph by a nonadjacent two-edge connection

The beta-three core-contact case in `lem:ten-forests` has at most two
edges globally. A connection between distinct nonadjacent distinguished
vertices therefore forces an actual two-edge path, and those two edges
exhaust the entire graph. The remaining vertices are consequently isolated.

The result concerns the actual graph and its actual edge finset. It does
not assume that the graph is one of the manuscript's candidate rows.
-/

namespace KltDP.LinearAlgebra

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two consecutive actual edges between distinct endpoints exhaust a graph
whose entire edge finset has cardinality at most two. -/
theorem edgeFinset_eq_two_path (G : SimpleGraph V) [DecidableRel G.Adj]
    {a m b : V} (hab : a ≠ b) (ham : G.Adj a m) (hmb : G.Adj m b)
    (hedges : G.edgeFinset.card ≤ 2) :
    G.edgeFinset = {s(a, m), s(m, b)} := by
  have hne : s(a, m) ≠ s(m, b) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact ham.ne h.1
    · exact hab h.1
  have hfirst : s(a, m) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using ham
  have hlast : s(m, b) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmb
  have hsub : ({s(a, m), s(m, b)} : Finset (Sym2 V)) ⊆ G.edgeFinset :=
    Finset.insert_subset_iff.mpr ⟨hfirst, Finset.singleton_subset_iff.mpr hlast⟩
  have hcard : ({s(a, m), s(m, b)} : Finset (Sym2 V)).card = 2 := by simp [hne]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hedges)).symm

/-- Entrywise adjacency consequence of the actual exhausted edge finset. -/
theorem adj_iff_of_edgeFinset_eq_two_path (G : SimpleGraph V) [DecidableRel G.Adj]
    {a m b : V} (hedges : G.edgeFinset = {s(a, m), s(m, b)}) (x y : V) :
    G.Adj x y ↔ ((x = a ∧ y = m) ∨ (x = m ∧ y = a)) ∨
      ((x = m ∧ y = b) ∨ (x = b ∧ y = m)) := by
  calc
    G.Adj x y ↔ s(x, y) ∈ G.edgeFinset := by
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    _ ↔ _ := by
      rw [hedges]
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]

/-- Every vertex outside the three actual path vertices is isolated once
the two path edges exhaust the graph. -/
theorem no_adj_outside_two_path (G : SimpleGraph V) [DecidableRel G.Adj]
    {a m b : V} (hedges : G.edgeFinset = {s(a, m), s(m, b)})
    (v : V) (hva : v ≠ a) (hvm : v ≠ m) (hvb : v ≠ b) :
    ∀ u, ¬ G.Adj v u := by
  intro u
  rw [adj_iff_of_edgeFinset_eq_two_path G hedges]
  simp only [hva, hvm, hvb, false_and, false_or, not_false_eq_true]

/-- The actual neighbor finsets of the forced path. These identities can
be substituted directly into weighted row equations. -/
theorem neighborFinsets_of_two_path (G : SimpleGraph V) [DecidableRel G.Adj]
    {a m b : V} (hab : a ≠ b) (ham : G.Adj a m) (hmb : G.Adj m b)
    (hedges : G.edgeFinset = {s(a, m), s(m, b)}) :
    G.neighborFinset a = {m} ∧ G.neighborFinset m = {a, b} ∧
      G.neighborFinset b = {m} := by
  refine ⟨?_, ?_, ?_⟩
  · ext v
    rw [G.mem_neighborFinset a v]
    simp only [Finset.mem_singleton, adj_iff_of_edgeFinset_eq_two_path G hedges,
      ham.ne, hab, true_and, false_and, false_or, or_false, eq_self]
  · ext v
    rw [G.mem_neighborFinset m v]
    simp only [Finset.mem_insert, Finset.mem_singleton,
      adj_iff_of_edgeFinset_eq_two_path G hedges, Ne.symm ham.ne, hmb.ne,
      true_and, false_and, false_or, or_false, eq_self]
  · ext v
    rw [G.mem_neighborFinset b v]
    simp only [Finset.mem_singleton, adj_iff_of_edgeFinset_eq_two_path G hedges,
      Ne.symm hab, Ne.symm hmb.ne, true_and, false_and, false_or, or_false, eq_self]

/-- Genuine reachability and the global edge bound force the actual middle
vertex and exhaust all graph edges. Distinctness and nonadjacency are the
source's marked-vertex hypotheses. -/
theorem exists_middle_of_nonadjacent_two_edge_connection
    (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b) (hreach : G.Reachable a b)
    (hedges : G.edgeFinset.card ≤ 2) :
    ∃ m, G.Adj a m ∧ G.Adj m b ∧ G.edgeFinset = {s(a, m), s(m, b)} ∧
      (∀ v, v ≠ a → v ≠ m → v ≠ b → ∀ u, ¬ G.Adj v u) := by
  obtain ⟨p, hp, hdist⟩ := hreach.exists_path_of_dist
  have hmin := hreach.one_lt_dist_of_ne_of_not_adj hab hnadj
  have hmax := hp.isTrail.length_le_card_edgeFinset.trans hedges
  have hlength : p.length = 2 := by omega
  let m := p.getVert 1
  have ham : G.Adj a m := by
    have h := p.adj_getVert_succ (by omega : 0 < p.length)
    simpa only [SimpleGraph.Walk.getVert_zero, m] using h
  have hmb : G.Adj m b := by
    have h := p.adj_getVert_succ (by omega : 1 < p.length)
    have hlast : p.getVert 2 = b := by simpa only [hlength] using p.getVert_length
    simpa only [m, hlast] using h
  have hexhaust := edgeFinset_eq_two_path G hab ham hmb hedges
  exact ⟨m, ham, hmb, hexhaust, fun v hva hvm hvb =>
    no_adj_outside_two_path G hexhaust v hva hvm hvb⟩

/-- The middle vertex has weight two when the terminal higher-weight vertex
is unique in its component. This adapter uses the already proved separation
conclusion; the underlying graph exhaustion does not require weights. -/
theorem exists_canonical_middle_of_two_edge_connection
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (hweight : ∀ v, 2 ≤ weight v)
    (hunique : ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y)
    {a b : V} (hb : 2 < weight b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hreach : G.Reachable a b) (hedges : G.edgeFinset.card ≤ 2) :
    ∃ m, weight m = 2 ∧ G.Adj a m ∧ G.Adj m b ∧
      G.edgeFinset = {s(a, m), s(m, b)} ∧
      (∀ v, v ≠ a → v ≠ m → v ≠ b → ∀ u, ¬ G.Adj v u) := by
  obtain ⟨m, ham, hmb, hexhaust, hisolated⟩ :=
    exists_middle_of_nonadjacent_two_edge_connection G hab hnadj hreach hedges
  have hm : weight m = 2 := by
    apply Nat.le_antisymm ?_ (hweight m)
    by_contra! hhigher
    exact hmb.ne (hunique m b hhigher hb hmb.reachable)
  exact ⟨m, hm, ham, hmb, hexhaust, hisolated⟩

end KltDP.LinearAlgebra
