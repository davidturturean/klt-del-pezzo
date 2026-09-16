import KltDP.LinearAlgebra.SingleExtraGreenData
import Mathlib.Tactic

/-!
# Remaining vertices and edges in the single-extra cases

These graph theorems take the actual structural conclusions already derived
from the source budgets. A graph with the closed edge C-T and at most two
edges has either no remaining edge or one actual edge wholly outside the
four fixed vertices. The source vertex count determines the exact number
of remaining isolated canonical vertices.
-/

namespace KltDP.LinearAlgebra

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finset containing a specified element and having at most two elements
is its singleton or a pair with one distinct additional element. -/
theorem eq_singleton_or_pair_of_mem_card_le_two {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α) (ha : a ∈ S) (hcard : S.card ≤ 2) :
    S = {a} ∨ ∃ b, b ≠ a ∧ S = {a, b} := by
  have herase : (S.erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  rcases (S.erase a).eq_empty_or_nonempty with hempty | ⟨b, hb⟩
  · left
    calc
      S = insert a (S.erase a) := (Finset.insert_erase ha).symm
      _ = {a} := by rw [hempty]; rfl
  · right
    have hsingle : S.erase a = {b} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hb, fun c hc => Finset.card_le_one.mp herase c hc b hb⟩
    refine ⟨b, (Finset.mem_erase.mp hb).1, ?_⟩
    calc
      S = insert a (S.erase a) := (Finset.insert_erase ha).symm
      _ = {a, b} := by rw [hsingle]

/-- All vertices outside the endpoints of two actual listed edges are
isolated, once those edges are proved to exhaust the actual edge finset. -/
theorem no_adj_outside_pair_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c d : V) (hedges : G.edgeFinset = {s(a, b), s(c, d)})
    (v : V) (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c) (hvd : v ≠ d) :
    ∀ u, ¬ G.Adj v u := by
  intro u hadj
  have hmem : s(v, u) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj
  rw [hedges] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hmem
  rcases hmem with (h | h) | (h | h)
  · exact hva h.1
  · exact hvb h.1
  · exact hvc h.1
  · exact hvd h.1

/-- A second edge is disjoint from a closed edge and from two actual
isolated core vertices. The two alternatives exhaust the full edge set. -/
theorem closed_edge_remaining_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (C T B D : V) (hCT : G.Adj C T)
    (hnC : G.neighborFinset C = {T}) (hnT : G.neighborFinset T = {C})
    (hBiso : ∀ u, ¬ G.Adj B u) (hDiso : ∀ u, ¬ G.Adj D u)
    (hedges : G.edgeFinset.card ≤ 2) :
    G.edgeFinset = {s(C, T)} ∨
      ∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
        v ∉ ({C, T, B, D} : Finset V) ∧
        G.edgeFinset = {s(C, T), s(u, v)} := by
  have hmem : s(C, T) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hCT
  rcases eq_singleton_or_pair_of_mem_card_le_two G.edgeFinset (s(C, T)) hmem hedges with
    hsingle | hsecond
  · exact Or.inl hsingle
  · right
    obtain ⟨u, v, hne, heq⟩ := Sym2.exists.mp hsecond
    have huv : G.Adj u v := by
      have hmem' : s(u, v) ∈ G.edgeFinset := by rw [heq]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmem'
    have hout (x y : V) (hxy : G.Adj x y) (hneq : s(x, y) ≠ s(C, T)) :
        x ∉ ({C, T, B, D} : Finset V) := by
      have hxC : x ≠ C := by
        intro h
        subst x
        have hy := (G.mem_neighborFinset C y).mpr hxy
        rw [hnC, Finset.mem_singleton] at hy
        subst y
        exact hneq rfl
      have hxT : x ≠ T := by
        intro h
        subst x
        have hy := (G.mem_neighborFinset T y).mpr hxy
        rw [hnT, Finset.mem_singleton] at hy
        subst y
        exact hneq Sym2.eq_swap
      have hxB : x ≠ B := by intro h; subst x; exact hBiso y hxy
      have hxD : x ≠ D := by intro h; subst x; exact hDiso y hxy
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or, hxC, hxT, hxB, hxD,
        not_false_eq_true, and_self]
    exact ⟨u, v, huv.ne, hout u v huv hne,
      hout v u huv.symm (by simpa only [Sym2.eq_swap] using hne), heq⟩

/-- The four fixed family-A vertices leave six vertices in the actual
ten-vertex graph. Any additional edge uses two of those six. -/
theorem familyA_remaining_vertex_counts (C T B D : V)
    (hcard : Fintype.card V = 10)
    (hCT : C ≠ T) (hCB : C ≠ B) (hCD : C ≠ D)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) :
    (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
      ∀ u v, u ≠ v → u ∉ ({C, T, B, D} : Finset V) →
        v ∉ ({C, T, B, D} : Finset V) →
        (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 := by
  have hfour : ({C, T, B, D} : Finset V).card = 4 := by
    simp [hCT, hCB, hCD, hTB, hTD, hBD]
  constructor
  · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hfour]
  · intro u v huv hu hv
    have hu' : u ∉ insert v ({C, T, B, D} : Finset V) := by simp [huv, hu]
    have hsix : ({u, v, C, T, B, D} : Finset V).card = 6 := by
      rw [Finset.card_insert_of_not_mem hu', Finset.card_insert_of_not_mem hv, hfour]
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hsix]

/-- Complete leftover allocation for family A: six isolated canonical
vertices, or one actual canonical edge and four isolated canonical vertices.
The alternative is proved from the edge bound, not assumed as a table row. -/
theorem familyA_remaining_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C T B D : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) (hCT : G.Adj C T)
    (hnC : G.neighborFinset C = {T}) (hnT : G.neighborFinset T = {C})
    (hBiso : ∀ u, ¬ G.Adj B u) (hDiso : ∀ u, ¬ G.Adj D u)
    (hedges : G.edgeFinset.card ≤ 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    (G.edgeFinset = {s(C, T)} ∧
      (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
      ∀ v ∈ Finset.univ \ ({C, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∨
    (∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
      v ∉ ({C, T, B, D} : Finset V) ∧ weight u = 2 ∧ weight v = 2 ∧
      G.edgeFinset = {s(C, T), s(u, v)} ∧
      (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 ∧
      ∀ w ∈ Finset.univ \ ({u, v, C, T, B, D} : Finset V),
        weight w = 2 ∧ ∀ z, ¬ G.Adj w z) := by
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  obtain ⟨hsix, hfour⟩ := familyA_remaining_vertex_counts C T B D hcard hCT.ne hCB hCD
    hTB hTD hBD
  have hcanonical (w : V) (hw : w ∉ ({C, T, B, D} : Finset V)) : weight w = 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    exact hother w hw.2.2.1 hw.2.2.2 hw.2.1
  rcases closed_edge_remaining_edge G C T B D hCT hnC hnT hBiso hDiso hedges with
    he | ⟨u, v, huv, hu, hv, he⟩
  · left
    refine ⟨he, hsix, ?_⟩
    intro w hw
    have hout := (Finset.mem_sdiff.mp hw).2
    have hw2 := hcanonical w hout
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    have he' : G.edgeFinset = {s(C, T), s(C, T)} := by simpa using he
    exact ⟨hw2, no_adj_outside_pair_edges G C T C T he' w
      hout.1 hout.2.1 hout.1 hout.2.1⟩
  · right
    refine ⟨u, v, huv, hu, hv, hcanonical u hu, hcanonical v hv, he,
      hfour u v huv hu hv, ?_⟩
    intro w hw
    have hout := (Finset.mem_sdiff.mp hw).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    exact ⟨hother w hout.2.2.2.2.1 hout.2.2.2.2.2 hout.2.2.2.1,
      no_adj_outside_pair_edges G C T u v he w hout.2.2.1 hout.2.2.2.1
        hout.1 hout.2.1⟩

/-- The actual family-B path, two distinct cores and the source count leave
exactly five canonical isolated vertices. -/
theorem familyB_remaining_vertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M T B D : V)
    (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hCM : G.Adj C M) (hMT : G.Adj M T)
    (hedges : G.edgeFinset = {s(C, M), s(M, T)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
      ∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u := by
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  have hfive : ({C, M, T, B, D} : Finset V).card = 5 := by
    simp [hCM.ne, hCT, hCB, hCD, hMT.ne, hMB, hMD, hTB, hTD, hBD]
  constructor
  · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hfive]
  · intro v hv
    have hout := (Finset.mem_sdiff.mp hv).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    exact ⟨hother v hout.2.2.2.1 hout.2.2.2.2 hout.2.2.1,
      no_adj_outside_two_path G hedges v hout.1 hout.2.1 hout.2.2.1⟩

end KltDP.LinearAlgebra
