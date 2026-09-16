import KltDP.LinearAlgebra.SingleExtraAllocation
import Mathlib.Tactic

/-!
# Actual remaining graph in family D

The hypotheses are the actual closed canonical edge and four distinct
isolated weight-three vertices obtained in the preceding source argument.
The full graph has ten vertices and at most two edges. The only remaining
possibilities are four isolated canonical vertices, or a canonical edge and
two isolated canonical vertices. These alternatives are proved from the
actual edge set and cardinality, not assumed as table membership.
-/

namespace KltDP.LinearAlgebra

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A six-element actual fixed vertex set leaves four vertices in a
ten-vertex graph. Selecting two distinct outside vertices leaves two. -/
theorem six_fixed_remaining_counts (fixed : Finset V)
    (hcard : Fintype.card V = 10) (hfixed : fixed.card = 6) :
    (Finset.univ \ fixed).card = 4 ∧
      ∀ x y, x ≠ y → x ∉ fixed → y ∉ fixed →
        (Finset.univ \ insert x (insert y fixed)).card = 2 := by
  constructor
  · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hfixed]
  · intro x y hxy hx hy
    have hx' : x ∉ insert y fixed := by simp only [Finset.mem_insert, not_or]; exact ⟨hxy, hx⟩
    rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ,
      Finset.card_insert_of_not_mem hx', Finset.card_insert_of_not_mem hy, hcard, hfixed]

/-- The potential second edge is disjoint from the actual closed edge and
from all four actual isolated higher-weight vertices. -/
theorem closed_edge_four_isolated_remaining_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (C M B D T U : V)
    (hCM : G.Adj C M)
    (hnC : G.neighborFinset C = {M}) (hnM : G.neighborFinset M = {C})
    (hBiso : ∀ v, ¬ G.Adj B v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (hedges : G.edgeFinset.card ≤ 2) :
    G.edgeFinset = {s(C, M)} ∨
      ∃ x y, G.Adj x y ∧ x ∉ ({C, M, B, D, T, U} : Finset V) ∧
        y ∉ ({C, M, B, D, T, U} : Finset V) ∧
        G.edgeFinset = {s(C, M), s(x, y)} := by
  rcases closed_edge_remaining_edge G C M B D hCM hnC hnM hBiso hDiso hedges with
    he | ⟨x, y, _, hx, hy, he⟩
  · exact Or.inl he
  · right
    have hxy : G.Adj x y := by
      have hmem : s(x, y) ∈ G.edgeFinset := by rw [he]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmem
    have hxT : x ≠ T := by intro h; subst x; exact hTiso y hxy
    have hxU : x ≠ U := by intro h; subst x; exact hUiso y hxy
    have hyT : y ≠ T := by intro h; subst y; exact hTiso x hxy.symm
    have hyU : y ≠ U := by intro h; subst y; exact hUiso x hxy.symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
    refine ⟨x, y, hxy, ?_, ?_, he⟩
    · simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        And.intro hx.1 (And.intro hx.2.1 (And.intro hx.2.2.1
          (And.intro hx.2.2.2 (And.intro hxT hxU))))
    · simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
        And.intro hy.1 (And.intro hy.2.1 (And.intro hy.2.2.1
          (And.intro hy.2.2.2 (And.intro hyT hyU))))

/-- Exhaustive actual leftover allocation for family D. Natural vertex
weights match the source convention; isolation and the closed C-M edge
are genuine graph predicates. Every omitted vertex's weight and isolation
are included in the conclusion. -/
theorem familyD_remaining_vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (C M B D T U : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M)
    (hnC : G.neighborFinset C = {M}) (hnM : G.neighborFinset M = {C})
    (hBiso : ∀ v, ¬ G.Adj B v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (hedges : G.edgeFinset.card ≤ 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2) :
    (G.edgeFinset = {s(C, M)} ∧
      (Finset.univ \ ({C, M, B, D, T, U} : Finset V)).card = 4 ∧
      ∀ v ∈ Finset.univ \ ({C, M, B, D, T, U} : Finset V),
        weight v = 2 ∧ ∀ w, ¬ G.Adj v w) ∨
    (∃ x y, G.Adj x y ∧ x ∉ ({C, M, B, D, T, U} : Finset V) ∧
      y ∉ ({C, M, B, D, T, U} : Finset V) ∧ weight x = 2 ∧ weight y = 2 ∧
      G.edgeFinset = {s(C, M), s(x, y)} ∧
      (Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V)).card = 2 ∧
      ∀ v ∈ Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V),
        weight v = 2 ∧ ∀ w, ¬ G.Adj v w) := by
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hCU : C ≠ U := by intro h; have := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  have hMT : M ≠ T := by intro h; have := congrArg weight h; omega
  have hMU : M ≠ U := by intro h; have := congrArg weight h; omega
  have hfixed : ({C, M, B, D, T, U} : Finset V).card = 6 := by
    simp [hCM.ne, hCB, hCD, hCT, hCU, hMB, hMD, hMT, hMU, hBD,
      Ne.symm hTB, Ne.symm hUB, Ne.symm hTD, Ne.symm hUD, hTU]
  obtain ⟨hfour, htwo⟩ := six_fixed_remaining_counts
    ({C, M, B, D, T, U} : Finset V) hcard hfixed
  have hcanonical (v : V) (hv : v ∉ ({C, M, B, D, T, U} : Finset V)) :
      weight v = 2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hother v hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2
  rcases closed_edge_four_isolated_remaining_edge G C M B D T U hCM hnC hnM
    hBiso hDiso hTiso hUiso hedges with he | ⟨x, y, hxy, hx, hy, he⟩
  · left
    refine ⟨he, hfour, ?_⟩
    intro v hv
    have hout := (Finset.mem_sdiff.mp hv).2
    have hv2 := hcanonical v hout
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    have he' : G.edgeFinset = {s(C, M), s(C, M)} := by simpa using he
    exact ⟨hv2, no_adj_outside_pair_edges G C M C M he' v
      hout.1 hout.2.1 hout.1 hout.2.1⟩
  · right
    refine ⟨x, y, hxy, hx, hy, hcanonical x hx, hcanonical y hy, he,
      htwo x y hxy.ne hx hy, ?_⟩
    intro v hv
    have hout := (Finset.mem_sdiff.mp hv).2
    have hvx : v ≠ x := by intro h; subst v; simp at hout
    have hvy : v ≠ y := by intro h; subst v; simp at hout
    have hvfixed : v ∉ ({C, M, B, D, T, U} : Finset V) := by
      intro h
      exact hout (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hv2 := hcanonical v hvfixed
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvfixed
    exact ⟨hv2, no_adj_outside_pair_edges G C M x y he v
      hvfixed.1 hvfixed.2.1 hvx hvy⟩

end KltDP.LinearAlgebra
