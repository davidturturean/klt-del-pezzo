/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte, Daniel Weber, Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

/-!
# An induced path to a nearest higher-weight vertex

The endpoint is chosen by minimizing the genuine graph distance among
reachable distinct vertices of weight greater than two. A shortest walk to
that endpoint is a path, has no chords, and has only weight-two interior
vertices when every graph weight is at least two.

The two walk-length lemmas below are small attributed ports from official
Apache-2.0 Mathlib revision 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
`Mathlib/Combinatorics/SimpleGraph/Walk/Operations.lean`, lines 558 and 605.
Their take/drop definition bodies agree with the current project's pin.
No dependency or toolchain change is made.
-/

namespace KltDP.LinearAlgebra

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Port of Mathlib's `Walk.drop_length` from the cited newer revision. -/
theorem walk_drop_length (p : G.Walk u v) (n : ℕ) :
    (p.drop n).length = p.length - n := by
  induction p generalizing n <;> cases n <;> simp [*, SimpleGraph.Walk.drop]

/-- Port of Mathlib's `Walk.take_length` from the cited newer revision. -/
theorem walk_take_length (p : G.Walk u v) (n : ℕ) :
    (p.take n).length = min n p.length := by
  induction p generalizing n <;> cases n <;> simp [*, SimpleGraph.Walk.take]

/-- The actual sequence of vertices of a walk, with a finite index type. -/
def walkVertexMap (p : G.Walk u v) : Fin (p.length + 1) → V :=
  fun i => p.getVert i.val

theorem walkVertexMap_zero (p : G.Walk u v) : walkVertexMap p 0 = u := by
  simp [walkVertexMap]

theorem walkVertexMap_last (p : G.Walk u v) :
    walkVertexMap p (Fin.last p.length) = v := by
  simp [walkVertexMap]

/-- A path gives an actual injective finite vertex map. -/
theorem walkVertexMap_injective {p : G.Walk u v} (hp : p.IsPath) :
    Function.Injective (walkVertexMap p) := by
  intro i j hij
  apply Fin.ext
  have hi : i.val ≤ p.length := Nat.le_of_lt_succ i.isLt
  have hj : j.val ≤ p.length := Nat.le_of_lt_succ j.isLt
  change p.getVert i.val = p.getVert j.val at hij
  exact hp.getVert_injOn hi hj hij

/-- A chord in a shortest walk cannot skip a vertex. The proof constructs
the actual shortcut from the prefix, the proposed chord, and the suffix. -/
theorem shortest_walk_adjacent_indices {p : G.Walk u v}
    (hp : p.length = G.dist u v) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i < j)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) : i + 1 = j := by
  let shortcut : G.Walk u v := (p.take i).append ((p.drop j).cons hadj)
  have hlength := SimpleGraph.dist_le shortcut
  rw [← hp] at hlength
  simp only [shortcut, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    walk_take_length, walk_drop_length, Nat.min_eq_left hi] at hlength
  omega

/-- The actual vertex map of a shortest walk identifies adjacency with
successive indices, proving inducedness rather than assuming it. -/
theorem shortest_walk_adj_iff {p : G.Walk u v} (hp : p.length = G.dist u v)
    (i j : Fin (p.length + 1)) :
    G.Adj (walkVertexMap p i) (walkVertexMap p j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have hi : i.val ≤ p.length := by have := i.isLt; omega
  have hj : j.val ≤ p.length := by have := j.isLt; omega
  constructor
  · intro hadj
    have hne : i.val ≠ j.val := by
      intro heq
      apply hadj.ne
      simp only [walkVertexMap, heq]
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact Or.inl (shortest_walk_adjacent_indices hp hi hj hij hadj)
    · exact Or.inr (shortest_walk_adjacent_indices hp hj hi hji hadj.symm)
  · rintro (hij | hji)
    · have hadj := p.adj_getVert_succ (by omega : i.val < p.length)
      simpa only [walkVertexMap, hij] using hadj
    · have hadj := p.adj_getVert_succ (by omega : j.val < p.length)
      simpa only [walkVertexMap, hji] using hadj.symm

/-- A standard path graph embeds as an induced subgraph along a shortest walk. -/
def shortestWalkGraphEmbedding (p : G.Walk u v) (hp : p.length = G.dist u v) :
    SimpleGraph.pathGraph (p.length + 1) ↪g G where
  toFun := walkVertexMap p
  inj' := walkVertexMap_injective (p.isPath_of_length_eq_dist hp)
  map_rel_iff' := by
    intro i j
    change G.Adj (walkVertexMap p i) (walkVertexMap p j) ↔
      (SimpleGraph.pathGraph (p.length + 1)).Adj i j
    rw [shortest_walk_adj_iff hp, SimpleGraph.pathGraph_adj]

/-- A nearest distinct reachable higher-weight vertex exists whenever there
is any such vertex. Disconnected vertices are excluded from the minimized
set, since the natural graph distance has junk value zero there. -/
theorem exists_nearest_higher_vertex (G : SimpleGraph V) (weight : V → ℕ) (root : V)
    (hexists : ∃ z, z ≠ root ∧ 2 < weight z ∧ G.Reachable root z) :
    ∃ target, target ≠ root ∧ 2 < weight target ∧ G.Reachable root target ∧
      ∀ z, z ≠ root → 2 < weight z → G.Reachable root z →
        G.dist root target ≤ G.dist root z := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ z, z ≠ root ∧ 2 < weight z ∧ G.Reachable root z ∧ G.dist root z = d
  have hP : ∃ d, P d := by
    obtain ⟨z, hne, hweight, hreach⟩ := hexists
    exact ⟨G.dist root z, z, hne, hweight, hreach, rfl⟩
  obtain ⟨target, hne, hweight, hreach, hdist⟩ := Nat.find_spec hP
  refine ⟨target, hne, hweight, hreach, ?_⟩
  intro z hz hw hr
  rw [hdist]
  exact Nat.find_min' hP ⟨z, hz, hw, hr, rfl⟩

/-- Genuine nearest-endpoint minimality forces every interior vertex of the
shortest path to have weight exactly two. -/
theorem nearest_higher_path_internal_weight (weight : V → ℕ)
    (hweight : ∀ z, 2 ≤ weight z) {root target : V} (p : G.Walk root target)
    (hp : p.length = G.dist root target)
    (hmin : ∀ z, z ≠ root → 2 < weight z → G.Reachable root z →
      G.dist root target ≤ G.dist root z)
    (i : ℕ) (hi : 0 < i) (hilast : i < p.length) : weight (p.getVert i) = 2 := by
  apply Nat.le_antisymm ?_ (hweight _)
  by_contra! hhigher
  have hpath := p.isPath_of_length_eq_dist hp
  have hne : p.getVert i ≠ root := by
    intro h
    have := (hpath.getVert_eq_start_iff (by omega)).mp h
    omega
  have hminimum := hmin (p.getVert i) hne hhigher (p.take i).reachable
  have hprefix := SimpleGraph.dist_le (p.take i)
  rw [walk_take_length, Nat.min_eq_left (by omega : i ≤ p.length)] at hprefix
  omega

/-- Full existence result from actual graph weights and reachability. The
returned path is nonempty, induced, injectively indexed, and has weight-two
interior vertices. Neither inducedness nor the interior weights is assumed. -/
theorem exists_nearest_higher_weight_path (G : SimpleGraph V) (weight : V → ℕ)
    (hweight : ∀ z, 2 ≤ weight z) (root : V) (hroot : 2 < weight root)
    (hexists : ∃ z, z ≠ root ∧ 2 < weight z ∧ G.Reachable root z) :
    ∃ (target : V) (p : G.Walk root target),
      target ≠ root ∧ 2 < weight root ∧ 2 < weight target ∧ p.IsPath ∧
      p.length = G.dist root target ∧ 0 < p.length ∧
      Function.Injective (walkVertexMap p) ∧
      (∀ i j : Fin (p.length + 1),
        G.Adj (walkVertexMap p i) (walkVertexMap p j) ↔
          i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
      (∀ i : ℕ, 0 < i → i < p.length → weight (p.getVert i) = 2) ∧
      (∀ z, z ≠ root → 2 < weight z → G.Reachable root z →
        G.dist root target ≤ G.dist root z) := by
  obtain ⟨target, hne, hhigher, hreach, hmin⟩ :=
    exists_nearest_higher_vertex G weight root hexists
  obtain ⟨p, hpath, hlength⟩ := hreach.exists_path_of_dist
  refine ⟨target, p, hne, hroot, hhigher, hpath, hlength, ?_,
    walkVertexMap_injective hpath, shortest_walk_adj_iff hlength,
    nearest_higher_path_internal_weight weight hweight p hlength hmin, hmin⟩
  rw [hlength]
  exact hreach.pos_dist_of_ne (Ne.symm hne)

end KltDP.LinearAlgebra
