import KltDP.LinearAlgebra.BetaThreeCoreContact
import Mathlib.Tactic

/-!
# The beta-three component containing the sole extra higher-weight vertex

This module treats an actual adjacency from the canonical marked vertex C
to the sole extra weight-three vertex T. The full source budgets rule out
a second neighbor at either endpoint. This part of the source argument
does not require the stated leaf hypothesis at C.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Mutual singleton neighbor finsets determine the entire actual
connected component, using Mathlib's subgraph closure theorem. -/
theorem reachable_iff_of_mutual_singleton_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj] (C T : V) (hCT : G.Adj C T)
    (hC : G.neighborFinset C = {T}) (hT : G.neighborFinset T = {C}) (v : V) :
    G.Reachable C v ↔ v = C ∨ v = T := by
  have hclosed : ∀ x ∈ (G.subgraphOfAdj hCT).verts,
      ∀ y, G.Adj x y → (G.subgraphOfAdj hCT).Adj x y := by
    intro x hx y hxy
    change x = C ∨ x = T at hx
    rcases hx with hx | hx
    · subst x
      have hy : y = T := by
        have hmem := (G.mem_neighborFinset C y).mpr hxy
        rw [hC, Finset.mem_singleton] at hmem
        exact hmem
      subst y
      rfl
    · subst x
      have hy : y = C := by
        have hmem := (G.mem_neighborFinset T y).mpr hxy
        rw [hT, Finset.mem_singleton] at hmem
        exact hmem
      subst y
      change s(C, T) = s(T, C)
      exact Sym2.eq_swap
  constructor
  · intro hr
    have hmem := hr.mem_subgraphVerts hclosed
      (by change C = C ∨ C = T; exact Or.inl rfl)
    exact hmem
  · rintro (hv | hv)
    · subst v
      exact SimpleGraph.Reachable.refl C
    · subst v
      exact hCT.reachable

/-- The canonical coefficient at an actual isolated weight-three vertex. -/
theorem canonical_isolated_weight_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (v : V) (hv : weight v = 3) (hisolated : ∀ u, ¬ G.Adj v u) :
    coeff v = 1 / 3 := by
  have h := graph_isolated_row G (fun i => (weight i : 𝕜)) coeff
    (fun i => (weight i : 𝕜) - 2) hrow v hisolated
  dsimp only at h
  rw [hv] at h
  norm_num at h
  linarith only [h]

/-- Exact source sum when the actual two cores and the sole extra vertex
all have weight three. Every other actual source entry is zero. -/
theorem beta_three_single_extra_source_sum (weight : V → ℕ) (coeff : V → 𝕜)
    (B D T : V) (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    dotProduct (fun i => (weight i : 𝕜) - 2) coeff = coeff B + coeff D + coeff T := by
  have hmass := noncoreSourceMass_eq_single_extra (fun i => (weight i : 𝕜)) coeff B D T
    hTB hTD (by change (weight T : 𝕜) = 3; exact_mod_cast hT)
    (fun i hiB hiD hiT => by
      change (weight i : 𝕜) = 2
      exact_mod_cast hother i hiB hiD hiT)
  have hsource := canonical_source_sum_split (fun i => (weight i : 𝕜)) coeff B D hBD
  dsimp only at hsource
  rw [hB, hD, hmass] at hsource
  norm_num at hsource
  exact hsource

/-- Canonical coefficients on an actual two-edge path of weights two,
three, two. The full edge finset, rather than a candidate matrix, is used. -/
theorem two_edge_center_three_coefficients (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (C T M : V) (hC : weight C = 2) (hT : weight T = 3) (hM : weight M = 2)
    (hCM : C ≠ M) (hCT : G.Adj C T) (hTM : G.Adj T M)
    (hedges : G.edgeFinset = {s(C, T), s(T, M)}) :
    coeff C = 1 / 4 ∧ coeff T = 1 / 2 ∧ coeff M = 1 / 4 := by
  obtain ⟨hc, ht, hm⟩ := graph_two_path_rows G (fun i => (weight i : 𝕜)) coeff
    (fun i => (weight i : 𝕜) - 2) hrow C T M hCM hCT hTM hedges
  norm_num [hC, hT, hM] at hc ht hm
  constructor
  · linarith only [hc, ht, hm]
  constructor <;> linarith only [hc, ht, hm]

/-- An actual weight-three vertex with an actual weight-two neighbor has
coefficient at least two-fifths. Omitted neighbor terms are nonnegative. -/
theorem weight_three_adjacent_two_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (B M : V)
    (hB : weight B = 3) (hM : weight M = 2) (hBM : G.Adj B M) :
    (2 : 𝕜) / 5 ≤ coeff B := by
  have hneighbor := graph_neighbor_le_twice G (fun i => (weight i : 𝕜)) coeff
    hrow hcoeff M B (by change (weight M : 𝕜) = 2; exact_mod_cast hM) hBM.symm
  have hsum := Finset.single_le_sum
    (fun i (_ : i ∈ G.neighborFinset B) => hcoeff i)
    ((G.mem_neighborFinset B M).mpr hBM)
  have h := congrFun hrow B
  rw [graphWeightMatrix_mulVec_apply] at h
  change (weight B : 𝕜) * coeff B - (∑ u ∈ G.neighborFinset B, coeff u) =
    (weight B : 𝕜) - 2 at h
  rw [hB] at h
  norm_num at h
  linarith only [hneighbor, hsum, h]

section Source

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- If C is actually adjacent to the sole extra weight-three vertex T in
the beta-three case, its component is the isolated edge C-T, both cores
are isolated, and their canonical coefficients have the stated values.
Each exclusion is derived from the actual graph rows and source budget. -/
theorem beta_three_adjacent_extra_structure
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → 𝕜) (C B D T : V)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B D) (hCT : G.Adj C T)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B - coeff D)
    (hv : -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D) :
    G.neighborFinset C = {T} ∧ G.neighborFinset T = {C} ∧
      (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
      coeff C = 1 / 5 ∧ coeff T = 2 / 5 ∧ coeff B = 1 / 3 ∧ coeff D = 1 / 3 := by
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  have hother' : ∀ i, i ≠ B → i ≠ D → weight i = 2 ∨ weight i = 3 := by
    intro i hiB hiD
    by_cases hiT : i = T
    · exact Or.inr (by simpa only [hiT] using hT)
    · exact Or.inl (hother i hiB hiD hiT)
  obtain ⟨hcore, hcharge⟩ := graph_charge_budgets_of_source_budgets
    (fun i => (weight i : 𝕜)) coeff C B D (3 : 𝕜) hBD
    (by change (weight B : 𝕜) = 3; exact_mod_cast hB)
    (by change (weight D : 𝕜) = 3; exact_mod_cast hD) (hcoeff C) hell
    (by simpa only [show (2 : 𝕜) - 3 = -1 by norm_num] using hv)
  have hunique := heavy_vertices_eq_of_graph_charge G weight coeff B D 3
    (Or.inl rfl) hweight hB hD hother' hseparate hA hrow hcoeff hcore hcharge
  have hsource := beta_three_single_extra_source_sum weight coeff B D T hBD hTB hTD
    hB hD hT hother
  have hTgt : 2 < weight T := by rw [hT]; omega
  have hBgt : 2 < weight B := by rw [hB]; omega
  have hDgt : 2 < weight D := by rw [hD]; omega
  have hnotcore (v : V) (hr : G.Reachable v T) : v ≠ B ∧ v ≠ D := by
    constructor
    · intro heq
      subst v
      exact hTB (hunique B T hBgt hTgt hr).symm
    · intro heq
      subst v
      exact hTD (hunique D T hDgt hTgt hr).symm
  have hcanonical (v : V) (hne : v ≠ T) (hr : G.Reachable v T) : weight v = 2 := by
    apply Nat.le_antisymm ?_ (hweight v)
    by_contra! hhigher
    exact hne (hunique v T hhigher hTgt hr)
  have hcorevalues (P Q R : V)
      (he : G.edgeFinset = {s(P, Q), s(Q, R)})
      (hp : G.Reachable P T) (hq : G.Reachable Q T) (hr : G.Reachable R T) :
      coeff B = 1 / 3 ∧ coeff D = 1 / 3 := by
    constructor
    · exact canonical_isolated_weight_three G weight coeff hrow B hB
        (no_adj_outside_two_path G he B (Ne.symm (hnotcore P hp).1)
          (Ne.symm (hnotcore Q hq).1) (Ne.symm (hnotcore R hr).1))
    · exact canonical_isolated_weight_three G weight coeff hrow D hD
        (no_adj_outside_two_path G he D (Ne.symm (hnotcore P hp).2)
          (Ne.symm (hnotcore Q hq).2) (Ne.symm (hnotcore R hr).2))
  have hTneighbor : ∀ M, G.Adj T M → M = C := by
    intro M hTM
    apply Classical.byContradiction
    intro hMC
    have hM := hcanonical M (Ne.symm hTM.ne) hTM.symm.reachable
    have hexhaust := edgeFinset_eq_two_path G (Ne.symm hMC) hCT hTM hedges
    obtain ⟨hc, ht, _⟩ := two_edge_center_three_coefficients G weight coeff hrow C T M
      hC hT hM (Ne.symm hMC) hCT hTM hexhaust
    obtain ⟨hb, hd⟩ := hcorevalues C T M hexhaust hCT.reachable
      (SimpleGraph.Reachable.refl T) hTM.symm.reachable
    norm_num [hsource, hc, ht, hb, hd] at hv
  have hCneighbor : ∀ M, G.Adj C M → M = T := by
    intro M hCM
    apply Classical.byContradiction
    intro hMT
    have hr : G.Reachable M T := hCM.symm.reachable.trans hCT.reachable
    have hM := hcanonical M hMT hr
    have hexhaust := edgeFinset_eq_two_path G hMT hCM.symm hCT hedges
    obtain ⟨_, hc, ht⟩ := two_edge_canonical_coefficients G weight coeff hrow M C T
      hM hC hT hMT hCM.symm hCT hexhaust
    obtain ⟨hb, hd⟩ := hcorevalues M C T hexhaust hr hCT.reachable
      (SimpleGraph.Reachable.refl T)
    norm_num [hsource, hc, ht, hb, hd] at hv
  have hnC : G.neighborFinset C = {T} := by
    ext v
    rw [G.mem_neighborFinset C v, Finset.mem_singleton]
    constructor
    · exact hCneighbor v
    · intro h
      subst v
      exact hCT
  have hnT : G.neighborFinset T = {C} := by
    ext v
    rw [G.mem_neighborFinset T v, Finset.mem_singleton]
    constructor
    · exact hTneighbor v
    · intro h
      subst v
      exact hCT.symm
  have hcrow := congrFun hrow C
  have htrow := congrFun hrow T
  rw [graphWeightMatrix_mulVec_apply, hnC] at hcrow
  rw [graphWeightMatrix_mulVec_apply, hnT] at htrow
  simp only [Finset.sum_singleton] at hcrow htrow
  change (weight C : 𝕜) * coeff C - coeff T = (weight C : 𝕜) - 2 at hcrow
  change (weight T : 𝕜) * coeff T - coeff C = (weight T : 𝕜) - 2 at htrow
  rw [hC] at hcrow
  rw [hT] at htrow
  norm_num at hcrow htrow
  have hc : coeff C = 1 / 5 := by linarith only [hcrow, htrow]
  have ht : coeff T = 2 / 5 := by linarith only [hcrow, htrow]
  have hcorelower (U : V) (hU : weight U = 3) : (1 : 𝕜) / 3 ≤ coeff U := by
    have h := graph_coefficient_lower_bound G (fun i => (weight i : 𝕜)) coeff hrow
      hcoeff U (by change (0 : 𝕜) < (weight U : 𝕜); rw [hU]; norm_num)
    norm_num [hU] at h
    exact h
  have hBlower := hcorelower B hB
  have hDlower := hcorelower D hD
  have hv' := hv
  rw [hsource, hc, ht] at hv'
  have hcoreisolated (U : V) (hU : weight U = 3) (hwhich : U = B ∨ U = D) :
      ∀ M, ¬ G.Adj U M := by
    intro M hUM
    have hM : weight M = 2 := by
      apply Nat.le_antisymm ?_ (hweight M)
      by_contra! hhigher
      exact hUM.ne (hunique U M (by rw [hU]; omega) hhigher hUM.reachable)
    have hlower := weight_three_adjacent_two_bound G weight coeff hrow hcoeff U M hU hM hUM
    rcases hwhich with rfl | rfl
    · linarith only [hv', hlower, hDlower]
    · linarith only [hv', hlower, hBlower]
  have hBisolated := hcoreisolated B hB (Or.inl rfl)
  have hDisolated := hcoreisolated D hD (Or.inr rfl)
  exact ⟨hnC, hnT, hBisolated, hDisolated, hc, ht,
    canonical_isolated_weight_three G weight coeff hrow B hB hBisolated,
    canonical_isolated_weight_three G weight coeff hrow D hD hDisolated⟩

end Source

end KltDP.LinearAlgebra
