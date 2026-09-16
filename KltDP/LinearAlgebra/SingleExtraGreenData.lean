import KltDP.LinearAlgebra.SingleExtraComponent
import Mathlib.Tactic

/-!
# Actual marked Green data for the surviving single-extra components

The family-A edge and family-B two-edge path are derived from the actual
graph in the source-facing theorems. Their marked Green values are then
computed from the full inverse-source equation and actual neighbor sets.
No projection identity or candidate-table membership is assumed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A weight-three isolated marked vertex has Green coefficient one-third.
The source here is the actual three-coordinate marked vector. -/
theorem isolated_marked_green_value (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (green : V → 𝕜) (C B D : V)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ green =
      threeMarkedSource C B D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hB : weight B = 3)
    (hisolated : ∀ u, ¬ G.Adj B u) : green B = 1 / 3 := by
  have h := graph_isolated_row G (fun i => (weight i : 𝕜)) green
    (threeMarkedSource C B D) hrow B hisolated
  dsimp only at h
  rw [hB] at h
  norm_num [threeMarkedSource, Pi.single_apply, hBC, hBD] at h
  linarith only [h]

/-- The energy of the actual marked source when C-T is a closed edge and
both marked core vertices are actually isolated. -/
theorem adjacent_extra_green_energy (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (green : V → 𝕜) (C B D T : V)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hnC : G.neighborFinset C = {T}) (hnT : G.neighborFinset T = {C})
    (hBiso : ∀ u, ¬ G.Adj B u) (hDiso : ∀ u, ¬ G.Adj D u)
    (hgreen : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ green =
      threeMarkedSource C B D) :
    dotProduct (threeMarkedSource C B D) green = (19 : 𝕜) / 15 := by
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have gc := congrFun hgreen C
  have gt := congrFun hgreen T
  rw [graphWeightMatrix_mulVec_apply, hnC] at gc
  rw [graphWeightMatrix_mulVec_apply, hnT] at gt
  simp only [Finset.sum_singleton] at gc gt
  rw [hC] at gc
  rw [hT] at gt
  norm_num [threeMarkedSource, Pi.single_apply, hCB, hCD, Ne.symm hCT, hTB, hTD] at gc gt
  have hgC : green C = 3 / 5 := by linarith only [gc, gt]
  have hgB := isolated_marked_green_value G weight green C B D hgreen
    (Ne.symm hCB) hBD hB hBiso
  have gd := graph_isolated_row G (fun i => (weight i : 𝕜)) green
    (threeMarkedSource C B D) hgreen D hDiso
  dsimp only at gd
  rw [hD] at gd
  norm_num [threeMarkedSource, Pi.single_apply, Ne.symm hCD, Ne.symm hBD] at gd
  have hgD : green D = 1 / 3 := by linarith only [gd]
  rw [threeMarkedSource_dotProduct, hgC, hgB, hgD]
  norm_num

/-- The energy of the actual marked source on the exhausted C-M-T path
of weights two, two, three, with both marked cores actually isolated. -/
theorem nonadjacent_extra_green_energy (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (green : V → 𝕜) (C M B D T : V)
    (hC : weight C = 2) (hM : weight M = 2) (hB : weight B = 3)
    (hD : weight D = 3) (hT : weight T = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hCM : G.Adj C M) (hMT : G.Adj M T)
    (hedges : G.edgeFinset = {s(C, M), s(M, T)})
    (hBiso : ∀ u, ¬ G.Adj B u) (hDiso : ∀ u, ¬ G.Adj D u)
    (hgreen : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ green =
      threeMarkedSource C B D) :
    dotProduct (threeMarkedSource C B D) green = (29 : 𝕜) / 21 := by
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  obtain ⟨gc, gm, gt⟩ := graph_two_path_rows G (fun i => (weight i : 𝕜)) green
    (threeMarkedSource C B D) hgreen C M T hCT hCM hMT hedges
  rw [hC] at gc
  rw [hM] at gm
  rw [hT] at gt
  norm_num [threeMarkedSource, Pi.single_apply, hCB, hCD, Ne.symm hCM.ne,
    hMB, hMD, Ne.symm hCT, hTB, hTD] at gc gm gt
  have hgC : green C = 5 / 7 := by linarith only [gc, gm, gt]
  have hgB := isolated_marked_green_value G weight green C B D hgreen
    (Ne.symm hCB) hBD hB hBiso
  have gd := graph_isolated_row G (fun i => (weight i : 𝕜)) green
    (threeMarkedSource C B D) hgreen D hDiso
  dsimp only at gd
  rw [hD] at gd
  norm_num [threeMarkedSource, Pi.single_apply, Ne.symm hCD, Ne.symm hBD] at gd
  have hgD : green D = 1 / 3 := by linarith only [gd]
  rw [threeMarkedSource_dotProduct, hgC, hgB, hgD]
  norm_num

section Source

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- Family-A invariant values derived from the actual adjacent-extra
source hypotheses and actual inverse quadratic form. -/
theorem beta_three_adjacent_extra_data
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
    (∀ v, G.Reachable C v ↔ v = C ∨ v = T) ∧
      (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = (2 : 𝕜) / 15 ∧
      -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff = (1 : 𝕜) / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun i => (weight i : 𝕜)))⁻¹ *ᵥ
          threeMarkedSource C B D) = (19 : 𝕜) / 15 := by
  obtain ⟨hnC, hnT, hBiso, hDiso, hc, ht, hb, hd⟩ :=
    beta_three_adjacent_extra_structure G weight coeff C B D T hweight hC hB hD hT
      hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  have hsource := beta_three_single_extra_source_sum weight coeff B D T hBD hTB hTD
    hB hD hT hother
  let A := graphWeightMatrix G (fun i => (weight i : 𝕜))
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  have hgreen : A *ᵥ (A⁻¹ *ᵥ threeMarkedSource C B D) = threeMarkedSource C B D := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  refine ⟨reachable_iff_of_mutual_singleton_neighbors G C T hCT hnC hnT,
    hBiso, hDiso, ?_, ?_, ?_⟩
  · rw [threeMarkedSource_dotProduct, hc, hb, hd]
    norm_num
  · rw [hsource, hb, hd, ht]
    norm_num
  · exact adjacent_extra_green_energy G weight (A⁻¹ *ᵥ threeMarkedSource C B D)
      C B D T hC hB hD hT hBD hTB hTD hnC hnT hBiso hDiso hgreen

/-- Family-B actual path and invariant values. Reachability, nonadjacency
and the actual edge bound force the entire graph edge set; the path itself
and its canonical middle are not assumptions. -/
theorem beta_three_nonadjacent_extra_data
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → 𝕜) (C B D T : V)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B D) (hreach : G.Reachable C T) (hnadj : ¬ G.Adj C T)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B - coeff D)
    (hv : -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D) :
    ∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
      G.edgeFinset = {s(C, M), s(M, T)} ∧
      (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = (4 : 𝕜) / 21 ∧
      -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff = (2 : 𝕜) / 21 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun i => (weight i : 𝕜)))⁻¹ *ᵥ
          threeMarkedSource C B D) = (29 : 𝕜) / 21 := by
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
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
  obtain ⟨M, hM, hCM, hMT, hexhaust, _⟩ :=
    exists_canonical_middle_of_two_edge_connection G weight hweight hunique
      (by rw [hT]; omega : 2 < weight T) hCT hnadj hreach hedges
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  have hBiso := no_adj_outside_two_path G hexhaust B (Ne.symm hCB) (Ne.symm hMB) (Ne.symm hTB)
  have hDiso := no_adj_outside_two_path G hexhaust D (Ne.symm hCD) (Ne.symm hMD) (Ne.symm hTD)
  obtain ⟨hc, _, ht⟩ := two_edge_canonical_coefficients G weight coeff hrow C M T
    hC hM hT hCT hCM hMT hexhaust
  have hb := canonical_isolated_weight_three G weight coeff hrow B hB hBiso
  have hd := canonical_isolated_weight_three G weight coeff hrow D hD hDiso
  have hsource := beta_three_single_extra_source_sum weight coeff B D T hBD hTB hTD
    hB hD hT hother
  let A := graphWeightMatrix G (fun i => (weight i : 𝕜))
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  have hgreen : A *ᵥ (A⁻¹ *ᵥ threeMarkedSource C B D) = threeMarkedSource C B D := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  refine ⟨M, hM, hCM, hMT, hexhaust, hBiso, hDiso, ?_, ?_, ?_⟩
  · rw [threeMarkedSource_dotProduct, hc, hb, hd]
    norm_num
  · rw [hsource, hb, hd, ht]
    norm_num
  · exact nonadjacent_extra_green_energy G weight (A⁻¹ *ᵥ threeMarkedSource C B D)
      C M B D T hC hM hB hD hT hBD hTB hTD hCM hMT hexhaust hBiso hDiso hgreen

end Source

end KltDP.LinearAlgebra
