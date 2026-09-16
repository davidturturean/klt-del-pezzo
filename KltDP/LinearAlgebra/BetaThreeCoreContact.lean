import KltDP.LinearAlgebra.TwoEdgePathExhaustion
import KltDP.LinearAlgebra.GraphPathConcavity
import Mathlib.Tactic

/-!
# Excluding beta-three core contact from actual graph rows

The global two-edge bound forces the connected core-contact path to have
weights two, two, three. Every other vertex is isolated. The actual
canonical and marked Green rows then determine the source invariants.
Their projection identity would require four times the number of extra
weight-three vertices to equal three, which is impossible.

The source-facing theorem derives the path and higher-weight separation;
neither a candidate-graph membership nor a matrix fixture is assumed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The actual marked source with one contribution at each distinguished
vertex. Distinctness is imposed where the source is evaluated. -/
def threeMarkedSource (C B D : V) : V → 𝕜 :=
  Pi.single C 1 + Pi.single B 1 + Pi.single D 1

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Pairing the actual marked vector is the sum of its three coordinates. -/
theorem threeMarkedSource_dotProduct (C B D : V) (x : V → 𝕜) :
    dotProduct (threeMarkedSource C B D) x = x C + x B + x D := by
  simp only [threeMarkedSource, add_dotProduct, single_dotProduct, one_mul]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- At an actually isolated vertex the full matrix equation reduces to
the diagonal equation. Isolation is stated on the actual graph. -/
theorem graph_isolated_row (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight x source : V → 𝕜) (hrow : graphWeightMatrix G weight *ᵥ x = source)
    (v : V) (hisolated : ∀ u, ¬ G.Adj v u) :
    weight v * x v = source v := by
  have hn : G.neighborFinset v = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro u hu
    exact hisolated u ((G.mem_neighborFinset v u).mp hu)
  have h := congrFun hrow v
  rw [graphWeightMatrix_mulVec_apply, hn] at h
  simpa only [Finset.sum_empty, sub_zero] using h

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The actual three path rows after the graph's edge set has been proved
to consist of these two edges. This applies to any source vector. -/
theorem graph_two_path_rows (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight x source : V → 𝕜) (hrow : graphWeightMatrix G weight *ᵥ x = source)
    (C M B : V) (hCB : C ≠ B) (hCM : G.Adj C M) (hMB : G.Adj M B)
    (hedges : G.edgeFinset = {s(C, M), s(M, B)}) :
    weight C * x C - x M = source C ∧
      weight M * x M - (x C + x B) = source M ∧
      weight B * x B - x M = source B := by
  obtain ⟨hC, hM, hB⟩ := neighborFinsets_of_two_path G hCB hCM hMB hedges
  refine ⟨?_, ?_, ?_⟩
  · have h := congrFun hrow C
    rw [graphWeightMatrix_mulVec_apply, hC] at h
    simpa only [Finset.sum_singleton] using h
  · have h := congrFun hrow M
    rw [graphWeightMatrix_mulVec_apply, hM] at h
    simpa [hCB] using h
  · have h := congrFun hrow B
    rw [graphWeightMatrix_mulVec_apply, hB] at h
    simpa only [Finset.sum_singleton] using h

/-- The canonical coefficients on the actual exhausted path of weights
two, two, three are forced by the full canonical equation. -/
theorem two_edge_canonical_coefficients (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → 𝕜)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (C M B : V) (hC : weight C = 2) (hM : weight M = 2) (hB : weight B = 3)
    (hCB : C ≠ B) (hCM : G.Adj C M) (hMB : G.Adj M B)
    (hedges : G.edgeFinset = {s(C, M), s(M, B)}) :
    coeff C = 1 / 7 ∧ coeff M = 2 / 7 ∧ coeff B = 3 / 7 := by
  obtain ⟨hc, hm, hb⟩ := graph_two_path_rows G (fun i => (weight i : 𝕜)) coeff
    (fun i => (weight i : 𝕜) - 2) hrow C M B hCB hCM hMB hedges
  norm_num [hC, hM, hB] at hc hm hb
  constructor
  · linarith only [hc, hm, hb]
  constructor <;> linarith only [hc, hm, hb]

/-- Exact invariant values for an actual exhausted core-contact path.
The number `k` is the cardinality of an actual filtered vertex finset.
No upper bound on this number is needed for the resulting contradiction. -/
theorem beta_three_core_contact_values
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff green : V → 𝕜) (C M B D : V)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hBD : B ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → weight i = 2 ∨ weight i = 3)
    (hCM : G.Adj C M) (hMB : G.Adj M B)
    (hedges : G.edgeFinset = {s(C, M), s(M, B)})
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hgreen : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ green =
      threeMarkedSource C B D) :
    ∃ k : ℕ,
      1 - dotProduct (threeMarkedSource C B D) coeff = (2 : 𝕜) / 21 ∧
      dotProduct (threeMarkedSource C B D) green = (37 : 𝕜) / 21 ∧
      -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff =
        (k : 𝕜) / 3 - 5 / 21 := by
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  have hDiso : ∀ u, ¬ G.Adj D u :=
    no_adj_outside_two_path G hedges D (Ne.symm hCD) (Ne.symm hMD) (Ne.symm hBD)
  obtain ⟨hc, hm, hb⟩ := two_edge_canonical_coefficients G weight coeff hrow C M B
    hC hM hB hCB hCM hMB hedges
  have hd : coeff D = 1 / 3 := by
    have h := graph_isolated_row G (fun i => (weight i : 𝕜)) coeff
      (fun i => (weight i : 𝕜) - 2) hrow D hDiso
    dsimp only at h
    rw [hD] at h
    norm_num at h
    linarith only [h]
  obtain ⟨gc, gm, gb⟩ := graph_two_path_rows G (fun i => (weight i : 𝕜)) green
    (threeMarkedSource C B D) hgreen C M B hCB hCM hMB hedges
  have gd := graph_isolated_row G (fun i => (weight i : 𝕜)) green
    (threeMarkedSource C B D) hgreen D hDiso
  dsimp only at gc gm gb gd
  rw [hC] at gc
  rw [hM] at gm
  rw [hB] at gb
  rw [hD] at gd
  norm_num [threeMarkedSource, Pi.single_apply, hCB, hCD, hBD,
    Ne.symm hCB, Ne.symm hCD, Ne.symm hBD, hCM.ne, Ne.symm hCM.ne,
    hMB.ne, hMD] at gc gm gb gd
  have hgC : green C = 6 / 7 := by linarith only [gc, gm, gb]
  have hgB : green B = 4 / 7 := by linarith only [gc, gm, gb]
  have hgD : green D = 1 / 3 := by linarith only [gd]
  let S : Finset V := (Finset.univ.erase B).erase D
  let E : Finset V := S.filter (fun i => weight i = 3)
  have hterm : ∀ i ∈ S, ((weight i : 𝕜) - 2) * coeff i =
      if weight i = 3 then (1 : 𝕜) / 3 else 0 := by
    intro i hi
    have hiD : i ≠ D := (Finset.mem_erase.mp hi).1
    have hiB : i ≠ B := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    by_cases hi3 : weight i = 3
    · have hiC : i ≠ C := by intro h; have := congrArg weight h; omega
      have hiM : i ≠ M := by intro h; have := congrArg weight h; omega
      have hiso := no_adj_outside_two_path G hedges i hiC hiM hiB
      have hr := graph_isolated_row G (fun j => (weight j : 𝕜)) coeff
        (fun j => (weight j : 𝕜) - 2) hrow i hiso
      dsimp only at hr
      rw [hi3] at hr
      norm_num at hr
      rw [if_pos hi3, hi3]
      norm_num
      linarith only [hr]
    · have hi2 : weight i = 2 := (hother i hiB hiD).resolve_right hi3
      norm_num [hi2]
  have hmass : noncoreSourceMass (fun i => (weight i : 𝕜)) coeff B D =
      (E.card : 𝕜) / 3 := by
    change (∑ i ∈ S, ((weight i : 𝕜) - 2) * coeff i) = _
    calc
      _ = ∑ i ∈ S, if weight i = 3 then (1 : 𝕜) / 3 else 0 :=
        Finset.sum_congr rfl hterm
      _ = ∑ i ∈ E, (1 : 𝕜) / 3 := by
        change _ = ∑ i ∈ S.filter (fun i => weight i = 3), (1 : 𝕜) / 3
        rw [Finset.sum_filter]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hsource := canonical_source_sum_split (fun i => (weight i : 𝕜)) coeff B D hBD
  dsimp only at hsource
  rw [hB, hD, hb, hd, hmass] at hsource
  refine ⟨E.card, ?_, ?_, ?_⟩
  · rw [threeMarkedSource_dotProduct, hc, hb, hd]
    norm_num
  · rw [threeMarkedSource_dotProduct, hgC, hgB, hgD]
    norm_num
  · rw [hsource]
    ring

section Source

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- Under the actual beta-three source equations and budgets, the canonical
marked vertex cannot share a component with a core vertex. The proof obtains
the actual two-edge path and excludes every possible number of extra
weight-three vertices by an integer-cardinality contradiction. -/
theorem beta_three_core_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → 𝕜) (C B D : V)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hother : ∀ i, i ≠ B → i ≠ D → weight i = 2 ∨ weight i = 3)
    (hseparate : ¬ G.Reachable B D) (hnadj : ¬ G.Adj C B)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : 𝕜))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : 𝕜)) *ᵥ coeff =
      fun i => (weight i : 𝕜) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B - coeff D)
    (hv : -1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D)
    (hprojection :
      (-1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun i => (weight i : 𝕜)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff) ^ 2) :
    ¬ G.Reachable C B := by
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  obtain ⟨hcore, hcharge⟩ := graph_charge_budgets_of_source_budgets
    (fun i => (weight i : 𝕜)) coeff C B D (3 : 𝕜) hBD
    (by change (weight B : 𝕜) = 3; exact_mod_cast hB)
    (by change (weight D : 𝕜) = 3; exact_mod_cast hD) (hcoeff C) hell
    (by simpa only [show (2 : 𝕜) - 3 = -1 by norm_num] using hv)
  have hunique := heavy_vertices_eq_of_graph_charge G weight coeff B D 3
    (Or.inl rfl) hweight hB hD hother hseparate hA hrow hcoeff hcore hcharge
  intro hreach
  obtain ⟨M, hM, hCM, hMB, hexhaust, _⟩ :=
    exists_canonical_middle_of_two_edge_connection G weight hweight hunique
      (by rw [hB]; omega : 2 < weight B) hCB hnadj hreach hedges
  let A := graphWeightMatrix G (fun i => (weight i : 𝕜))
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  have hgreen : A *ᵥ (A⁻¹ *ᵥ threeMarkedSource C B D) = threeMarkedSource C B D := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  obtain ⟨k, hkell, hkg, hkv⟩ := beta_three_core_contact_values G weight coeff
    (A⁻¹ *ᵥ threeMarkedSource C B D) C M B D hC hM hB hD hBD hother
    hCM hMB hexhaust hrow hgreen
  change (-1 + dotProduct (fun i => (weight i : 𝕜) - 2) coeff) *
      (dotProduct (threeMarkedSource C B D) (A⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff) ^ 2 at hprojection
  rw [hkell, hkg, hkv] at hprojection
  have hcast : (4 : 𝕜) * (k : 𝕜) = 3 := by nlinarith only [hprojection]
  have hnat : 4 * k = 3 := by exact_mod_cast hcast
  omega

end Source

end KltDP.LinearAlgebra
