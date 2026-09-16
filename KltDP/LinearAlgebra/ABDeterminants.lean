import KltDP.LinearAlgebra.GraphDeterminantDecomposition
import KltDP.LinearAlgebra.SingleExtraAllocation
import KltDP.LinearAlgebra.SchurComplement
import Mathlib.Tactic

/-!
# Actual exceptional and bordered determinants for families A and B

The small principal blocks are selected by explicit injective maps of their
actual vertices. The actual edge finset proves both their entries and the
isolation of the complement. The remaining weight product and vertex count
then determine the full determinant.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Family A1's exceptional determinant from its actual single edge and
actual ten-vertex weight data. This is a graph determinant theorem. -/
theorem familyA1_exceptional_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C T B D : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) (hCT : G.Adj C T)
    (hedges : G.edgeFinset = {s(C, T)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2880 := by
  classical
  let f : Fin 2 → V := fun i => if i = 0 then C else T
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, hCT.ne, Ne.symm hCT.ne]
  let e : Fin 2 ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = C ∨ v = T := by
    simp [Set.mem_range, e, f, Fin.exists_fin_succ, eq_comm]
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hepair : G.edgeFinset = {s(C, T), s(C, T)} := by simpa using hedges
  have hisolated : ∀ v, v ∉ Set.range e → ∀ u, ¬ G.Adj v u := by
    intro v hv
    have hvC : v ≠ C := fun h => hv ((hrange v).mpr (Or.inl h))
    have hvT : v ≠ T := fun h => hv ((hrange v).mpr (Or.inr h))
    exact no_adj_outside_pair_edges G C T C T hepair v hvC hvT hvC hvT
  have hblock : ((graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e).det = 5 := by
    rw [Matrix.det_fin_two]
    norm_num [Matrix.submatrix_apply, e, f, graphWeightMatrix_apply, hC, hT,
      hCT.ne, Ne.symm hCT.ne, hCT, hCT.symm]
  have hBout : B ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨Ne.symm hCB, Ne.symm hTB⟩
  have hDout : D ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨Ne.symm hCD, Ne.symm hTD⟩
  have hprod := prod_weights_two_exceptions (outsideRange e)
    (fun i => (weight i : 𝕜)) B D hBD hBout hDout (fun i hi hiB hiD => by
      have hi' := (mem_outsideRange e i).mp hi
      have hiT : i ≠ T := fun h => hi' ((hrange i).mpr (Or.inr h))
      change (weight i : 𝕜) = 2
      exact_mod_cast hother i hiB hiD hiT)
  have hcount : (outsideRange e).card = 8 := by rw [card_outsideRange, hcard]; norm_num
  rw [graph_det_eq_principal_mul_complement G (fun i => (weight i : 𝕜)) e hisolated,
    hblock, hprod, hcount]
  dsimp only
  rw [hB, hD]
  norm_num

/-- Family B's exceptional determinant from its actual exhausted two-edge
path and actual ten-vertex weight data. -/
theorem familyB_exceptional_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M T B D : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hCM : G.Adj C M) (hMT : G.Adj M T)
    (hedges : G.edgeFinset = {s(C, M), s(M, T)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2016 := by
  classical
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  let f : Fin 3 → V := fun i => if i.val = 0 then C else if i.val = 1 then M else T
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hCM.ne, Ne.symm hCM.ne, hMT.ne, Ne.symm hMT.ne, hCT, Ne.symm hCT]
  let e : Fin 3 ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = C ∨ v = M ∨ v = T := by
    simp [Set.mem_range, e, f, Fin.exists_fin_succ, eq_comm]
  have hisolated : ∀ v, v ∉ Set.range e → ∀ u, ¬ G.Adj v u := by
    intro v hv
    have hvC : v ≠ C := fun h => hv ((hrange v).mpr (Or.inl h))
    have hvM : v ≠ M := fun h => hv ((hrange v).mpr (Or.inr (Or.inl h)))
    have hvT : v ≠ T := fun h => hv ((hrange v).mpr (Or.inr (Or.inr h)))
    exact no_adj_outside_two_path G hedges v hvC hvM hvT
  have hnotCT : ¬ G.Adj C T := by
    rw [adj_iff_of_edgeFinset_eq_two_path G hedges]
    simp [hCM.ne, Ne.symm hCM.ne, hMT.ne, Ne.symm hMT.ne, hCT, Ne.symm hCT]
  have hnotTC : ¬ G.Adj T C := fun h => hnotCT h.symm
  have hblock : ((graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e).det = 7 := by
    have he0 : e 0 = C := rfl
    have he1 : e 1 = M := rfl
    have he2 : e 2 = T := rfl
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, he0, he1, he2]
    norm_num [graphWeightMatrix_apply, hC, hM, hT,
      hCM.ne, Ne.symm hCM.ne, hMT.ne, Ne.symm hMT.ne, hCT, Ne.symm hCT,
      hCM, hCM.symm, hMT, hMT.symm, hnotCT, hnotTC]
  have hBout : B ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨Ne.symm hCB, not_or.mpr ⟨Ne.symm hMB, Ne.symm hTB⟩⟩
  have hDout : D ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨Ne.symm hCD, not_or.mpr ⟨Ne.symm hMD, Ne.symm hTD⟩⟩
  have hprod := prod_weights_two_exceptions (outsideRange e)
    (fun i => (weight i : 𝕜)) B D hBD hBout hDout (fun i hi hiB hiD => by
      have hi' := (mem_outsideRange e i).mp hi
      have hiT : i ≠ T := fun h => hi' ((hrange i).mpr (Or.inr (Or.inr h)))
      change (weight i : 𝕜) = 2
      exact_mod_cast hother i hiB hiD hiT)
  have hcount : (outsideRange e).card = 7 := by rw [card_outsideRange, hcard]; norm_num
  rw [graph_det_eq_principal_mul_complement G (fun i => (weight i : 𝕜)) e hisolated,
    hblock, hprod, hcount]
  dsimp only
  rw [hB, hD]
  norm_num

/-- Family A2's exceptional determinant from the actual closed marked
edge and its actual disjoint canonical edge. -/
theorem familyA2_exceptional_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C T B D u v : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) (hCT : G.Adj C T)
    (huv : u ≠ v) (hu : u ∉ ({C, T, B, D} : Finset V))
    (hv : v ∉ ({C, T, B, D} : Finset V))
    (hu2 : weight u = 2) (hv2 : weight v = 2)
    (hedges : G.edgeFinset = {s(C, T), s(u, v)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2160 := by
  classical
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hu' := hu
  have hv' := hv
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu' hv'
  have hadj (x y : V) : G.Adj x y ↔
      ((x = C ∧ y = T) ∨ (x = T ∧ y = C)) ∨
      ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
    calc
      G.Adj x y ↔ s(x, y) ∈ G.edgeFinset := by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      _ ↔ _ := by rw [hedges]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  let f : Fin 2 ⊕ Fin 2 → V := Sum.elim
    (fun i => if i = 0 then C else T) (fun i => if i = 0 then u else v)
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j <;>
      simp_all [f, hCT.ne, Ne.symm hCT.ne]
  let e : (Fin 2 ⊕ Fin 2) ↪ V := ⟨f, hf⟩
  have hrange (w : V) : w ∈ Set.range e ↔ w = C ∨ w = T ∨ w = u ∨ w = v := by
    simp [Set.mem_range, e, f, Sum.exists, Fin.exists_fin_succ, eq_comm, or_assoc]
  have hisolated : ∀ w, w ∉ Set.range e → ∀ z, ¬ G.Adj w z := by
    intro w hw
    have hneq : w ≠ C ∧ w ≠ T ∧ w ≠ u ∧ w ≠ v := by
      simpa only [hrange, not_or] using hw
    exact no_adj_outside_pair_edges G C T u v hedges w hneq.1 hneq.2.1
      hneq.2.2.1 hneq.2.2.2
  have hblockMatrix :
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e =
        Matrix.fromBlocks !![(2 : 𝕜), -1; -1, 3] 0 0 !![(2 : 𝕜), -1; -1, 2] := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, e, f,
        graphWeightMatrix_apply, hadj, hC, hT, hu2, hv2, hCT.ne, Ne.symm hCT.ne,
        huv, Ne.symm huv, hu'.1, hu'.2.1, hv'.1, hv'.2.1,
        Ne.symm hu'.1, Ne.symm hu'.2.1, Ne.symm hv'.1, Ne.symm hv'.2.1]
  have hblock : ((graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e).det = 15 := by
    rw [hblockMatrix, Matrix.det_fromBlocks_zero₂₁]
    norm_num
  have hBout : B ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨Ne.symm hCB, not_or.mpr ⟨Ne.symm hTB,
      not_or.mpr ⟨Ne.symm hu'.2.2.1, Ne.symm hv'.2.2.1⟩⟩⟩
  have hDout : D ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨Ne.symm hCD, not_or.mpr ⟨Ne.symm hTD,
      not_or.mpr ⟨Ne.symm hu'.2.2.2, Ne.symm hv'.2.2.2⟩⟩⟩
  have hprod := prod_weights_two_exceptions (outsideRange e)
    (fun i => (weight i : 𝕜)) B D hBD hBout hDout (fun i hi hiB hiD => by
      have hi' := (mem_outsideRange e i).mp hi
      have hiT : i ≠ T := fun h => hi' ((hrange i).mpr (Or.inr (Or.inl h)))
      change (weight i : 𝕜) = 2
      exact_mod_cast hother i hiB hiD hiT)
  have hcount : (outsideRange e).card = 6 := by rw [card_outsideRange, hcard]; norm_num
  rw [graph_det_eq_principal_mul_complement G (fun i => (weight i : 𝕜)) e hisolated,
    hblock, hprod, hcount]
  dsimp only
  rw [hB, hD]
  norm_num

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With ten exceptional vertices, the already proved bordered determinant
formula has positive sign. This identifies the actual full Gram matrix. -/
theorem bordered_det_of_ten_vertices (A : Matrix V V 𝕜) (p : V → 𝕜)
    (hA : IsUnit A) (hcard : Fintype.card V = 10) :
    (borderedGram A p (-1)).det = A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1) := by
  rw [det_minusOne_borderedGram hA, hcard]
  norm_num

section Source

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- The source-facing A1/A2 completion and determinants. The alternative
edge sets and their remaining vertex counts are proved from the actual
source hypotheses; no table-row predicate is assumed. -/
theorem beta_three_adjacent_extra_determinants
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → 𝕜) (C B D T : V) (hcard : Fintype.card V = 10)
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
    (G.edgeFinset = {s(C, T)} ∧
      (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
      (∀ v ∈ Finset.univ \ ({C, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2880 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : 𝕜)))
        (threeMarkedSource C B D) (-1)).det = 768) ∨
    (∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
      v ∉ ({C, T, B, D} : Finset V) ∧ weight u = 2 ∧ weight v = 2 ∧
      G.edgeFinset = {s(C, T), s(u, v)} ∧
      (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 ∧
      (∀ w ∈ Finset.univ \ ({u, v, C, T, B, D} : Finset V),
        weight w = 2 ∧ ∀ z, ¬ G.Adj w z) ∧
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2160 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : 𝕜)))
        (threeMarkedSource C B D) (-1)).det = 576) := by
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  obtain ⟨hnC, hnT, hBiso, hDiso, _, _, _, _⟩ :=
    beta_three_adjacent_extra_structure G weight coeff C B D T hweight hC hB hD hT
      hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv
  obtain ⟨_, _, _, _, _, hg⟩ :=
    beta_three_adjacent_extra_data G weight coeff C B D T hweight hC hB hD hT
      hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv
  have hborder := bordered_det_of_ten_vertices
    (graphWeightMatrix G (fun i => (weight i : 𝕜))) (threeMarkedSource C B D)
    (isUnit_of_posDef hA) hcard
  rw [hg] at hborder
  rcases familyA_remaining_vertices G weight C T B D hcard hC hT hB hD hTB hTD hBD
    hCT hnC hnT hBiso hDiso hedges hother with
    ⟨he, hc, hremaining⟩ | ⟨u, v, huv, hu, hv', hu2, hv2, he, hc, hremaining⟩
  · have hd := familyA1_exceptional_det (𝕜 := 𝕜) G weight C T B D hcard hC hT hB hD hTB hTD hBD
      hCT he hother
    left
    refine ⟨he, hc, hremaining, hd, ?_⟩
    rw [hborder, hd]
    norm_num
  · have hd := familyA2_exceptional_det (𝕜 := 𝕜) G weight C T B D u v hcard hC hT hB hD hTB hTD hBD
      hCT huv hu hv' hu2 hv2 he hother
    right
    refine ⟨u, v, huv, hu, hv', hu2, hv2, he, hc, hremaining, hd, ?_⟩
    rw [hborder, hd]
    norm_num

/-- The source-facing family-B completion and determinants. The actual
middle, full edge set, five isolated canonical leftovers and both matrix
determinants are derived from the genuine nonadjacent connection. -/
theorem beta_three_nonadjacent_extra_determinants
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → 𝕜) (C B D T : V) (hcard : Fintype.card V = 10)
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
      (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
      (∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2016 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : 𝕜)))
        (threeMarkedSource C B D) (-1)).det = 768 := by
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  obtain ⟨M, hM, hCM, hMT, he, _, _, _, _, hg⟩ :=
    beta_three_nonadjacent_extra_data G weight coeff C B D T hweight hC hB hD hT
      hTB hTD hother hseparate hreach hnadj hedges hA hrow hcoeff hell hv
  obtain ⟨hcount, hremaining⟩ := familyB_remaining_vertices G weight C M T B D hcard
    hC hM hT hB hD hTB hTD hBD hCM hMT he hother
  have hd := familyB_exceptional_det (𝕜 := 𝕜) G weight C M T B D hcard hC hM hT hB hD hTB hTD hBD
    hCM hMT he hother
  refine ⟨M, hM, hCM, hMT, he, hcount, hremaining, hd, ?_⟩
  rw [bordered_det_of_ten_vertices _ _ (isUnit_of_posDef hA) hcard, hd, hg]
  norm_num

end Source

end KltDP.LinearAlgebra
