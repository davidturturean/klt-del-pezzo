import KltDP.LinearAlgebra.ABDeterminants
import KltDP.LinearAlgebra.FamilyDAllocation

/-!
# Actual exceptional and bordered determinants for family D

The two possible edge sets determine actual principal blocks of the graph
matrix. The complementary product is computed from four distinct vertices
of weight three and weight two everywhere else. The ten-vertex count then
gives the exceptional determinants, and the actual inverse quadratic form
gives the bordered determinants.

The graph allocation and the Green energy remain separate inputs here.
This module makes no geometric realization or full classification claim.

Reuse: `GraphDeterminantDecomposition` supplies the actual graph block split,
and `bordered_det_of_ten_vertices` supplies the full bordered Schur formula.
Pinned Mathlib's `prod_erase_mul`, `det_fin_two` and
`det_fromBlocks_zero₂₁` suffice; the corresponding current official Mathlib
proofs were also reviewed. No newer source or tree-library port is needed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Fintype V] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A finite weight product with four actual distinct exceptional indices.
The exponent is the cardinality of the actual remaining index set. -/
theorem prod_weights_four_exceptions (S : Finset V) (weight : V → 𝕜)
    (B D T U : V) (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hB : B ∈ S) (hD : D ∈ S) (hT : T ∈ S) (hU : U ∈ S)
    (hother : ∀ i ∈ S, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2) :
    (∏ i ∈ S, weight i) =
      weight B * weight D * weight T * weight U * 2 ^ (S.card - 4) := by
  have hD' : D ∈ S.erase B := by simp [hD, Ne.symm hBD]
  have hT' : T ∈ (S.erase B).erase D := by simp [hT, hTB, hTD]
  have hU' : U ∈ (S.erase B).erase D := by simp [hU, hUB, hUD]
  have hfirst := Finset.prod_erase_mul S weight hB
  have hsecond := Finset.prod_erase_mul (S.erase B) weight hD'
  have hrest := prod_weights_two_exceptions ((S.erase B).erase D) weight T U
    hTU hT' hU' (fun i hi hiT hiU => by
      have hiD := (Finset.mem_erase.mp hi).1
      have hiB := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hiS := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).2
      exact hother i hiS hiB hiD hiT hiU)
  have hcount : ((S.erase B).erase D).card - 2 = S.card - 4 := by
    rw [Finset.card_erase_of_mem hD', Finset.card_erase_of_mem hB]
    omega
  rw [hcount] at hrest
  rw [← hfirst, ← hsecond, hrest]
  ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Family D1's actual exceptional determinant. The unique actual edge
is canonical, and the four actual higher-weight vertices are distinct. -/
theorem familyD1_exceptional_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M B D T U : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hedges : G.edgeFinset = {s(C, M)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2) :
    (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 3888 := by
  classical
  let f : Fin 2 → V := fun i => if i = 0 then C else M
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, hCM.ne, Ne.symm hCM.ne]
  let e : Fin 2 ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = C ∨ v = M := by
    simp [Set.mem_range, e, f, Fin.exists_fin_succ, eq_comm]
  have hepair : G.edgeFinset = {s(C, M), s(C, M)} := by simpa using hedges
  have hisolated : ∀ v, v ∉ Set.range e → ∀ u, ¬ G.Adj v u := by
    intro v hv
    have hvC : v ≠ C := fun h => hv ((hrange v).mpr (Or.inl h))
    have hvM : v ≠ M := fun h => hv ((hrange v).mpr (Or.inr h))
    exact no_adj_outside_pair_edges G C M C M hepair v hvC hvM hvC hvM
  have hblock : ((graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e).det = 3 := by
    rw [Matrix.det_fin_two]
    norm_num [Matrix.submatrix_apply, e, f, graphWeightMatrix_apply, hC, hM,
      hCM.ne, Ne.symm hCM.ne, hCM, hCM.symm]
  have hout (v : V) (hv : weight v = 3) : v ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    rintro (rfl | rfl) <;> omega
  have hprod := prod_weights_four_exceptions (outsideRange e)
    (fun i => (weight i : 𝕜)) B D T U hBD hTB hTD hUB hUD hTU
    (hout B hB) (hout D hD) (hout T hT) (hout U hU)
    (fun i _ hiB hiD hiT hiU => by
      change (weight i : 𝕜) = 2
      simp only [hother i hiB hiD hiT hiU, Nat.cast_ofNat])
  have hcount : (outsideRange e).card = 8 := by
    rw [card_outsideRange, hcard]
    norm_num
  rw [graph_det_eq_principal_mul_complement G (fun i => (weight i : 𝕜)) e hisolated,
    hblock, hprod, hcount]
  norm_num [hB, hD, hT, hU]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Family D2's actual exceptional determinant, with a second actual
canonical edge outside the six fixed vertices. -/
theorem familyD2_exceptional_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M B D T U x y : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hxy : x ≠ y)
    (hx : x ∉ ({C, M, B, D, T, U} : Finset V))
    (hy : y ∉ ({C, M, B, D, T, U} : Finset V))
    (hx2 : weight x = 2) (hy2 : weight y = 2)
    (hedges : G.edgeFinset = {s(C, M), s(x, y)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2) :
    (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2916 := by
  classical
  have hx' := hx
  have hy' := hy
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx' hy'
  have hadj (v w : V) : G.Adj v w ↔
      ((v = C ∧ w = M) ∨ (v = M ∧ w = C)) ∨
      ((v = x ∧ w = y) ∨ (v = y ∧ w = x)) := by
    calc
      G.Adj v w ↔ s(v, w) ∈ G.edgeFinset := by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      _ ↔ _ := by rw [hedges]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  let f : Fin 2 ⊕ Fin 2 → V := Sum.elim
    (fun i => if i = 0 then C else M) (fun i => if i = 0 then x else y)
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j <;>
      simp_all [f, hCM.ne, Ne.symm hCM.ne]
  let e : (Fin 2 ⊕ Fin 2) ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = C ∨ v = M ∨ v = x ∨ v = y := by
    simp [Set.mem_range, e, f, Sum.exists, Fin.exists_fin_succ, eq_comm, or_assoc]
  have hisolated : ∀ v, v ∉ Set.range e → ∀ w, ¬ G.Adj v w := by
    intro v hv
    have hneq : v ≠ C ∧ v ≠ M ∧ v ≠ x ∧ v ≠ y := by
      simpa only [hrange, not_or] using hv
    exact no_adj_outside_pair_edges G C M x y hedges v hneq.1 hneq.2.1
      hneq.2.2.1 hneq.2.2.2
  have hblockMatrix :
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e =
        Matrix.fromBlocks !![(2 : 𝕜), -1; -1, 2] 0 0 !![(2 : 𝕜), -1; -1, 2] := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, e, f,
        graphWeightMatrix_apply, hadj, hC, hM, hx2, hy2, hCM.ne, Ne.symm hCM.ne,
        hxy, Ne.symm hxy, hx'.1, hx'.2.1, hy'.1, hy'.2.1,
        Ne.symm hx'.1, Ne.symm hx'.2.1, Ne.symm hy'.1, Ne.symm hy'.2.1]
  have hblock : ((graphWeightMatrix G (fun i => (weight i : 𝕜))).submatrix e e).det = 9 := by
    rw [hblockMatrix, Matrix.det_fromBlocks_zero₂₁]
    norm_num
  have hout (v : V) (hv : weight v = 3) : v ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    rintro (rfl | rfl | rfl | rfl) <;> omega
  have hprod := prod_weights_four_exceptions (outsideRange e)
    (fun i => (weight i : 𝕜)) B D T U hBD hTB hTD hUB hUD hTU
    (hout B hB) (hout D hD) (hout T hT) (hout U hU)
    (fun i _ hiB hiD hiT hiU => by
      change (weight i : 𝕜) = 2
      simp only [hother i hiB hiD hiT hiU, Nat.cast_ofNat])
  have hcount : (outsideRange e).card = 6 := by
    rw [card_outsideRange, hcard]
    norm_num
  rw [graph_det_eq_principal_mul_complement G (fun i => (weight i : 𝕜)) e hisolated,
    hblock, hprod, hcount]
  norm_num [hB, hD, hT, hU]

/-- The two actual family-D completions with their exceptional and full
bordered determinants. The edge alternative and leftover counts are derived
from the closed canonical edge, actual isolated higher-weight vertices and
the total edge bound. The Green energy is supplied as an actual matrix
quadratic form, to be discharged by the separate canonical Green theorem. -/
theorem familyD_determinants
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
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2)
    (hA : IsUnit (graphWeightMatrix G (fun i => (weight i : 𝕜))))
    (hg : dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G (fun i => (weight i : 𝕜)))⁻¹ *ᵥ
        threeMarkedSource C B D) = (4 : 𝕜) / 3) :
    (G.edgeFinset = {s(C, M)} ∧
      (Finset.univ \ ({C, M, B, D, T, U} : Finset V)).card = 4 ∧
      (∀ v ∈ Finset.univ \ ({C, M, B, D, T, U} : Finset V),
        weight v = 2 ∧ ∀ w, ¬ G.Adj v w) ∧
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 3888 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : 𝕜)))
        (threeMarkedSource C B D) (-1)).det = 1296) ∨
    (∃ x y, G.Adj x y ∧ x ∉ ({C, M, B, D, T, U} : Finset V) ∧
      y ∉ ({C, M, B, D, T, U} : Finset V) ∧ weight x = 2 ∧ weight y = 2 ∧
      G.edgeFinset = {s(C, M), s(x, y)} ∧
      (Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V)).card = 2 ∧
      (∀ v ∈ Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V),
        weight v = 2 ∧ ∀ w, ¬ G.Adj v w) ∧
      (graphWeightMatrix G (fun i => (weight i : 𝕜))).det = 2916 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : 𝕜)))
        (threeMarkedSource C B D) (-1)).det = 972) := by
  have hborder := bordered_det_of_ten_vertices
    (graphWeightMatrix G (fun i => (weight i : 𝕜))) (threeMarkedSource C B D) hA hcard
  rw [hg] at hborder
  rcases familyD_remaining_vertices G weight C M B D T U hcard hC hM hB hD hT hU
    hBD hTB hTD hUB hUD hTU hCM hnC hnM hBiso hDiso hTiso hUiso hedges hother with
    ⟨he, hc, hremaining⟩ | ⟨x, y, hxy, hx, hy, hx2, hy2, he, hc, hremaining⟩
  · have hd := familyD1_exceptional_det (𝕜 := 𝕜) G weight C M B D T U hcard
      hC hM hB hD hT hU hBD hTB hTD hUB hUD hTU hCM he hother
    left
    refine ⟨he, hc, hremaining, hd, ?_⟩
    rw [hborder, hd]
    norm_num
  · have hd := familyD2_exceptional_det (𝕜 := 𝕜) G weight C M B D T U x y hcard
      hC hM hB hD hT hU hBD hTB hTD hUB hUD hTU hCM hxy.ne hx hy hx2 hy2 he hother
    right
    refine ⟨x, y, hxy, hx, hy, hx2, hy2, he, hc, hremaining, hd, ?_⟩
    rw [hborder, hd]
    norm_num

end KltDP.LinearAlgebra
