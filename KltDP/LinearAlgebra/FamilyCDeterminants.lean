import KltDP.LinearAlgebra.FamilyCClassification
import KltDP.LinearAlgebra.ABDeterminants

/-!
# Actual matrix values for family C

The actual two edges of family C select two weight-(3,2) principal blocks.
Every other vertex is isolated. Their actual complementary weight product
gives exceptional determinant 2400. The full bordered determinant is 720
when the actual marked inverse quadratic form is 13/10.

The canonical coefficients and the source values ell=1/5 and v=2/15 are
also derived directly from the full graph matrix equation and the actual
singleton neighbor sets. No coefficient value or determinant is assumed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Fintype V] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A finite actual weight product with one exceptional index. -/
theorem prod_weights_one_exception (S : Finset V) (weight : V → 𝕜)
    (T : V) (hT : T ∈ S) (hother : ∀ i ∈ S, i ≠ T → weight i = 2) :
    (∏ i ∈ S, weight i) = weight T * 2 ^ (S.card - 1) := by
  have hprod := Finset.prod_erase_mul S weight hT
  have hrest : (∏ i ∈ S.erase T, weight i) = (2 : 𝕜) ^ (S.erase T).card := by
    calc
      _ = ∏ _i ∈ S.erase T, (2 : 𝕜) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hother i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1
      _ = _ := by simp
  rw [Finset.card_erase_of_mem hT] at hrest
  rw [← hprod, hrest]
  ring

/-- The exceptional determinant is computed from actual adjacency and
actual weights. The four edge endpoints are selected by an explicit
injective map, and the remaining six vertices supply one weight three
and five weights two. -/
theorem familyC_exceptional_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (B L D M T : V) (hcard : Fintype.card V = 10)
    (hB : weight B = 3) (hL : weight L = 2)
    (hD : weight D = 3) (hM : weight M = 2) (hT : weight T = 3)
    (hBD : B ≠ D) (hLM : L ≠ M) (hTB : T ≠ B) (hTD : T ≠ D)
    (hBL : G.Adj B L) (hDM : G.Adj D M)
    (hedges : G.edgeFinset = {s(B, L), s(D, M)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    (graphWeightMatrix G weight).det = 2400 := by
  classical
  have hBM : B ≠ M := by intro h; have := congrArg weight h; linarith
  have hLD : L ≠ D := by intro h; have := congrArg weight h; linarith
  have hTL : T ≠ L := by intro h; have := congrArg weight h; linarith
  have hTM : T ≠ M := by intro h; have := congrArg weight h; linarith
  have hadj (v w : V) : G.Adj v w ↔
      ((v = B ∧ w = L) ∨ (v = L ∧ w = B)) ∨
      ((v = D ∧ w = M) ∨ (v = M ∧ w = D)) := by
    calc
      G.Adj v w ↔ s(v, w) ∈ G.edgeFinset := by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      _ ↔ _ := by
        rw [hedges]
        simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  let f : Fin 2 ⊕ Fin 2 → V := Sum.elim
    (fun i => if i = 0 then B else L) (fun i => if i = 0 then D else M)
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j <;>
      simp_all [f, hBL.ne, Ne.symm hBL.ne, hDM.ne, Ne.symm hDM.ne]
  let e : (Fin 2 ⊕ Fin 2) ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = B ∨ v = L ∨ v = D ∨ v = M := by
    simp [Set.mem_range, e, f, Sum.exists, Fin.exists_fin_succ, eq_comm, or_assoc]
  have hisolated : ∀ v, v ∉ Set.range e → ∀ w, ¬ G.Adj v w := by
    intro v hv
    have hneq : v ≠ B ∧ v ≠ L ∧ v ≠ D ∧ v ≠ M := by
      simpa only [hrange, not_or] using hv
    exact no_adj_outside_pair_edges G B L D M hedges v hneq.1 hneq.2.1
      hneq.2.2.1 hneq.2.2.2
  have hblockMatrix : (graphWeightMatrix G weight).submatrix e e =
      Matrix.fromBlocks !![(3 : 𝕜), -1; -1, 2] 0 0 !![(3 : 𝕜), -1; -1, 2] := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, e, f,
        graphWeightMatrix_apply, hadj, hB, hL, hD, hM,
        hBL.ne, Ne.symm hBL.ne, hDM.ne, Ne.symm hDM.ne,
        hBD, Ne.symm hBD, hBM, Ne.symm hBM, hLD, Ne.symm hLD,
        hLM, Ne.symm hLM]
  have hblock : ((graphWeightMatrix G weight).submatrix e e).det = 25 := by
    rw [hblockMatrix, Matrix.det_fromBlocks_zero₂₁]
    norm_num
  have hTout : T ∈ outsideRange e := by
    rw [mem_outsideRange, hrange]
    exact not_or.mpr ⟨hTB, not_or.mpr ⟨hTL, not_or.mpr ⟨hTD, hTM⟩⟩⟩
  have hprod := prod_weights_one_exception (outsideRange e) weight T hTout
    (fun i hi hiT => by
      have hout : i ≠ B ∧ i ≠ L ∧ i ≠ D ∧ i ≠ M := by
        simpa only [mem_outsideRange, hrange, not_or] using hi
      exact hother i hout.1 hout.2.2.1 hiT)
  have hcount : (outsideRange e).card = 6 := by
    rw [card_outsideRange, hcard]
    norm_num
  rw [graph_det_eq_principal_mul_complement G weight e hisolated,
    hblock, hprod, hcount, hT]
  norm_num

/-- The family-C coefficients and row values follow from the actual full
canonical equation and the actual fixed component adjacency. -/
theorem familyC_source_row_values
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (C B L D M T : V)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hC : weight C = 2) (hB : weight B = 3) (hL : weight L = 2)
    (hD : weight D = 3) (hM : weight M = 2) (hT : weight T = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hCiso : ∀ v, ¬ G.Adj C v) (hTiso : ∀ v, ¬ G.Adj T v)
    (hnB : G.neighborFinset B = {L}) (hnL : G.neighborFinset L = {B})
    (hnD : G.neighborFinset D = {M}) (hnM : G.neighborFinset M = {D})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2) :
    coeff C = 0 ∧ coeff B = 2 / 5 ∧ coeff L = 1 / 5 ∧
      coeff D = 2 / 5 ∧ coeff M = 1 / 5 ∧ coeff T = 1 / 3 ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 5 ∧
      -1 + dotProduct (fun i => weight i - 2) coeff = 2 / 15 := by
  have hc := graph_isolated_row G weight coeff (fun i => weight i - 2) hrow C hCiso
  have ht := graph_isolated_row G weight coeff (fun i => weight i - 2) hrow T hTiso
  dsimp only at hc ht
  rw [hC] at hc
  rw [hT] at ht
  have hb := congrFun hrow B
  have hl := congrFun hrow L
  have hd := congrFun hrow D
  have hm := congrFun hrow M
  rw [graphWeightMatrix_mulVec_apply, hnB, Finset.sum_singleton, hB] at hb
  rw [graphWeightMatrix_mulVec_apply, hnL, Finset.sum_singleton, hL] at hl
  rw [graphWeightMatrix_mulVec_apply, hnD, Finset.sum_singleton, hD] at hd
  rw [graphWeightMatrix_mulVec_apply, hnM, Finset.sum_singleton, hM] at hm
  have hc' : coeff C = 0 := by linarith only [hc]
  have hb' : coeff B = 2 / 5 := by linarith only [hb, hl]
  have hl' : coeff L = 1 / 5 := by linarith only [hb, hl]
  have hd' : coeff D = 2 / 5 := by linarith only [hd, hm]
  have hm' : coeff M = 1 / 5 := by linarith only [hd, hm]
  have ht' : coeff T = 1 / 3 := by linarith only [ht]
  have hsource := canonical_source_sum_extras weight coeff B D ({T} : Finset V) 3
    hBD hB hD
    (fun t ht => by
      have heq := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hTB, hTD, hT⟩)
    (fun i hiB hiD hiT => hother i hiB hiD (by simpa only [Finset.mem_singleton] using hiT))
  simp only [Finset.sum_singleton] at hsource
  refine ⟨hc', hb', hl', hd', hm', ht', ?_, ?_⟩
  · rw [threeMarkedSource_dotProduct, hc', hb', hd']
    norm_num
  · rw [hsource, hb', hd', ht']
    norm_num

/-- The bordered determinant follows from the actual exceptional matrix
and actual marked Green energy. The energy hypothesis remains an explicit
upstream inverse-matrix obligation, rather than an assumed determinant. -/
theorem familyC_bordered_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (C B L D M T : V) (hcard : Fintype.card V = 10)
    (hB : weight B = 3) (hL : weight L = 2)
    (hD : weight D = 3) (hM : weight M = 2) (hT : weight T = 3)
    (hBD : B ≠ D) (hLM : L ≠ M) (hTB : T ≠ B) (hTD : T ≠ D)
    (hBL : G.Adj B L) (hDM : G.Adj D M)
    (hedges : G.edgeFinset = {s(B, L), s(D, M)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hg : dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 13 / 10) :
    (graphWeightMatrix G weight).det = 2400 ∧
      (borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1)).det = 720 := by
  have hd := familyC_exceptional_det G weight B L D M T hcard hB hL hD hM hT
    hBD hLM hTB hTD hBL hDM hedges hother
  refine ⟨hd, ?_⟩
  rw [bordered_det_of_ten_vertices _ _ hA hcard, hd, hg]
  norm_num

end KltDP.LinearAlgebra
