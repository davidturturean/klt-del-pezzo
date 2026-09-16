import KltDP.LinearAlgebra.TenForestEGraphIsomorphisms
import KltDP.LinearAlgebra.TenForestRowUniqueness

/-!
# A selected candidate row has its own marked weighted model

The row-indexed models below are actual finite graphs with actual weights
and three specified vertices. The realization theorem starts with the
exact row already derived by the classifier and constructs an isomorphism
to that same row's model. It does not combine an unrelated numerical row
with an independent disjunction of graph shapes.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

namespace TenForestRow

def ModelVertex : TenForestRow → Type
  | .a1 => Fin 4 ⊕ Fin 6
  | .a2 => Fin 6 ⊕ Fin 4
  | .b => Fin 5 ⊕ Fin 5
  | .c | .d1 => Fin 6 ⊕ Fin 4
  | .d2 => Fin 8 ⊕ Fin 2
  | .e1 => Fin 6 ⊕ (Fin 0 ⊕ Fin 5)
  | .e2 => Fin 6 ⊕ (Fin 2 ⊕ Fin 3)
  | .e3 => Fin 6 ⊕ (Fin 3 ⊕ Fin 2)
  | .e4 => Fin 6 ⊕ (Fin 4 ⊕ Fin 1)

instance modelVertexFintype (row : TenForestRow) : Fintype row.ModelVertex := by
  cases row <;> dsimp [ModelVertex] <;> infer_instance

instance modelVertexDecidableEq (row : TenForestRow) : DecidableEq row.ModelVertex := by
  cases row <;> dsimp [ModelVertex] <;> infer_instance

def modelGraph : (row : TenForestRow) → SimpleGraph row.ModelVertex
  | .a1 => familyA1Graph
  | .a2 => familyA2Graph
  | .b => familyBGraph
  | .c => familyCGraph
  | .d1 => familyD1Graph
  | .d2 => familyD2Graph
  | .e1 => familyE1Graph
  | .e2 => familyE2Graph
  | .e3 => familyE3Graph
  | .e4 => familyE4Graph

def modelWeight : (row : TenForestRow) → row.ModelVertex → ℕ
  | .a1 => familyA1GraphWeight
  | .a2 => familyA2GraphWeight
  | .b => familyBGraphWeight
  | .c => familyCGraphWeight
  | .d1 => familyD1GraphWeight
  | .d2 => familyD2GraphWeight
  | .e1 => familyEGraphWeight
  | .e2 => familyEGraphWeight
  | .e3 => familyEGraphWeight
  | .e4 => familyEGraphWeight

def modelC : (row : TenForestRow) → row.ModelVertex
  | .a1 => Sum.inl 0
  | .a2 => Sum.inl 2
  | .b => Sum.inl 1
  | .c | .d1 => Sum.inl 0
  | .d2 => Sum.inl 2
  | .e1 | .e2 | .e3 | .e4 => Sum.inl 0

def modelB : (row : TenForestRow) → row.ModelVertex
  | .a1 => Sum.inl 2
  | .a2 => Sum.inl 4
  | .b => Sum.inl 3
  | .c | .d1 => Sum.inl 2
  | .d2 => Sum.inl 4
  | .e1 | .e2 | .e3 | .e4 => Sum.inl 2

def modelD : (row : TenForestRow) → row.ModelVertex
  | .a1 => Sum.inl 3
  | .a2 => Sum.inl 5
  | .b => Sum.inl 4
  | .c | .d1 => Sum.inl 3
  | .d2 => Sum.inl 5
  | .e1 | .e2 | .e3 | .e4 => Sum.inl 3

theorem model_card (row : TenForestRow) : Fintype.card row.ModelVertex = row.beta + 7 := by
  cases row <;>
    dsimp only [ModelVertex, modelVertexFintype, beta] <;>
    norm_num only [Fintype.card_sum, Fintype.card_fin]

theorem model_marked_weights (row : TenForestRow) :
    row.modelWeight row.modelC = 2 ∧ row.modelWeight row.modelB = 3 ∧
      row.modelWeight row.modelD = row.beta := by
  cases row <;> exact ⟨rfl, rfl, rfl⟩

end TenForestRow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact selected row admits an actual weight-preserving graph
isomorphism with its own model, fixing the three distinguished labels.
All hypotheses besides `Realized` are original source data. -/
theorem TenForestRow.Realized.weighted_graph_iso
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (h : row.Realized G weight coeff C B D β)
    (hcard : Fintype.card V = β + 7)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β) (hBD : B ≠ D) :
    ∃ f : row.modelGraph ≃g G,
      f row.modelC = C ∧ f row.modelB = B ∧ f row.modelD = D ∧
      ∀ v, weight (f v) = row.modelWeight v := by
  have hcard' : Fintype.card V = row.beta + 7 :=
    hcard.trans (congrArg (fun n => n + 7) h.1)
  have hD' : weight D = row.beta := hD.trans h.1
  have hd := h.2
  cases row
  case a1 =>
    obtain ⟨T, hTB, hTD, hT, _, _, he, _, hr, _⟩ := hd
    have ho : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
      intro v hvB hvD hvT
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvT, hvB, hvD⟩)).1
    obtain ⟨f, hfC, _, hfB, hfD, hw⟩ := familyA1_weighted_graph_iso G weight
      C T B D hcard' hC hT hB hD' hTB hTD hBD he ho
    exact ⟨f, hfC, hfB, hfD, hw⟩
  case a2 =>
    obtain ⟨T, hTB, hTD, hT, _, _, x, y, hxy, hx, hy, hx2, hy2, he, _, hr, _⟩ := hd
    have ho : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
      intro v hvB hvD hvT
      by_cases hvx : v = x
      · simpa only [hvx] using hx2
      by_cases hvy : v = y
      · simpa only [hvy] using hy2
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvx, hvy, hvC, hvT, hvB, hvD⟩)).1
    obtain ⟨f, _, _, hfC, _, hfB, hfD, hw⟩ := familyA2_weighted_graph_iso G weight
      C T B D x y hcard' hC hT hB hD' hTB hTD hBD hxy hx hy he ho
    exact ⟨f, hfC, hfB, hfD, hw⟩
  case b =>
    obtain ⟨T, hTB, hTD, hT, _, _, M, hM, hCM, _, he, _, hr, _⟩ := hd
    have ho : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
      intro v hvB hvD hvT
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      by_cases hvM : v = M
      · simpa only [hvM] using hM
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvM, hvT, hvB, hvD⟩)).1
    obtain ⟨f, _, hfC, _, hfB, hfD, hw⟩ := familyB_weighted_graph_iso G weight
      C M T B D hcard' hC hM hT hB hD' hTB hTD hBD hCM he ho
    exact ⟨f, hfC, hfB, hfD, hw⟩
  case c =>
    obtain ⟨T, hTB, hTD, hT, hc⟩ := hd
    obtain ⟨L, M, f, hf, hw⟩ := CForestRow_weighted_graph_iso G weight coeff C B D T
      hcard' hC hB hD' hT hTB hTD hBD hc
    exact ⟨f, hf 0, hf 2, hf 3, hw⟩
  case d1 =>
    obtain ⟨T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, M, hCM, hC', hM,
      _, _, _, _, _, _, _, _, _, _, he, _, hr, _⟩ := hd
    have ho : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2 := by
      intro v hvB hvD hvT hvU
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      by_cases hvM : v = M
      · simpa only [hvM] using hM
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvM, hvB, hvD, hvT, hvU⟩)).1
    obtain ⟨f, hf, hw⟩ := familyD1_weighted_graph_iso G weight C M B D T U hcard'
      hC' hM hB hD' hT hU hBD hTB hTD hUB hUD hTU hCM he ho
    exact ⟨f, hf 0, hf 2, hf 3, hw⟩
  case d2 =>
    obtain ⟨T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, M, hCM, hC', hM,
      _, _, _, _, _, _, _, _, _, _, x, y, hxy, hx, hy, hx2, hy2, he, _, hr, _⟩ := hd
    have ho : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2 := by
      intro v hvB hvD hvT hvU
      by_cases hvx : v = x
      · simpa only [hvx] using hx2
      by_cases hvy : v = y
      · simpa only [hvy] using hy2
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      by_cases hvM : v = M
      · simpa only [hvM] using hM
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvx, hvy, hvC, hvM, hvB, hvD, hvT, hvU⟩)).1
    obtain ⟨f, hf, hw⟩ := familyD2_weighted_graph_iso G weight C M B D T U x y hcard'
      hC' hM hB hD' hT hU hBD hTB hTD hUB hUD hTU hCM hxy hx hy he ho
    exact ⟨f, hf 2, hf 4, hf 5, hw⟩
  case e1 =>
    obtain ⟨T, U, hTB, _, hUB, _, hTU, hT, hU, M, hM, hBM, hnB, hnM,
      _, hCiso, hDiso, hTiso, hUiso, _, _, _, _, hZcard, hZweight, _, he, _, _⟩ := hd
    let Z := G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)}
    have hMnat : weight M = 2 := by exact_mod_cast hM
    have hz : ∀ v : {v | v ∉ ({C, B, M, D, T, U} : Finset V)}, weight v.val = 2 := by
      intro v
      exact_mod_cast hZweight v
    obtain ⟨rest⟩ := familyE1_remaining_iso Z hZcard he
    obtain ⟨f, hf, hw⟩ := familyE_fixed_core_weighted_iso G weight C M B D T U
      hC hMnat hB hD' hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso
      familyE1RemainingGraph rest hz
    exact ⟨f, hf 0, hf 2, hf 3, hw⟩
  case e2 =>
    obtain ⟨T, U, hTB, _, hUB, _, hTU, hT, hU, M, hM, hBM, hnB, hnM,
      _, hCiso, hDiso, hTiso, hUiso, _, _, _, _, hZcard, hZweight, _,
      x, y, hxy, he, _, _, _⟩ := hd
    let Z := G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)}
    have hMnat : weight M = 2 := by exact_mod_cast hM
    have hz : ∀ v : {v | v ∉ ({C, B, M, D, T, U} : Finset V)}, weight v.val = 2 := by
      intro v
      exact_mod_cast hZweight v
    obtain ⟨rest⟩ := familyE2_remaining_iso Z hZcard x y hxy he
    obtain ⟨f, hf, hw⟩ := familyE_fixed_core_weighted_iso G weight C M B D T U
      hC hMnat hB hD' hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso
      familyE2RemainingGraph rest hz
    exact ⟨f, hf 0, hf 2, hf 3, hw⟩
  case e3 =>
    obtain ⟨T, U, hTB, _, hUB, _, hTU, hT, hU, M, hM, hBM, hnB, hnM,
      _, hCiso, hDiso, hTiso, hUiso, _, _, _, _, hZcard, hZweight, _,
      x, y, z, hxy, hxz, hyz, he, _, _, _⟩ := hd
    let Z := G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)}
    have hMnat : weight M = 2 := by exact_mod_cast hM
    have hz : ∀ v : {v | v ∉ ({C, B, M, D, T, U} : Finset V)}, weight v.val = 2 := by
      intro v
      exact_mod_cast hZweight v
    obtain ⟨rest⟩ := familyE3_remaining_iso Z hZcard x y z hxy hxz hyz he
    obtain ⟨f, hf, hw⟩ := familyE_fixed_core_weighted_iso G weight C M B D T U
      hC hMnat hB hD' hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso
      familyE3RemainingGraph rest hz
    exact ⟨f, hf 0, hf 2, hf 3, hw⟩
  case e4 =>
    obtain ⟨T, U, hTB, _, hUB, _, hTU, hT, hU, M, hM, hBM, hnB, hnM,
      _, hCiso, hDiso, hTiso, hUiso, _, _, _, _, hZcard, hZweight, _,
      x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he, _, _, _⟩ := hd
    let Z := G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)}
    have hMnat : weight M = 2 := by exact_mod_cast hM
    have hz : ∀ v : {v | v ∉ ({C, B, M, D, T, U} : Finset V)}, weight v.val = 2 := by
      intro v
      exact_mod_cast hZweight v
    obtain ⟨rest⟩ := familyE4_remaining_iso Z hZcard x y z w hxy hxz hxw hyz hyw hzw he
    obtain ⟨f, hf, hw⟩ := familyE_fixed_core_weighted_iso G weight C M B D T U
      hC hMnat hB hD' hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso
      familyE4RemainingGraph rest hz
    exact ⟨f, hf 0, hf 2, hf 3, hw⟩

end KltDP.LinearAlgebra
