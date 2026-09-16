import KltDP.Manuscript.S09.TenForestRemainingDeterminants
import KltDP.LinearAlgebra.TenForestABRemaining
import KltDP.LinearAlgebra.TenForestRowUniqueness

/-!
# All ten actual remaining determinants under the original source hypotheses

The source classifier selects a unique row while retaining its actual
graph witnesses. The relation below records which actual fixed vertices
are removed; their complement is an induced graph with the original
restricted weights. Its determinant, the scalar values, the exceptional
and full bordered determinants, and Delta/det Z are then assembled for
that same row. No classified row or determinant is a source premise.

This is a source-level invariant integration toward Lemma 9.2. The marked
weighted graph isomorphisms are assembled separately. Compilation,
elaborated-type review and transitive axiom audit remain separate gates.
-/

namespace KltDP.Manuscript.S09

open Matrix SimpleGraph KltDP.LinearAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A conclusion relation retaining actual witnesses for the fixed
components removed in the displayed row. The remaining graph is always
the complement in the original vertex type, never a substitute matrix. -/
def TenForestRemainingVertices (row : TenForestRow) (G : SimpleGraph V)
    [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (fixed : Finset V) : Prop :=
  match row with
  | .a1 | .a2 => ∃ T, weight T = 3 ∧ T ≠ B ∧ T ≠ D ∧
      TenForestABCase row G weight coeff C B D T ∧ fixed = {C, T, B, D}
  | .b => ∃ T M, weight T = 3 ∧ weight M = 2 ∧
      TenForestABCase .b G weight coeff C B D T ∧
      G.Adj C M ∧ G.Adj M T ∧ G.edgeFinset = {s(C, M), s(M, T)} ∧
      fixed = {C, M, T, B, D}
  | .c => ∃ T L M, weight T = 3 ∧ (weight L : ℚ) = 2 ∧ (weight M : ℚ) = 2 ∧
      CForestRow G (fun v => (weight v : ℚ)) coeff C B D T ∧
      G.Adj B L ∧ G.Adj D M ∧ G.edgeFinset = {s(B, L), s(D, M)} ∧
      fixed = {C, B, L, D, M, T}
  | .d1 | .d2 => ∃ T U M, weight T = 3 ∧ weight U = 3 ∧ weight M = 2 ∧
      G.Adj C M ∧ G.neighborFinset C = {M} ∧ G.neighborFinset M = {C} ∧
      (∀ v, ¬ G.Adj B v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      TenForestDCase row G weight C M B D T U ∧ fixed = {C, M, B, D, T, U}
  | .e1 | .e2 | .e3 | .e4 => ∃ T U M,
      weight T = 3 ∧ weight U = 3 ∧ (weight M : ℚ) = 2 ∧
      G.Adj B M ∧ G.neighborFinset B = {M} ∧ G.neighborFinset M = {B} ∧
      (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      fixed = {C, B, M, D, T, U} ∧ fixed.card = 6 ∧
      TenForestECase row (G.induce {v | v ∉ fixed})
        (graphWeightMatrix G (fun v => (weight v : ℚ))).det
        (borderedGram (graphWeightMatrix G (fun v => (weight v : ℚ)))
          (threeMarkedSource C B D) (-1)).det

private theorem actual_isolated_complement_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (fixed : Finset V)
    (hremaining : ∀ v ∈ Finset.univ \ fixed, weight v = 2 ∧ ∀ w, ¬ G.Adj v w) :
    (graphWeightMatrix (G.induce {v | v ∉ fixed}) (fun v => weight v.val)).det =
      2 ^ (Finset.univ \ fixed).card := by
  classical
  let S : Finset V := Finset.univ \ fixed
  have hr : ∀ v : {v | v ∉ fixed}, weight v.val = 2 ∧ ∀ u, ¬ G.Adj v.val u := by
    intro v
    exact hremaining v.val
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v.val, v.property⟩)
  have hweights : (fun v : {v | v ∉ fixed} => weight v.val) = fun _ => (2 : ℚ) :=
    funext (fun v => (hr v).1)
  have hgraph : G.induce {v | v ∉ fixed} = ⊥ := by
    ext v u
    change G.Adj v.val u.val ↔ False
    exact iff_false_intro ((hr v).2 u.val)
  have hedges : (G.induce {v | v ∉ fixed}).edgeFinset = ∅ :=
    (SimpleGraph.edgeFinset_inj.mpr hgraph).trans SimpleGraph.edgeFinset_bot
  have hcount : Fintype.card {v | v ∉ fixed} = S.card := by
    let e : {v | v ∉ fixed} ≃ (S : Set V) :=
      Equiv.subtypeEquivRight (fun v => by simp [S])
    exact (Fintype.card_congr e).trans (Fintype.card_coe S)
  rw [hweights]
  exact (canonical_empty_det (G.induce {v | v ∉ fixed}) hedges).trans
    (congrArg (fun m : ℕ => (2 : ℚ) ^ m) hcount)

/-- A selected actual row has its displayed remaining determinant on its
actual induced complement. The small fixed blocks are computed from the
original pairings, and every selected fixed set keeps its graph witnesses. -/
theorem tenForestRealized_remaining_matrix
    (row : TenForestRow) (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D : V) (β : ℕ)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β) (hBD : B ≠ D)
    (h : row.Realized G weight coeff C B D β) :
    ∃ fixed : Finset V, TenForestRemainingVertices row G weight coeff C B D fixed ∧
      (graphWeightMatrix (G.induce {v | v ∉ fixed})
        (fun v => (weight v.val : ℚ))).det = row.remainingDet := by
  classical
  have hvalues := h.values
  have ha := hvalues.2.2.2.2.1
  rcases h with ⟨hβ, h⟩
  cases row with
  | a1 =>
      obtain ⟨T, hTB, hTD, hT, _, _, hc⟩ := h
      exact ⟨{C, T, B, D}, ⟨T, hT, hTB, hTD, hc, rfl⟩,
        tenForest_a1_remaining_det G weight coeff C B D T hc⟩
  | a2 =>
      obtain ⟨T, hTB, hTD, hT, hBi, hDi, hc⟩ := h
      have hD3 : weight D = 3 := hD.trans hβ
      exact ⟨{C, T, B, D}, ⟨T, hT, hTB, hTD, hc, rfl⟩,
        tenForest_a2_remaining_det G weight coeff C B D T hC hT hB hD3 hBD hBi hDi hc⟩
  | b =>
      obtain ⟨T, _, _, hT, _, _, hc⟩ := h
      obtain ⟨M, hM, hCM, hMT, he, _, _, hz⟩ :=
        tenForest_b_remaining_det G weight coeff C B D T hc
      exact ⟨{C, M, T, B, D}, ⟨T, M, hT, hM, hc, hCM, hMT, he, rfl⟩, hz⟩
  | c =>
      obtain ⟨T, _, _, hT, hc⟩ := h
      have hc' := hc
      obtain ⟨L, M, hL, hM, _, _, hBL, hDM, _, _, _, _, he, hcount, hr,
        _, _, _, _, _⟩ := hc
      refine ⟨{C, B, L, D, M, T}, ⟨T, L, M, hT, hL, hM, hc', hBL, hDM, he, rfl⟩, ?_⟩
      have hz := actual_isolated_complement_det G (fun v => (weight v : ℚ))
        {C, B, L, D, M, T} hr
      rw [hcount] at hz
      norm_num at hz
      exact hz
  | d1 =>
      obtain ⟨T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, M, hCM, hC', hM,
        hnC, hnM, _, hBi, hDi, hTi, hUi, _, _, _, hc⟩ := h
      have hD3 : weight D = 3 := hD.trans hβ
      have hf := familyD_fixed_det_factor G weight C M B D T U
        hC' hM hB hD3 hT hU hBD hTB hTD hUB hUD hTU hCM hnC hnM hBi hDi hTi hUi
      refine ⟨{C, M, B, D, T, U},
        ⟨T, U, M, hT, hU, hM, hCM, hnC, hnM, hBi, hDi, hTi, hUi, hc, rfl⟩, ?_⟩
      change (graphWeightMatrix G (fun v => (weight v : ℚ))).det = 3888 at ha
      change (graphWeightMatrix (G.induce {v | v ∉ ({C, M, B, D, T, U} : Finset V)})
        (fun v => (weight v.val : ℚ))).det = 16
      linarith only [hf, ha]
  | d2 =>
      obtain ⟨T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, M, hCM, hC', hM,
        hnC, hnM, _, hBi, hDi, hTi, hUi, _, _, _, hc⟩ := h
      have hD3 : weight D = 3 := hD.trans hβ
      have hf := familyD_fixed_det_factor G weight C M B D T U
        hC' hM hB hD3 hT hU hBD hTB hTD hUB hUD hTU hCM hnC hnM hBi hDi hTi hUi
      refine ⟨{C, M, B, D, T, U},
        ⟨T, U, M, hT, hU, hM, hCM, hnC, hnM, hBi, hDi, hTi, hUi, hc, rfl⟩, ?_⟩
      change (graphWeightMatrix G (fun v => (weight v : ℚ))).det = 2916 at ha
      change (graphWeightMatrix (G.induce {v | v ∉ ({C, M, B, D, T, U} : Finset V)})
        (fun v => (weight v.val : ℚ))).det = 12
      linarith only [hf, ha]
  | e1 | e2 | e3 | e4 =>
      obtain ⟨T, U, hTB, _, hUB, _, hTU, hT, hU, M, hM, hBM, hnB, hnM, _,
        hCi, hDi, hTi, hUi, _, _, _, hrest⟩ := h
      obtain ⟨hfixed, _, _, _, hc⟩ := hrest
      have hD4 : (weight D : ℚ) = 4 := by
        have hd4 : weight D = 4 := hD.trans hβ
        simp only [hd4, Nat.cast_ofNat]
      have hf := familyE_fixed_det_factor G (fun v => (weight v : ℚ)) C B M D T U
        (by simp only [hC, Nat.cast_ofNat]) (by simp only [hB, Nat.cast_ofNat]) hM hD4
        (by simp only [hT, Nat.cast_ofNat]) (by simp only [hU, Nat.cast_ofNat])
        hTB hUB hTU hBM hnB hnM hCi hDi hTi hUi
      refine ⟨{C, B, M, D, T, U},
        ⟨T, U, M, hT, hU, hM, hBM, hnB, hnM, hCi, hDi, hTi, hUi, rfl, hfixed, hc⟩, ?_⟩
      norm_num only [TenForestRow.exceptionalDet] at ha
      norm_num only [TenForestRow.remainingDet]
      linarith only [hf, ha]

/-- The original candidate-forest hypotheses select one unique actual row
and its scalar, exceptional, full-lattice and remaining-forest invariants.
The determinant in the ratio is that of the actual induced complement
specified by the retained graph witnesses. -/
theorem tenForestInvariantClassification
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5) (hcard : Fintype.card V = β + 7)
    (hG : G.IsAcyclic)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hextraCard : (candidateExtraVertices weight C B D).card ≤ 2)
    (hnadjCB : ¬ G.Adj C B) (hnadjCD : ¬ G.Adj C D) (hnadjBD : ¬ G.Adj B D)
    (hseparate : ¬ G.Reachable B D)
    (hdegreeC : G.degree C ≤ 1) (hdegree : ∀ v, G.degree v ≤ 3)
    (hedges : G.edgeFinset.card ≤ β - 1)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2))
    (hcoeffBounds : ∀ v, 0 ≤ coeff v ∧ coeff v < 1)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff)
    (hbudget : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃! row : TenForestRow, row.Realized G weight coeff C B D β ∧
      β = row.beta ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = row.length ∧
      2 - (β : ℚ) + dotProduct (fun i => (weight i : ℚ) - 2) coeff = row.volume ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
          threeMarkedSource C B D) = row.green ∧
      (graphWeightMatrix G (fun i => (weight i : ℚ))).det = row.exceptionalDet ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
        (threeMarkedSource C B D) (-1)).det = row.borderedDet ∧
      (∃ fixed : Finset V, TenForestRemainingVertices row G weight coeff C B D fixed ∧
        (let A := graphWeightMatrix G (fun i => (weight i : ℚ))
         let AZ := graphWeightMatrix (G.induce {v | v ∉ fixed})
           (fun v => (weight v.val : ℚ))
         let p := threeMarkedSource C B D
         let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
         AZ.det = row.remainingDet ∧ 0 < AZ.det ∧
           delta = row.deltaFactor * AZ.det ∧ delta / AZ.det = row.deltaFactor ∧
           |(borderedGram A p (-1)).det| = delta)) := by
  classical
  have hclassified := ten_forest_classification G weight coeff C B D β hβ hcard hG
    hC hB hD hother hextraCard hnadjCB hnadjCD hnadjBD hseparate hdegreeC hdegree
    hedges hboundary hA hsolve hcoeffBounds hvolume hbudget hprojection
  obtain ⟨row, hreal, hunique⟩ :=
    TenForestRows.existsUnique_realized G weight coeff C B D β hclassified
  have hBD : B ≠ D := by intro h; subst D; exact hseparate (.refl B)
  obtain ⟨fixed, hfixed, hremaining⟩ :=
    tenForestRealized_remaining_matrix row G weight coeff C B D β hC hB hD hBD hreal
  obtain ⟨hbeta, hell, hvol, hg, ha, hb⟩ := hreal.values
  let A := graphWeightMatrix G (fun i => (weight i : ℚ))
  let AZ := graphWeightMatrix (G.induce {v | v ∉ fixed}) (fun v => (weight v.val : ℚ))
  let p : V → ℚ := threeMarkedSource C B D
  let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
  have hpositive : 0 < AZ.det := by
    rw [hremaining]
    cases row <;> norm_num [TenForestRow.remainingDet]
  have hdelta : delta = row.deltaFactor * AZ.det := by
    change A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1) = row.deltaFactor * AZ.det
    rw [ha, hg, hremaining]
    cases row <;> norm_num [TenForestRow.exceptionalDet, TenForestRow.green,
      TenForestRow.deltaFactor, TenForestRow.remainingDet]
  have hratio : delta / AZ.det = row.deltaFactor := by
    rw [hdelta]
    exact mul_div_cancel_right₀ _ (ne_of_gt hpositive)
  have habs : |(borderedGram A p (-1)).det| = delta := by
    rw [hb, hdelta, hremaining]
    exact (TenForestRow.table_identities row).2.2.2.2
  refine ⟨row, ⟨hreal, hbeta, hell, hvol, hg, ha, hb,
    fixed, hfixed, hremaining, hpositive, hdelta, hratio, habs⟩, ?_⟩
  intro other hotherRow
  exact hunique other hotherRow.1

end KltDP.Manuscript.S09
