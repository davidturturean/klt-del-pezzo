import KltDP.LinearAlgebra.TenForestClassification

/-!
# Remaining determinant clauses for manuscript Lemma 9.2

This module supplies additional actual-matrix clauses toward the named
ten-forest result. It is not yet a declaration of the complete named
lemma. The exact source classifier remains in TenForestClassification;
marked weighted isomorphisms and the other remaining-factor rows are
recorded separately in the source review.

The family-E theorem retains its actual source equations. It derives the
actual remaining graph Z, computes its determinant, and proves the source
ratio Delta/det Z = 54. The negative sign of the full bordered determinant
is retained before taking its absolute value (there are eleven vertices).
No candidate determinant or block decomposition is supplied as a premise.
-/

namespace KltDP.Manuscript.S09

open Matrix SimpleGraph KltDP.LinearAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual finset of isolated weight-two vertices has the determinant
of its actual induced matrix, with the exponent computed from the finset. -/
theorem tenForests_isolated_remaining_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (S : Finset V)
    (hremaining : ∀ v ∈ S, weight v = 2 ∧ ∀ w, ¬ G.Adj v w) :
    (graphWeightMatrix (G.induce (S : Set V)) (fun v => weight v.val)).det =
      2 ^ S.card := by
  classical
  have hweights : (fun v : (S : Set V) => weight v.val) = fun _ => (2 : ℚ) :=
    funext (fun v => (hremaining v.val v.property).1)
  have hgraph : G.induce (S : Set V) = ⊥ := by
    ext v w
    change G.Adj v.val w.val ↔ False
    exact iff_false_intro ((hremaining v.val v.property).2 w.val)
  rw [hweights]
  have hedges : (G.induce (S : Set V)).edgeFinset = ∅ :=
    (SimpleGraph.edgeFinset_inj.mpr hgraph).trans SimpleGraph.edgeFinset_bot
  have hdet := canonical_empty_det (G.induce (S : Set V)) hedges
  have hcardS : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  exact hdet.trans (congrArg (fun n : ℕ => (2 : ℚ) ^ n) hcardS)

/-- The family-C row's actual leftover forest has determinant sixteen,
so its actual Delta is forty-five times that determinant. This is an
adapter for a row produced by the classifier, not an exhaustion premise. -/
theorem tenForests_familyC_remaining_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → ℚ) (C B D T : V)
    (hrows : CForestRow G weight coeff C B D T) :
    ∃ L M, G.Adj B L ∧ G.Adj D M ∧
      (let S : Finset V := Finset.univ \ {C, B, L, D, M, T}
       let AZ := graphWeightMatrix (G.induce (S : Set V)) (fun v => weight v.val)
       let A := graphWeightMatrix G weight
       let p := threeMarkedSource C B D
       let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
       S.card = 4 ∧ AZ.det = 16 ∧ delta = 45 * AZ.det ∧
         delta / AZ.det = 45 ∧ |(borderedGram A p (-1)).det| = delta) := by
  classical
  obtain ⟨L, M, _, _, _, _, hBL, hDM, _, _, _, _, _, hc, hr, _, _, hg, ha, hb⟩ := hrows
  let S : Finset V := Finset.univ \ {C, B, L, D, M, T}
  let AZ := graphWeightMatrix (G.induce (S : Set V)) (fun v => weight v.val)
  have hz : AZ.det = 16 := by
    have h := tenForests_isolated_remaining_det G weight S hr
    rw [hc] at h
    norm_num at h
    exact h
  refine ⟨L, M, hBL, hDM, hc, hz, ?_, ?_, ?_⟩
  · rw [ha, hg, hz]
    norm_num
  · rw [ha, hg, hz]
    norm_num
  · rw [ha, hg, hb]
    norm_num

/-- All four E completions have the stated ratio to the determinant of
their actual induced remaining forest. Both the matrix factor and its
positivity are derived from the source equations and graph classification. -/
theorem tenForests_familyE_remaining_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T U : V)
    (hcard : Fintype.card V = 11)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hedges : G.edgeFinset.card ≤ 3)
    (hB : weight B = 3) (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hUsingle : ∀ v, G.Reachable U v → v ≠ U → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2)
    (hvolume : 0 < -2 + dotProduct (fun i => weight i - 2) coeff)
    (hbudget : -2 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-2 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃ M, weight M = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
      G.neighborFinset M = {B} ∧
      (let fixed : Finset V := {C, B, M, D, T, U}
       let Z := G.induce {v | v ∉ fixed}
       let AZ := graphWeightMatrix Z (fun v => weight v.val)
       let A := graphWeightMatrix G weight
       let p := threeMarkedSource C B D
       let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
       Fintype.card {v | v ∉ fixed} = 5 ∧
         (∀ v : {v | v ∉ fixed}, weight v.val = 2) ∧
         FiveVertexForestShape Z ∧ 0 < AZ.det ∧ A.det = 360 * AZ.det ∧
         delta = 54 * AZ.det ∧ delta / AZ.det = 54 ∧
         (borderedGram A p (-1)).det = -delta ∧
         |(borderedGram A p (-1)).det| = delta) := by
  classical
  obtain ⟨M, hM, hBM, hnB, hnM, _, hCiso, hDiso, hTiso, hUiso, _, _, hg, hr⟩ :=
    familyE_complete_forest G weight coeff C B D T U hcard hA hG hrow hedges
      hB hD hT hU hTB hTD hUB hUD hTU hcanonical hBsingle hDsingle hTsingle
      hUsingle hother hvolume hbudget hprojection
  let fixed : Finset V := {C, B, M, D, T, U}
  let Z := G.induce {v | v ∉ fixed}
  let AZ := graphWeightMatrix Z (fun v => weight v.val)
  let A := graphWeightMatrix G weight
  let p : V → ℚ := threeMarkedSource C B D
  let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
  obtain ⟨_, hZcard, hZweights, _, hshape⟩ := hr
  have hfactor : A.det = 360 * AZ.det :=
    familyE_fixed_det_factor G weight C B M D T U (hcanonical C (.refl C))
      hB hM hD hT hU hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso
  have hweights : (fun v : {v | v ∉ fixed} => weight v.val) = fun _ => (2 : ℚ) :=
    funext hZweights
  have hZpositive : 0 < AZ.det := by
    change 0 < (graphWeightMatrix Z (fun v => weight v.val)).det
    rw [hweights]
    rcases five_vertex_forest_det_cases Z hZcard hshape with h | h | h | h <;>
      rw [h] <;> norm_num
  have hdelta : delta = 54 * AZ.det := by
    change A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1) = 54 * AZ.det
    change dotProduct p (A⁻¹ *ᵥ p) = 23 / 20 at hg
    rw [hfactor, hg]
    ring
  have hratio : delta / AZ.det = 54 := by
    rw [hdelta]
    exact mul_div_cancel_right₀ 54 (ne_of_gt hZpositive)
  have hborder : (borderedGram A p (-1)).det = -delta := by
    have hb := det_minusOne_borderedGram hA p
    rw [hcard] at hb
    norm_num only [show (-1 : ℚ)^11 = -1 by norm_num] at hb
    simpa only [A, delta, neg_one_mul, neg_mul, one_mul] using hb
  have hdeltaNonneg : 0 ≤ delta := by rw [hdelta]; positivity
  have habs : |(borderedGram A p (-1)).det| = delta := by
    rw [hborder, abs_neg, abs_of_nonneg hdeltaNonneg]
  exact ⟨M, hM, hBM, hnB, hnM, hZcard, hZweights, hshape, hZpositive,
    hfactor, hdelta, hratio, hborder, habs⟩

end KltDP.Manuscript.S09
