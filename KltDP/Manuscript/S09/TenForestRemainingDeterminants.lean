import KltDP.Manuscript.S09.TenForests
import KltDP.LinearAlgebra.TenForestFixedBlocks

/-!
# The A, B and D remaining-forest determinant ratios

The actual source equations first give the complete graph rows. The
fixed-component matrices are then computed to have determinants 45 for A
and 243 for D, independently of which allowed remaining edge occurs. For B
the actual remaining graph consists of the five proved isolated vertices.
These facts compute the source ratios 12, 24 and 81 for the actual induced
remaining matrices, completing the ratio values already supplied for C/E.

No candidate determinant, fixed block factor, Green value or numerical
remaining determinant is an input to either source-facing theorem below.
All original hypotheses of the corresponding AB/D source theorems are
retained. This is a matrix-invariant adapter, not a geometric realization
or the complete named classification wrapper.
-/

namespace KltDP.Manuscript.S09

open Matrix SimpleGraph KltDP.LinearAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both A completions have ratio twelve, and B has ratio twenty-four,
relative to the determinant of their actual induced remaining forest.
The extra vertex and its actual connection are source-branch hypotheses;
no candidate row or matrix value is supplied. -/
theorem tenForests_AB_source_remaining_factors
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → ℚ) (C B D T : V) (hcard : Fintype.card V = 10)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B D) (hreach : G.Reachable C T)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : ℚ))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : ℚ)) *ᵥ coeff =
      fun i => (weight i : ℚ) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hbudget : -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff) :
    let w : V → ℚ := fun i => weight i
    let A := graphWeightMatrix G w
    let p := threeMarkedSource C B D
    let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
    (G.Adj C T ∧
      (let AZ := graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
         (fun v => w v.val)
       (AZ.det = 64 ∨ AZ.det = 48) ∧ A.det = 45 * AZ.det ∧
         delta = 12 * AZ.det ∧ delta / AZ.det = 12 ∧
         |(borderedGram A p (-1)).det| = delta)) ∨
    (∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
      (let AZ := graphWeightMatrix (G.induce {v | v ∉ ({C, M, T, B, D} : Finset V)})
         (fun v => w v.val)
       AZ.det = 32 ∧ delta = 24 * AZ.det ∧ delta / AZ.det = 24 ∧
         |(borderedGram A p (-1)).det| = delta)) := by
  classical
  let w : V → ℚ := fun i => weight i
  let A := graphWeightMatrix G w
  let p : V → ℚ := threeMarkedSource C B D
  have hBD : B ≠ D := by intro h; subst D; exact hseparate (.refl B)
  have hell : 0 < 1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hlength
    linarith only [hlength]
  have hv : -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hbudget
    linarith only [hbudget]
  have hfixed (hCT : G.Adj C T) : A.det = 45 *
      (graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
        (fun v => w v.val)).det := by
    obtain ⟨hnC, hnT, hBiso, hDiso, _, _, _, _⟩ :=
      beta_three_adjacent_extra_structure G weight coeff C B D T hweight hC hB hD hT
        hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv
    exact familyA_fixed_det_factor G weight C T B D hC hT hB hD hBD
      hCT hnC hnT hBiso hDiso
  obtain ⟨_, _, hrows⟩ := beta_three_reachable_extra_source_rows G weight coeff C B D T
    hcard hweight hC hB hD hT hTB hTD hother hseparate hreach hedges hA hrow
    hcoeff hlength hbudget
  rcases hrows with ⟨he, _, _, _, _, hg, ha, hb⟩ |
    ⟨u, v, _, _, _, _, _, he, _, _, _, _, hg, ha, hb⟩ |
    ⟨M, hM, hCM, hMT, _, hc, hr, _, _, hg, ha, hb⟩
  · have hCT : G.Adj C T := by
      have hmem : s(C, T) ∈ G.edgeFinset := by rw [he]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmem
    let AZ := graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
      (fun v => w v.val)
    have hf : A.det = 45 * AZ.det := hfixed hCT
    have hz : AZ.det = 64 := by change A.det = 2880 at ha; linarith only [hf, ha]
    refine Or.inl ⟨hCT, Or.inl hz, hf, ?_, ?_, ?_⟩
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hb]; norm_num
  · have hCT : G.Adj C T := by
      have hmem : s(C, T) ∈ G.edgeFinset := by rw [he]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hmem
    let AZ := graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
      (fun v => w v.val)
    have hf : A.det = 45 * AZ.det := hfixed hCT
    have hz : AZ.det = 48 := by change A.det = 2160 at ha; linarith only [hf, ha]
    refine Or.inl ⟨hCT, Or.inr hz, hf, ?_, ?_, ?_⟩
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hb]; norm_num
  · let fixed : Finset V := {C, M, T, B, D}
    let S : Finset V := Finset.univ \ fixed
    let AZ := graphWeightMatrix (G.induce {v | v ∉ fixed}) (fun v => w v.val)
    have hr' : ∀ v : {v | v ∉ fixed}, w v.val = 2 ∧ ∀ u, ¬ G.Adj v.val u := by
      intro v
      obtain ⟨hw, hi⟩ := hr v.val (by simpa [fixed] using v.property)
      exact ⟨by simp only [w, hw, Nat.cast_ofNat], hi⟩
    have hz : AZ.det = 32 := by
      have hweights : (fun v : {v | v ∉ fixed} => w v.val) =
          fun _ => (2 : ℚ) := funext (fun v => (hr' v).1)
      have hgraph : G.induce {v | v ∉ fixed} = ⊥ := by
        ext v u
        change G.Adj v.val u.val ↔ False
        exact iff_false_intro ((hr' v).2 u.val)
      have hedges' : (G.induce {v | v ∉ fixed}).edgeFinset = ∅ :=
        (SimpleGraph.edgeFinset_inj.mpr hgraph).trans SimpleGraph.edgeFinset_bot
      have hcount : Fintype.card {v | v ∉ fixed} = 5 := by
        let e : {v | v ∉ fixed} ≃ (S : Set V) :=
          Equiv.subtypeEquivRight (fun v => by simp [S])
        exact (Fintype.card_congr e).trans ((Fintype.card_coe S).trans hc)
      change (graphWeightMatrix (G.induce {v | v ∉ fixed}) (fun v => w v.val)).det = 32
      rw [hweights]
      have hd := canonical_empty_det (G.induce {v | v ∉ fixed}) hedges'
      rw [hcount] at hd
      exact hd.trans (by norm_num)
    refine Or.inr ⟨M, hM, hCM, hMT, hz, ?_, ?_, ?_⟩
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hb]; norm_num

/-- Both D source completions have ratio eighty-one relative to the
determinant of their actual induced remaining forest. The closed edge,
heavy isolation, Green value and two determinant cases are derived inside. -/
theorem tenForests_familyD_source_remaining_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D T U : V) (hcard : Fintype.card V = 10)
    (hG : G.IsAcyclic) (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : ℚ))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : ℚ)) *ᵥ coeff =
      fun i => (weight i : ℚ) - 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hBD : ¬ G.Reachable B D)
    (hcanonical : ∀ i, G.Reachable C i → weight i = 2)
    (hBsingle : ∀ i, G.Reachable B i → i ≠ B → weight i = 2)
    (hDsingle : ∀ i, G.Reachable D i → i ≠ D → weight i = 2)
    (hTsingle : ∀ i, G.Reachable T i → i ≠ T → weight i = 2)
    (hUsingle : ∀ i, G.Reachable U i → i ≠ U → weight i = 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2)
    (hbudget : -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃ M, G.Adj C M ∧ G.neighborFinset C = {M} ∧ G.neighborFinset M = {C} ∧
      (let AZ := graphWeightMatrix (G.induce {v | v ∉ ({C, M, B, D, T, U} : Finset V)})
         (fun v => (weight v.val : ℚ))
       let A := graphWeightMatrix G (fun i => (weight i : ℚ))
       let p := threeMarkedSource C B D
       let delta := A.det * (dotProduct p (A⁻¹ *ᵥ p) - 1)
       (AZ.det = 16 ∨ AZ.det = 12) ∧ A.det = 243 * AZ.det ∧
         delta = 81 * AZ.det ∧ delta / AZ.det = 81 ∧
         |(borderedGram A p (-1)).det| = delta) := by
  classical
  obtain ⟨M, hCM, hC, hM, hnC, hnM, _, hBiso, hDiso, hTiso, hUiso,
      _, _, hg, hrows⟩ := familyD_source_rows G weight coeff C B D T U hcard hG hedges
    hA hrow hB hD hT hU hTB hTD hUB hUD hTU hCB hCD hBD hcanonical hBsingle hDsingle
    hTsingle hUsingle hother hbudget hprojection
  let A := graphWeightMatrix G (fun i => (weight i : ℚ))
  let AZ := graphWeightMatrix (G.induce {v | v ∉ ({C, M, B, D, T, U} : Finset V)})
    (fun v => (weight v.val : ℚ))
  have hneBD : B ≠ D := by intro h; subst D; exact hBD (.refl B)
  have hf : A.det = 243 * AZ.det := familyD_fixed_det_factor G weight C M B D T U
    hC hM hB hD hT hU hneBD hTB hTD hUB hUD hTU hCM hnC hnM
    hBiso hDiso hTiso hUiso
  rcases hrows with ⟨_, _, _, ha, hb⟩ | ⟨x, y, _, _, _, _, _, _, _, _, ha, hb⟩
  · have hz : AZ.det = 16 := by change A.det = 3888 at ha; linarith only [hf, ha]
    refine ⟨M, hCM, hnC, hnM, Or.inl hz, hf, ?_, ?_, ?_⟩
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hb]; norm_num
  · have hz : AZ.det = 12 := by change A.det = 2916 at ha; linarith only [hf, ha]
    refine ⟨M, hCM, hnC, hnM, Or.inr hz, hf, ?_, ?_, ?_⟩
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hz]; norm_num
    · rw [ha, hg, hb]; norm_num

end KltDP.Manuscript.S09
