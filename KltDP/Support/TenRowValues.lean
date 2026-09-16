import KltDP.Manuscript.S09.TenCandidateForestsNonvacuity
import KltDP.Lattices.TenForestLatticeReduction
import Mathlib.Algebra.Group.Even

/-!
# Exact candidate-row values and integral-lattice consequences

The finite models and inverse witnesses come from the actual original-hypothesis
forest classification. Absolute determinants are natural numbers: the signed
bordered determinants of the E rows are negative. Integral index and parity
statements require an actual unimodular integral Gram realization. No surface
realization or geometric no-even-node theorem is assumed or proved here.

Reuse: existing graph/matrix/index/node-code theorems; pinned Mathlib's IsSquare,
power monotonicity, factorization and matrix inverse APIs. The neighboring-square
certificates below are elementary specializations, with no new foundation or port.
-/

namespace KltDP.Support

open Matrix SimpleGraph KltDP.LinearAlgebra KltDP.Manuscript.S09 KltDP.Codes
open KltDP.Lattices.SmallADEForestLattice KltDP.Lattices.TenRowPicardExclusions
open scoped BigOperators

/-- Absolute full-lattice determinant, in the manuscript's ten-row order. -/
def tenRowAbsoluteDet : TenForestRow → ℕ
  | .a1 | .b => 768 | .a2 => 576 | .c => 720
  | .d1 | .e2 => 1296 | .d2 | .e4 => 972
  | .e1 => 1728 | .e3 => 864

/-- The index on the three square rows; zero elsewhere is unused. -/
def tenRowIndex : TenForestRow → ℕ
  | .a2 => 24 | .d1 | .e2 => 36 | _ => 0

/-- The two-adic index valuation on the three square rows. -/
def tenRowIndexValuation : TenForestRow → ℕ
  | .a2 => 3 | .d1 | .e2 => 2 | _ => 0

/-- Number of actual isolated canonical nodes selected on the square rows. -/
def tenRowNodeCount : TenForestRow → ℕ
  | .a2 | .d1 => 4 | .e2 => 3 | _ => 0

theorem tenRow_absoluteDet_cast (row : TenForestRow) :
    |row.borderedDet| = (tenRowAbsoluteDet row : ℚ) := by
  cases row <;> norm_num [TenForestRow.borderedDet, tenRowAbsoluteDet]

theorem tenRow_absoluteDet_pos (row : TenForestRow) : 0 < tenRowAbsoluteDet row := by
  cases row <;> norm_num [tenRowAbsoluteDet]

private theorem not_square_between {n a : ℕ}
    (hlo : a ^ 2 < n) (hhi : n < (a + 1) ^ 2) : ¬ IsSquare n := by
  rintro ⟨b, hb⟩
  have he : n = b ^ 2 := by simpa only [pow_two] using hb
  have hab : a < b := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show b ≤ a by omega) 2
    omega
  have hba : b < a + 1 := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) 2
    omega
  omega

/-- All five distinct nonsquare values are strictly between adjacent squares. -/
theorem tenRow_neighboring_square_exclusions :
    ¬ IsSquare (768 : ℕ) ∧ ¬ IsSquare (720 : ℕ) ∧ ¬ IsSquare (972 : ℕ) ∧
      ¬ IsSquare (1728 : ℕ) ∧ ¬ IsSquare (864 : ℕ) := by
  exact ⟨not_square_between (a := 27) (by norm_num) (by norm_num),
    not_square_between (a := 26) (by norm_num) (by norm_num),
    not_square_between (a := 31) (by norm_num) (by norm_num),
    not_square_between (a := 41) (by norm_num) (by norm_num),
    not_square_between (a := 29) (by norm_num) (by norm_num)⟩

/-- Precisely A2, D1 and E2 have square absolute full-lattice determinant. -/
theorem tenRow_square_iff (row : TenForestRow) :
    IsSquare (tenRowAbsoluteDet row) ↔ row = .a2 ∨ row = .d1 ∨ row = .e2 := by
  obtain ⟨h768, h720, h972, h1728, h864⟩ := tenRow_neighboring_square_exclusions
  have h576 : IsSquare (576 : ℕ) := ⟨24, by norm_num⟩
  have h1296 : IsSquare (1296 : ℕ) := ⟨36, by norm_num⟩
  cases row <;> simp [tenRowAbsoluteDet, h768, h720, h972, h1728, h864, h576, h1296]

theorem tenRow_factorization24 : (24 : ℕ).factorization 2 = 3 := by
  change (2 ^ 3 * 3 : ℕ).factorization 2 = 3
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ^ 3 ≠ 0) (by decide : (3 : ℕ) ≠ 0),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  simp

theorem tenRow_factorization36 : (36 : ℕ).factorization 2 = 2 := by
  change (2 ^ 2 * 3 ^ 2 : ℕ).factorization 2 = 2
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ^ 2 ≠ 0)
    (by decide : (3 : ℕ) ^ 2 ≠ 0),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  simp

/-- Public square-index and node-count triples, with no index claim for nonsquare rows. -/
theorem tenRow_square_triples (row : TenForestRow) (h : IsSquare (tenRowAbsoluteDet row)) :
    tenRowIndex row ^ 2 = tenRowAbsoluteDet row ∧
      (tenRowIndex row).factorization 2 = tenRowIndexValuation row ∧
      ((row = .a2 ∧ tenRowIndex row = 24 ∧ tenRowIndexValuation row = 3 ∧
          tenRowNodeCount row = 4) ∨
        (row = .d1 ∧ tenRowIndex row = 36 ∧ tenRowIndexValuation row = 2 ∧
          tenRowNodeCount row = 4) ∨
        (row = .e2 ∧ tenRowIndex row = 36 ∧ tenRowIndexValuation row = 2 ∧
          tenRowNodeCount row = 3)) := by
  rcases (tenRow_square_iff row).mp h with rfl | rfl | rfl <;>
    norm_num [tenRowIndex, tenRowAbsoluteDet, tenRowIndexValuation, tenRowNodeCount,
      tenRow_factorization24, tenRow_factorization36]

/-- Matrix and inverse-source data on the actual row model, not just table functions. -/
def TenRowModelCertificate (row : TenForestRow) : Prop :=
  let A := row.modelMatrix
  let q := row.modelCanonicalSource
  let p := row.modelMarkedSource
  A.det = row.exceptionalDet ∧
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 ∧
    A *ᵥ (A⁻¹ *ᵥ q) = q ∧ A *ᵥ (A⁻¹ *ᵥ p) = p ∧
    1 - dotProduct p (A⁻¹ *ᵥ q) = row.length ∧
    2 - (row.beta : ℚ) + dotProduct q (A⁻¹ *ᵥ q) = row.volume ∧
    dotProduct p (A⁻¹ *ᵥ p) = row.green ∧
    (borderedGram A p (-1)).det = row.borderedDet ∧
    |(borderedGram A p (-1)).det| = (tenRowAbsoluteDet row : ℚ)

/-- Every explicit model has its exact matrix inverse and scalar values.
The proof uses an actual original-hypothesis witness and the same marked
isomorphism supplied by the classifier. -/
theorem tenRow_model_certificate (row : TenForestRow) : TenRowModelCertificate row := by
  classical
  obtain ⟨G, adj, weight, coeff, C, B, D, _, hdata⟩ :=
    tenCandidateForests_all_rows_nonvacuous row
  letI : DecidableRel G.Adj := adj
  obtain ⟨_, _, hell, hvol, hg, hd, _,
    ⟨f, _, _, _, hw, _, _, _, hc, hp, hmd, hmg⟩, _⟩ := hdata
  let q : Fin (row.beta + 7) → ℚ := fun v => (weight v : ℚ) - 2
  let p : Fin (row.beta + 7) → ℚ := threeMarkedSource C B D
  have hq : q ∘ f = row.modelCanonicalSource := by
    funext i
    change (weight (f i) : ℚ) - 2 = (row.modelWeight i : ℚ) - 2
    rw [hw]
  have hpc := comp_equiv_dotProduct_comp_equiv p coeff f.toEquiv
  have hqc := comp_equiv_dotProduct_comp_equiv q coeff f.toEquiv
  change dotProduct (p ∘ f) (coeff ∘ f) = dotProduct p coeff at hpc
  change dotProduct (q ∘ f) (coeff ∘ f) = dotProduct q coeff at hqc
  rw [hp, hc] at hpc
  rw [hq, hc] at hqc
  have hdet : row.modelMatrix.det = row.exceptionalDet := hmd.symm.trans hd
  have hgreen : dotProduct row.modelMarkedSource
      (row.modelMatrix⁻¹ *ᵥ row.modelMarkedSource) = row.green := hmg.symm.trans hg
  have hunitDet : IsUnit row.modelMatrix.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hdet]
    cases row <;> norm_num [TenForestRow.exceptionalDet]
  have hleft := Matrix.mul_nonsing_inv row.modelMatrix hunitDet
  have hright := Matrix.nonsing_inv_mul row.modelMatrix hunitDet
  have hcanonical : row.modelMatrix *ᵥ
      (row.modelMatrix⁻¹ *ᵥ row.modelCanonicalSource) = row.modelCanonicalSource := by
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hmarked : row.modelMatrix *ᵥ
      (row.modelMatrix⁻¹ *ᵥ row.modelMarkedSource) = row.modelMarkedSource := by
    rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hborder : (borderedGram row.modelMatrix row.modelMarkedSource (-1)).det =
      row.borderedDet := by
    rw [det_minusOne_borderedGram ((Matrix.isUnit_iff_isUnit_det row.modelMatrix).mpr hunitDet),
      TenForestRow.model_card, hdet, hgreen]
    exact (TenForestRow.table_identities row).2.2.2.1.symm
  refine ⟨hdet, hleft, hright, hcanonical, hmarked, ?_, ?_, hgreen, hborder, ?_⟩
  · rw [hpc]
    exact hell
  · rw [hqc]
    exact hvol
  · rw [hborder]
    exact tenRow_absoluteDet_cast row

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A selected node set consists of actual ambient isolated canonical vertices
avoiding all three actual marks. It is a conclusion predicate. -/
def TenRowNodeSelection (row : TenForestRow) (G : SimpleGraph V)
    (weight : V → ℕ) (C B D : V) (S : Finset V) : Prop :=
  S.card = tenRowNodeCount row ∧
    ∀ x ∈ S, weight x = 2 ∧ (∀ y, ¬ G.Adj x y) ∧ x ≠ C ∧ x ≠ B ∧ x ≠ D

private theorem complement_node_selection (row : TenForestRow) (G : SimpleGraph V)
    (weight : V → ℕ) (C B D : V) (fixed : Finset V)
    (hC : C ∈ fixed) (hB : B ∈ fixed) (hD : D ∈ fixed)
    (hcard : (Finset.univ \ fixed).card = tenRowNodeCount row)
    (hrest : ∀ x ∈ Finset.univ \ fixed, weight x = 2 ∧ ∀ y, ¬ G.Adj x y) :
    TenRowNodeSelection row G weight C B D (Finset.univ \ fixed) := by
  refine ⟨hcard, ?_⟩
  intro x hx
  have hout := (Finset.mem_sdiff.mp hx).2
  exact ⟨(hrest x hx).1, (hrest x hx).2,
    fun he => hout (he.symm ▸ hC), fun he => hout (he.symm ▸ hB),
    fun he => hout (he.symm ▸ hD)⟩

/-- Each square row supplies its actual four, four, or three isolated nodes.
No integral-lattice realization is required to select the graph vertices. -/
theorem tenRow_actual_node_selection
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hrow : row.Realized G weight coeff C B D β)
    (hsquare : IsSquare (tenRowAbsoluteDet row)) :
    ∃ S : Finset V, TenRowNodeSelection row G weight C B D S := by
  classical
  rcases (tenRow_square_iff row).mp hsquare with rfl | rfl | rfl
  · obtain ⟨T, _, _, _, _, _, x, y, _, _, _, _, _, _, hc, hr, _⟩ := hrow.2
    exact ⟨_, complement_node_selection .a2 G weight C B D
      {x, y, C, T, B, D} (by simp) (by simp) (by simp) hc hr⟩
  · obtain ⟨T, U, _, _, _, _, _, _, _, M, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, hc, hr, _⟩ := hrow.2
    exact ⟨_, complement_node_selection .d1 G weight C B D
      {C, M, B, D, T, U} (by simp) (by simp) (by simp) hc hr⟩
  · obtain ⟨T, U, _, _, _, _, _, _, _, M, _, _, hnB, hnM,
      _, hCiso, hDiso, hTiso, hUiso, _, _, _, _, _, hZweight, _,
      x, y, _, _, hc, hi, _, _⟩ := hrow.2
    let fixed : Finset V := {C, B, M, D, T, U}
    let rest : Finset {v | v ∉ fixed} := Finset.univ \ {x, y}
    let inclusion : {v | v ∉ fixed} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨rest.map inclusion, ?_, ?_⟩
    · change (rest.map inclusion).card = 3
      rw [Finset.card_map]
      exact hc
    · intro v hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
      have hzout : z.val ∉ fixed := z.property
      have hzweight : weight z.val = 2 := by exact_mod_cast hZweight z
      have hziso : ∀ w, ¬ G.Adj z.val w := by
        intro w hadj
        by_cases hw : w ∈ fixed
        · simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with hw | hw | hw | hw | hw | hw
          · subst w
            exact hCiso _ hadj.symm
          · subst w
            have hm := (G.mem_neighborFinset B z.val).mpr hadj.symm
            rw [hnB, Finset.mem_singleton] at hm
            exact hzout (by simp [fixed, hm])
          · subst w
            have hm := (G.mem_neighborFinset M z.val).mpr hadj.symm
            rw [hnM, Finset.mem_singleton] at hm
            exact hzout (by simp [fixed, hm])
          · subst w
            exact hDiso _ hadj.symm
          · subst w
            exact hTiso _ hadj.symm
          · subst w
            exact hUiso _ hadj.symm
        · exact hi z (Finset.mem_sdiff.mp hz).2 ⟨w, hw⟩ hadj
      have havoid : z.val ≠ C ∧ z.val ≠ B ∧ z.val ≠ D := by
        exact ⟨fun he => hzout (by simp [fixed, he]),
          fun he => hzout (by simp [fixed, he]),
          fun he => hzout (by simp [fixed, he])⟩
      exact ⟨hzweight, hziso, havoid⟩

variable {Λ : Type*} [AddCommGroup Λ]

/-- The actual integer family, not a supplied numerical index. -/
noncomputable def tenRowSpanIndex (pairing : LinearMap.BilinForm ℤ Λ) (classes : V → Λ) (P : Λ) : ℕ :=
  (Submodule.span ℤ (Set.range (Sum.elim classes (fun _ : Unit => P)))).toAddSubgroup.index

/-- An actual unimodular integral Gram realization computes its span index
and leaves exactly the square rows. No characteristic hypothesis is needed. -/
theorem tenRow_actual_index
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hrow : row.Realized G weight coeff C B D β)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P : Λ)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram
        (graphWeightMatrix G (fun v => (weight v : ℚ))) (threeMarkedSource C B D) (-1)) :
    LinearIndependent ℤ (Sum.elim classes (fun _ : Unit => P)) ∧
      tenRowSpanIndex pairing classes P ^ 2 = tenRowAbsoluteDet row ∧
      IsSquare (tenRowAbsoluteDet row) ∧
      tenRowSpanIndex pairing classes P = tenRowIndex row ∧
      (tenRowSpanIndex pairing classes P).factorization 2 = tenRowIndexValuation row := by
  obtain ⟨_, _, _, _, _, hborder⟩ := hrow.values
  have hd : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).det.natAbs =
      tenRowAbsoluteDet row := by
    apply natAbs_det_of_rational_matrix hGram
    rw [hborder]
    exact tenRow_absoluteDet_cast row
  obtain ⟨hind, hs⟩ := span_index_sq_of_gram_det b pairing hunimod
    (Sum.elim classes (fun _ : Unit => P)) (ne_of_gt (tenRow_absoluteDet_pos row)) hd
  have hsq : IsSquare (tenRowAbsoluteDet row) :=
    (isSquare_iff_exists_sq _).mpr ⟨tenRowSpanIndex pairing classes P, hs.symm⟩
  obtain ⟨ht, hv, _⟩ := tenRow_square_triples row hsq
  have hindex : tenRowSpanIndex pairing classes P = tenRowIndex row := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    exact hs.trans ht.symm
  exact ⟨hind, hs, hsq, hindex, by rw [hindex]; exact hv⟩


private theorem tenRow_1296_parity_impossible
    {row : TenForestRow} {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hrow : row.Realized G weight coeff C B D β) (hlabel : row = .d1 ∨ row = .e2)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram
        (graphWeightMatrix G (fun v => (weight v : ℚ))) (threeMarkedSource C B D) (-1))
    (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (weight x : ℚ) - 2) : False := by
  have hsq : IsSquare (tenRowAbsoluteDet row) := (tenRow_square_iff row).mpr
    (by
      rcases hlabel with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  obtain ⟨S, hcard, hnodes⟩ := tenRow_actual_node_selection hrow hsq
  have hdet : |(borderedGram (graphWeightMatrix G (fun v => (weight v : ℚ)))
      (threeMarkedSource C B D) (-1)).det| = 1296 := by
    rw [hrow.values.2.2.2.2.2]
    rcases hlabel with rfl | rfl <;> norm_num [TenForestRow.borderedDet]
  have hcard' : S.card = 3 ∨ S.card = 4 := by
    rcases hlabel with rfl | rfl
    · exact Or.inr hcard
    · exact Or.inl hcard
  exact KltDP.Lattices.TenRowNodeSelections.finset_nodes_determinant1296_impossible
    b pairing hunimod classes P G (fun v => (weight v : ℚ)) C B D hGram hdet S hcard'
    (fun x hx => ⟨by
      change (weight x : ℚ) = 2
      exact congrArg (fun n : ℕ => (n : ℚ)) (hnodes x hx).1, (hnodes x hx).2.1⟩)
    (fun x hx => (hnodes x hx).2.2) K hchar hK

/-- D1's four actual isolated nodes contradict integral characteristic parity
in any actual unimodular realization of the original bordered Gram matrix. -/
theorem tenRow_d1_parity_impossible
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hrow : TenForestRow.d1.Realized G weight coeff C B D β)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram
        (graphWeightMatrix G (fun v => (weight v : ℚ))) (threeMarkedSource C B D) (-1))
    (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (weight x : ℚ) - 2) : False :=
  tenRow_1296_parity_impossible hrow (Or.inl rfl) b pairing hunimod classes P K hGram hchar hK

/-- E2's three actual isolated nodes contradict the same integral parity law.
The determinant used here is the absolute value of the signed value -1296. -/
theorem tenRow_e2_parity_impossible
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hrow : TenForestRow.e2.Realized G weight coeff C B D β)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram
        (graphWeightMatrix G (fun v => (weight v : ℚ))) (threeMarkedSource C B D) (-1))
    (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (weight x : ℚ) - 2) : False :=
  tenRow_1296_parity_impossible hrow (Or.inr rfl) b pairing hunimod classes P K hGram hchar hK

/-- A2 forces the half-sum of its four selected actual nodes to be integral,
with square -2 and canonical pairing zero. This does not invoke a geometric
no-even-node theorem. -/
theorem tenRow_a2_integral_half
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {weight : V → ℕ} {coeff : V → ℚ} {C B D : V} {β : ℕ}
    (hrow : TenForestRow.a2.Realized G weight coeff C B D β)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram
        (graphWeightMatrix G (fun v => (weight v : ℚ))) (threeMarkedSource C B D) (-1))
    (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (weight x : ℚ) - 2) :
    ∃ S : Finset V, TenRowNodeSelection .a2 G weight C B D S ∧
      ∃ m : Λ, (2 : ℤ) • m = (∑ x ∈ S, classes x) ∧
        pairing m m = -2 ∧ pairing K m = 0 := by
  have hsq : IsSquare (tenRowAbsoluteDet .a2) := (tenRow_square_iff .a2).mpr (Or.inl rfl)
  obtain ⟨S, hs⟩ := tenRow_actual_node_selection hrow hsq
  have hdet : |(borderedGram (graphWeightMatrix G (fun v => (weight v : ℚ)))
      (threeMarkedSource C B D) (-1)).det| = 576 := by
    rw [hrow.values.2.2.2.2.2]
    norm_num [TenForestRow.borderedDet]
  refine ⟨S, hs, ?_⟩
  exact KltDP.Lattices.TenRowNodeSelections.finset_four_nodes_half
    b pairing hunimod classes P G (fun v => (weight v : ℚ)) C B D hGram hdet S hs.1
    (fun x hx => ⟨by
      change (weight x : ℚ) = 2
      exact congrArg (fun n : ℕ => (n : ℚ)) (hs.2 x hx).1, (hs.2 x hx).2.1⟩)
    (fun x hx => (hs.2 x hx).2.2) K hchar hK

/-- **U-TEN-ROW-VALUES.** The original forest hypotheses and an actual
unimodular integral Gram realization with characteristic adjunction force
exactly A2. The conclusion retains the same marked forest, all of its model
matrix/inverse/scalar data, its actual span index and its four-node half-sum.
The all-ten model and nonsquare certificates are proved above; no integral
realization is required for a nonsquare or parity-excluded row. -/
theorem u_ten_row_values
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hsource : TenForestOriginalHypotheses G weight coeff C B D β)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram
        (graphWeightMatrix G (fun v => (weight v : ℚ))) (threeMarkedSource C B D) (-1))
    (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (weight x : ℚ) - 2) :
    β = 3 ∧ TenCandidateForestData .a2 G weight coeff C B D β ∧
      (∀ row, TenCandidateForestData row G weight coeff C B D β → row = .a2) ∧
      LinearIndependent ℤ (Sum.elim classes (fun _ : Unit => P)) ∧
      tenRowSpanIndex pairing classes P = 24 ∧
      (tenRowSpanIndex pairing classes P).factorization 2 = 3 ∧
      ∃ S : Finset V, TenRowNodeSelection .a2 G weight C B D S ∧
        ∃ m : Λ, (2 : ℤ) • m = (∑ x ∈ S, classes x) ∧
          pairing m m = -2 ∧ pairing K m = 0 := by
  obtain ⟨_, row, hdata, hunique⟩ := tenCandidateForests_of_originalHypotheses hsource
  have hi := tenRow_actual_index hdata.1 b pairing hunimod classes P hGram
  have hrow : row = .a2 := by
    rcases (tenRow_square_iff row).mp hi.2.2.1 with h | h | h
    · exact h
    · subst row
      exact (tenRow_d1_parity_impossible hdata.1 b pairing hunimod classes P K
        hGram hchar hK).elim
    · subst row
      exact (tenRow_e2_parity_impossible hdata.1 b pairing hunimod classes P K
        hGram hchar hK).elim
  subst row
  exact ⟨hdata.2.1, hdata, hunique, hi.1, hi.2.2.2.1, hi.2.2.2.2,
    tenRow_a2_integral_half hdata.1 b pairing hunimod classes P K hGram hchar hK⟩

/-- All ten graph/matrix cases are inhabited under the original forest
hypotheses, independently of the additional integral-lattice premises. -/
theorem u_ten_row_values_graph_nonvacuity (row : TenForestRow) :
    TenRowModelCertificate row ∧
      ∃ (G : SimpleGraph (Fin (row.beta + 7))) (adj : DecidableRel G.Adj)
        (weight : Fin (row.beta + 7) → ℕ) (coeff : Fin (row.beta + 7) → ℚ)
        (C B D : Fin (row.beta + 7)),
        letI : DecidableRel G.Adj := adj
        TenForestOriginalHypotheses G weight coeff C B D row.beta ∧
          TenCandidateForestData row G weight coeff C B D row.beta :=
  ⟨tenRow_model_certificate row, tenCandidateForests_all_rows_nonvacuous row⟩

end KltDP.Support
