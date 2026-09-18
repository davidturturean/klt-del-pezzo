import KltDP.Manuscript.S02.Projection
import KltDP.Manuscript.S02.ExteriorNullCurves
import KltDP.Manuscript.S04.DiscrepancyLemmas
import KltDP.LinearAlgebra.Discrepancy

/-!
# Manuscript Lemma 4.2: existence and rigidity of an excess contact

Source: `source/manuscript.tex`, lines 836–837 (definitions) and 868–902
(`lem:excess-contact`).

For the resolution datum `(S, D, L)` and an exterior `(-1)`-curve `P` with contact vector
`p_i = P · D_i` and canonical-degree vector `q_i = b_i - 2`, a contact at `D_i` is *excess* if
`p_i > q_i` (`IsExcessContact`) and *bounded* if `p_i ≤ q_i` (`IsBoundedContact`).

* `exists_excess_contact`: `p` has at least one excess contact (from the projection identities
  `pᵀA⁻¹p > 1`, `pᵀλ < 1` of Lemma 2.8 and positivity of the Stieltjes inverse `A⁻¹`);
* `bounded_contact_simple`: every nonzero bounded contact is simple, `P · D_i = 1`;
* `higher_weight_excess_contact`: a higher-weight component (`b_i ≥ 3`) with an excess contact
  has `b_i = 3` and `P · D_i = 2`;
* `higher_weight_excess_contact_unique`: there is at most one higher-weight excess contact.

The proofs follow the manuscript: the elementary discrepancy bound `λ_i ≥ (b_i-2)/b_i`
(Lemma 4.1, `elementaryDiscrepancyBound`) and the strict budget `Σ p_i λ_i = pᵀλ < 1`
(`rankOneProjection_charge_lt_one`), all of whose terms are nonnegative.

Only exteriority and the `(-1)`-property of `P` are used (the manuscript's `P` is a shortest
exterior `(-1)`-curve; minimality of `L · P` is not needed here). The characteristic
hypotheses `(p : ℕ) [CharP k p] (hp : 0 < p)` are those of Lemma 2.8's identity `pᵀA⁻¹p > 1`
and appear only in `exists_excess_contact`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S02

universe u

namespace KltDP.Manuscript.S04

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### Excess and bounded contacts (manuscript lines 836–837) -/

/-- A contact of `P` at `D_i` is *excess* when `p_i > q_i` (manuscript line 836). -/
def IsExcessContact (P : R.S.PrimeCurve) (i : R.Vertices) : Prop :=
  R.q i < contactVector R P i

/-- A contact of `P` at `D_i` is *bounded* when `p_i ≤ q_i` (manuscript line 837). -/
def IsBoundedContact (P : R.S.PrimeCurve) (i : R.Vertices) : Prop :=
  contactVector R P i ≤ R.q i

theorem isBoundedContact_iff_not_isExcessContact (P : R.S.PrimeCurve) (i : R.Vertices) :
    IsBoundedContact R P i ↔ ¬ IsExcessContact R P i :=
  not_lt.symm

theorem isExcessContact_or_isBoundedContact (P : R.S.PrimeCurve) (i : R.Vertices) :
    IsExcessContact R P i ∨ IsBoundedContact R P i :=
  lt_or_le _ _

/-- The rational contact vector is the cast of the integer contacts. -/
theorem contactVector_eq (P : R.S.PrimeCurve) (i : R.Vertices) :
    contactVector R P i = (R.contact P i : ℚ) := rfl

/-- Contacts of an exterior prime curve are nonnegative. -/
theorem contactVector_nonneg (P : R.S.PrimeCurve) (hP : ¬ IsExceptionalCurve R.π P)
    (i : R.Vertices) : 0 ≤ contactVector R P i := by
  rw [contactVector_eq]
  exact_mod_cast contact_nonneg_of_not_exceptional R P hP i

/-- The weight `b_i = -D_i²` is an integer. -/
theorem w_eq_intCast (i : R.Vertices) :
    R.w i = ((-(R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg i.val)) : ℤ) : ℚ) := by
  simp only [ResolutionDatum.w, ResolutionDatum.M, NullCurveIntersectionMatrix.intersectionMatrix,
    Int.cast_neg]

/-! ### The discrepancy budget `pᵀλ < 1` termwise -/

/-- Each term `p_i λ_i` is at most the whole budget `pᵀλ` (all terms are nonnegative). -/
theorem contact_mul_lam_le_dot (P : R.S.PrimeCurve) (hP : ¬ IsExceptionalCurve R.π P)
    (i : R.Vertices) :
    contactVector R P i * R.lam i ≤ dotProduct (contactVector R P) R.lam := by
  unfold dotProduct
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (contactVector_nonneg R P hP j) (R.lam_nonneg j)) (Finset.mem_univ i)

/-- `p_i λ_i < 1` for every `i` (manuscript's "contradicting `pᵀλ < 1`"). -/
theorem contact_mul_lam_lt_one (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (i : R.Vertices) : contactVector R P i * R.lam i < 1 :=
  lt_of_le_of_lt (contact_mul_lam_le_dot R P hP.2 i) (rankOneProjection_charge_lt_one R P hP)

/-- Two distinct terms jointly satisfy the strict budget. -/
theorem two_contacts_mul_lam_lt_one (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    {i j : R.Vertices} (hij : i ≠ j) :
    contactVector R P i * R.lam i + contactVector R P j * R.lam j < 1 := by
  refine lt_of_le_of_lt ?_ (rankOneProjection_charge_lt_one R P hP)
  unfold dotProduct
  exact Finset.add_le_sum
    (fun l _ => mul_nonneg (contactVector_nonneg R P hP.2 l) (R.lam_nonneg l))
    (Finset.mem_univ i) (Finset.mem_univ j) hij

/-! ### Manuscript Lemma 4.2 -/

/-- Manuscript Lemma 4.2, first clause (lines 869, 878–884): the contact vector of an exterior
`(-1)`-curve has at least one excess contact. If `p ≤ q` coordinatewise then, since `A⁻¹` is
entrywise nonnegative, `pᵀA⁻¹p ≤ pᵀA⁻¹q = pᵀλ < 1`, contradicting `pᵀA⁻¹p > 1`. -/
theorem exists_excess_contact [DecidableEq R.Vertices] (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P) :
    ∃ i : R.Vertices, IsExcessContact R P i :=
  KltDP.LinearAlgebra.exists_excess_of_stieltjes_budget R.A_posDef R.A_offDiag_nonpos
    (contactVector_nonneg R P hP.2)
    (le_of_lt (rankOneProjection_green_gt_one R p hp P hP))
    (by rw [A_inv_mulVec_q]; exact rankOneProjection_charge_lt_one R P hP)

/-- Manuscript Lemma 4.2, second clause (lines 869, 886–893): every nonzero bounded contact is
simple, `P · D_i = 1`. -/
theorem bounded_contact_simple (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (i : R.Vertices) (hpos : 0 < R.contact P i) (hbdd : IsBoundedContact R P i) :
    R.contact P i = 1 := by
  by_contra hne
  have hp2 : 2 ≤ R.contact P i := by omega
  have hp2' : (2 : ℚ) ≤ contactVector R P i := by
    rw [contactVector_eq]
    exact_mod_cast hp2
  have hq : (2 : ℚ) ≤ R.q i := le_trans hp2' hbdd
  have hw : 3 ≤ R.w i := by
    unfold ResolutionDatum.q at hq
    linarith
  have hlam := elementaryDiscrepancyBound R i hw
  have hhalf : (1 : ℚ) / 2 ≤ R.lam i := by
    refine le_trans ?_ hlam
    rw [le_div_iff₀ (by linarith)]
    unfold ResolutionDatum.q at hq
    linarith
  have hbud := contact_mul_lam_lt_one R P hP i
  nlinarith

/-- A bounded contact is `0` or `1`. -/
theorem contact_eq_zero_or_one_of_bounded (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (i : R.Vertices) (hbdd : IsBoundedContact R P i) :
    R.contact P i = 0 ∨ R.contact P i = 1 := by
  have h0 : 0 ≤ R.contact P i := contact_nonneg_of_not_exceptional R P hP.2 i
  rcases lt_or_eq_of_le h0 with hpos | hzero
  · exact Or.inr (bounded_contact_simple R P hP i hpos hbdd)
  · exact Or.inl hzero.symm

/-- A bounded contact is at most `1`. -/
theorem contact_le_one_of_bounded (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (i : R.Vertices) (hbdd : IsBoundedContact R P i) : R.contact P i ≤ 1 := by
  rcases contact_eq_zero_or_one_of_bounded R P hP i hbdd with h | h <;> omega

/-- A nonzero bounded contact lies on a higher-weight component: `1 ≤ p_i ≤ q_i = b_i - 2`. -/
theorem three_le_w_of_bounded_pos (P : R.S.PrimeCurve) (i : R.Vertices)
    (hpos : 0 < R.contact P i) (hbdd : IsBoundedContact R P i) : 3 ≤ R.w i := by
  have h1 : (1 : ℚ) ≤ contactVector R P i := by
    rw [contactVector_eq]
    exact_mod_cast hpos
  have := le_trans h1 hbdd
  unfold ResolutionDatum.q at this
  linarith

/-- Manuscript Lemma 4.2, third clause (lines 869–873, 895–900): a higher-weight component
`D_i² = -b`, `b ≥ 3`, with an excess contact has `b = 3` and `P · D_i = 2`. -/
theorem higher_weight_excess_contact (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (i : R.Vertices) (hw : 3 ≤ R.w i) (hex : IsExcessContact R P i) :
    R.w i = 3 ∧ R.contact P i = 2 := by
  -- integer forms of the weight and the contact
  obtain ⟨wZ, hwZ⟩ : ∃ wZ : ℤ, R.w i = (wZ : ℚ) := ⟨_, w_eq_intCast R i⟩
  have hpq : (wZ : ℚ) - 2 < (R.contact P i : ℚ) := by
    have h := hex
    unfold IsExcessContact ResolutionDatum.q at h
    rw [hwZ, contactVector_eq] at h
    exact h
  have hpq' : wZ - 2 < R.contact P i := by exact_mod_cast hpq
  have hw3 : (3 : ℤ) ≤ wZ := by
    rw [hwZ] at hw
    exact_mod_cast hw
  have hlam := elementaryDiscrepancyBound R i hw
  have hbud : (R.contact P i : ℚ) * R.lam i < 1 := contact_mul_lam_lt_one R P hP i
  have hlam0 := R.lam_nonneg i
  -- `b = 3`: otherwise `b ≥ 4`, `λ_i ≥ 1/2`, `p_i ≥ 3` and `p_i λ_i ≥ 3/2`
  have hwZ3 : wZ = 3 := by
    by_contra hne
    have hw4 : (4 : ℤ) ≤ wZ := by omega
    have hw4' : (4 : ℚ) ≤ (wZ : ℚ) := by exact_mod_cast hw4
    have hp3 : (3 : ℚ) ≤ (R.contact P i : ℚ) := by
      exact_mod_cast (show (3 : ℤ) ≤ R.contact P i by omega)
    have hhalf : (1 : ℚ) / 2 ≤ R.lam i := by
      refine le_trans ?_ hlam
      rw [hwZ, le_div_iff₀ (by linarith)]
      linarith
    nlinarith
  have hw3' : R.w i = 3 := by
    rw [hwZ, hwZ3]
    norm_num
  refine ⟨hw3', ?_⟩
  -- `p_i = 2`: `p_i ≥ b - 1 = 2`, and `λ_i ≥ 1/3` excludes `p_i ≥ 3`
  have hthird : (1 : ℚ) / 3 ≤ R.lam i := by
    rw [hw3'] at hlam
    norm_num at hlam
    exact hlam
  have hp2 : 2 ≤ R.contact P i := by omega
  by_contra hne
  have hp3 : (3 : ℚ) ≤ (R.contact P i : ℚ) := by
    exact_mod_cast (show (3 : ℤ) ≤ R.contact P i by omega)
  nlinarith

/-- Manuscript Lemma 4.2, last clause (lines 874, 900–901): there is at most one higher-weight
excess contact (two of them would contribute at least `4/3` to `pᵀλ < 1`). -/
theorem higher_weight_excess_contact_unique (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    {i j : R.Vertices} (hi : 3 ≤ R.w i) (hj : 3 ≤ R.w j)
    (hexi : IsExcessContact R P i) (hexj : IsExcessContact R P j) : i = j := by
  by_contra hij
  obtain ⟨hwi, hpi⟩ := higher_weight_excess_contact R P hP i hi hexi
  obtain ⟨hwj, hpj⟩ := higher_weight_excess_contact R P hP j hj hexj
  have hli : (1 : ℚ) / 3 ≤ R.lam i := by
    have h := elementaryDiscrepancyBound R i hi
    rw [hwi] at h
    norm_num at h
    exact h
  have hlj : (1 : ℚ) / 3 ≤ R.lam j := by
    have h := elementaryDiscrepancyBound R j hj
    rw [hwj] at h
    norm_num at h
    exact h
  have h := two_contacts_mul_lam_lt_one R P hP hij
  have hpi' : contactVector R P i = 2 := by
    rw [contactVector_eq, hpi]
    norm_num
  have hpj' : contactVector R P j = 2 := by
    rw [contactVector_eq, hpj]
    norm_num
  rw [hpi', hpj'] at h
  linarith

/-- The excess contacts of `P` are exactly its non-bounded contacts; in particular an excess
contact is nonzero. -/
theorem contact_pos_of_excess (P : R.S.PrimeCurve) (i : R.Vertices)
    (hex : IsExcessContact R P i) : 0 < contactVector R P i := by
  have hq : 0 ≤ R.q i := by
    unfold ResolutionDatum.q
    linarith [R.two_le_w i]
  exact lt_of_le_of_lt hq hex

end KltDP.Manuscript.S04

#print axioms KltDP.Manuscript.S04.exists_excess_contact
#print axioms KltDP.Manuscript.S04.bounded_contact_simple
#print axioms KltDP.Manuscript.S04.higher_weight_excess_contact
#print axioms KltDP.Manuscript.S04.higher_weight_excess_contact_unique
