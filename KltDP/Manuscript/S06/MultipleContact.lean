import KltDP.Manuscript.S06.SquareOneBound
import KltDP.Manuscript.S03.NefThreshold
import KltDP.Support.SchurStieltjesLoewner
import KltDP.LinearAlgebra.Stieltjes

/-!
# Manuscript Corollary 6.4: the only possible multiple weight-two contact at a shortest curve

Source: `source/manuscript.tex`, lines 1782–1817, label `cor:multiple-contact`.

Let `P` be a shortest exterior `(-1)`-curve (`R.IsShortestExteriorMinusOne P`), `ℓ = L · P`,
and suppose an exceptional weight-two curve `C` has `m = P · C ≥ 2`. Then `m = 2`,
`ℓ = L² = 1`, `L ≡ -K_S`, all exceptional weights are two (all discrepancies vanish), and `P`
meets no other exceptional curve.

Proof (manuscript lines 1800–1817). The nef threshold class `N = L + ℓ K_S` (Lemma 3.3,
`KltDP.Manuscript.S03.thresholdClass_nef`, `thresholdClass_square_nonneg`, both under
`2 < ρ(S)`) is orthogonal to `C` and `P`, whose span contains the positive class
`G = C + mP` (`G² = m² − 2 > 0`); Hodge index forces `N ≡ 0`. Its exceptional degrees
`ℓ (b_i − 2)` vanish, so all weights are two, `λ = 0`, `L ≡ -K_S`, `ℓ = 1`, and `v = L² = K_S²`
is a positive integer. The projection identity `pᵀ A⁻¹ p = 1 + 1/v ≤ 2` (Lemma 2.8) and the
Stieltjes/Schur bounds `A⁻¹ ≥ 0`, `(A⁻¹)_{CC} ≥ 1/A_{CC} = 1/2` give
`m²/2 + Σ_{i ≠ C} p_i² (A⁻¹)_{ii} ≤ 2`, hence `m = 2`, `v = 1` and `p_i = 0` for `i ≠ C`.

`multipleContact_bound` then applies Proposition 6.2 (ii), type (U1), to `A = C + P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S03 KltDP.Manuscript.S05

universe u

namespace KltDP.Manuscript.S06

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

local notation "𝒞" => DisjointNegativeCurvesRank.curveClass R.S R.hreg
local notation "𝔅" => R.S.numericalIntersectionBilinForm R.hreg

set_option maxHeartbeats 1000000 in
/-- **Corollary 6.4 (`cor:multiple-contact`)**: at a shortest exterior `(-1)`-curve `P`, a
multiple contact `m = P · C ≥ 2` with a weight-two exceptional curve `C` forces `m = 2`,
`L · P = L² = 1`, `λ = 0`, all weights two, `P · D_i = 0` for `i ≠ C`, and `L ≡ -K_S`.
The hypothesis `2 < ρ(S)` is that of Lemma 3.3 (a minimal counterexample has `ρ(S) ≥ 9`). -/
theorem multipleContact (p : ℕ) [CharP k p] (hp : 0 < p) (hrho : 2 < R.S.picardRank)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (C : R.Vertices) (hC : R.w C = 2) (hm : 2 ≤ R.contact P C) :
    R.contact P C = 2 ∧ R.Ldeg P = 1 ∧ R.Lsq = 1 ∧ (∀ i, R.lam i = 0) ∧ (∀ i, R.w i = 2) ∧
      (∀ i, i ≠ C → R.contact P i = 0) ∧ R.Lnum = -R.Knum := by
  classical
  have hnef := thresholdClass_nef R hrho P hP
  have hNsq := thresholdClass_square_nonneg R hrho P hP
  have hℓpos : 0 < R.Ldeg P := Ldeg_pos R P hP.1.2
  have hm2 : (2 : ℚ) ≤ (R.contact P C : ℚ) := by exact_mod_cast hm
  have hmm : (4 : ℚ) ≤ (R.contact P C : ℚ) * (R.contact P C : ℚ) := by
    have := mul_le_mul hm2 hm2 (by norm_num) (by linarith)
    linarith
  have hCC : 𝔅 (𝒞 C.val) (𝒞 C.val) = -2 := by rw [pairing_vertex_self, hC]
  have hPC : 𝔅 (𝒞 P) (𝒞 C.val) = (R.contact P C : ℚ) := pairing_contact R P C
  have hCP : 𝔅 (𝒞 C.val) (𝒞 P) = (R.contact P C : ℚ) := by rw [pairing_symm, hPC]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1.1
  set N : R.S.NumericalClassGroup := thresholdClass R (R.Ldeg P) with hNdef
  set G : R.S.NumericalClassGroup := 𝒞 C.val + (R.contact P C : ℚ) • 𝒞 P with hGdef
  -- `G² = m² - 2 > 0`
  have hbig : 0 < 𝔅 G G := by
    rw [hGdef]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hCC, hCP, hPC, hPP]
    linarith
  -- `N ⊥ C`, `N ⊥ P`
  have hNC : R.S.numericalRestrictionDegree C.val N = 0 := by
    rw [hNdef, thresholdClass_degree_exceptional, hC]
    ring
  have hNP : R.S.numericalRestrictionDegree P N = 0 := by
    rw [hNdef, thresholdClass_degree, Kdeg_eq_neg_one_of_isMinusOne R P hP.1.1]
    push_cast
    ring
  have hGN : 𝔅 G N = 0 := by
    rw [hGdef, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      pairing_symm R (𝒞 C.val) N, ← deg_eq_pairing, hNC, pairing_symm R (𝒞 P) N,
      ← deg_eq_pairing, hNP]
    ring
  -- Hodge index: `N ≡ 0`
  have hN0 : N = 0 :=
    NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal R.S R.hreg G N hbig hGN hNsq
  -- all weights two, `λ = 0`, `L ≡ -K_S`
  have hw : ∀ i, R.w i = 2 := by
    intro i
    have h := thresholdClass_degree_exceptional R (R.Ldeg P) i
    rw [← hNdef, hN0, map_zero] at h
    rcases mul_eq_zero.mp h.symm with h0 | h0
    · exact absurd h0 hℓpos.ne'
    · linarith
  have hq : R.q = 0 := by
    funext i
    show R.w i - 2 = 0
    rw [hw i]
    norm_num
  have hlam : R.lam = 0 := by
    rw [← A_inv_mulVec_q R, hq, Matrix.mulVec_zero]
  have hL : R.Lnum = -R.Knum := by
    rw [R.Lnum_eq, hlam]
    simp
  have hKsq : R.Ksq = R.Lsq := by
    show 𝔅 R.Knum R.Knum = 𝔅 R.Lnum R.Lnum
    rw [hL, LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]
  -- `ℓ = 1`
  have hℓ1 : R.Ldeg P = 1 := by
    have h : R.Lnum + R.Ldeg P • R.Knum = 0 := hN0
    rw [hL] at h
    have h2 : (R.Ldeg P - 1) • R.Knum = 0 := by
      rw [sub_smul, one_smul, ← neg_add_eq_sub]
      exact h
    rcases smul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exfalso
      have hpos := R.Lsq_pos
      rw [← hKsq] at hpos
      change 0 < 𝔅 R.Knum R.Knum at hpos
      rw [h3] at hpos
      simp at hpos
  -- `v = L² = K_S²` is a positive integer
  have hv1 : (1 : ℚ) ≤ R.Lsq := by
    have h := R.Ksq_eq_intersectionPairing
    rw [hKsq] at h
    have hpos := R.Lsq_pos
    rw [h] at hpos ⊢
    have hz : (0 : ℤ) < R.S.intersectionPairing R.hreg R.KS R.KS := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ R.S.intersectionPairing R.hreg R.KS R.KS := by omega
    exact_mod_cast hz1
  -- the projection identity `pᵀ A⁻¹ p = 1 + 1/v`
  have hgreen := rankOneProjection_green R p hp P hP.1
  rw [hℓ1] at hgreen
  -- Stieltjes and Schur bounds
  have hinv_nn : ∀ i j, 0 ≤ R.A⁻¹ i j :=
    KltDP.LinearAlgebra.stieltjes_inverse_nonnegative R.A_posDef R.A_offDiag_nonpos
  have hp_nn : ∀ i, 0 ≤ contactVector R P i := contactVector_nonneg R P hP.1.2
  have hAii : ∀ i, 0 < R.A i i := fun i => by
    rw [R.A_diag]
    linarith [R.two_le_w i]
  have hdiag : ∀ i, 1 / R.A i i ≤ R.A⁻¹ i i := fun i =>
    KltDP.Support.F26.inverse_diag_lower_bound R.A_posDef i
  have hdiag_pos : ∀ i, 0 < R.A⁻¹ i i := fun i =>
    lt_of_lt_of_le (one_div_pos.mpr (hAii i)) (hdiag i)
  have hterm : ∀ i, contactVector R P i ^ 2 * R.A⁻¹ i i ≤
      contactVector R P i * (R.A⁻¹ *ᵥ contactVector R P) i := by
    intro i
    have hrow : R.A⁻¹ i i * contactVector R P i ≤ (R.A⁻¹ *ᵥ contactVector R P) i := by
      show R.A⁻¹ i i * contactVector R P i ≤ ∑ j, R.A⁻¹ i j * contactVector R P j
      exact Finset.single_le_sum (fun j _ => mul_nonneg (hinv_nn i j) (hp_nn j))
        (Finset.mem_univ i)
    have := mul_le_mul_of_nonneg_left hrow (hp_nn i)
    calc contactVector R P i ^ 2 * R.A⁻¹ i i
        = contactVector R P i * (R.A⁻¹ i i * contactVector R P i) := by ring
      _ ≤ _ := this
  have hlower : ∑ i, contactVector R P i ^ 2 * R.A⁻¹ i i ≤
      contactVector R P ⬝ᵥ (R.A⁻¹ *ᵥ contactVector R P) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hsplit : contactVector R P C ^ 2 * R.A⁻¹ C C +
      ∑ i ∈ Finset.univ.erase C, contactVector R P i ^ 2 * R.A⁻¹ i i =
      ∑ i, contactVector R P i ^ 2 * R.A⁻¹ i i :=
    Finset.add_sum_erase Finset.univ (fun i => contactVector R P i ^ 2 * R.A⁻¹ i i)
      (Finset.mem_univ C)
  have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase C, contactVector R P i ^ 2 * R.A⁻¹ i i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hinv_nn i i))
  have hACC : R.A C C = 2 := by rw [R.A_diag, hC]
  have hdC : (1 : ℚ) / 2 ≤ R.A⁻¹ C C := by
    have := hdiag C
    rwa [hACC] at this
  have hpC : contactVector R P C = (R.contact P C : ℚ) := rfl
  have h1v : 1 / R.Lsq ≤ 1 := by
    rw [div_le_one R.Lsq_pos]
    exact hv1
  have hmain : contactVector R P C ^ 2 * R.A⁻¹ C C +
      ∑ i ∈ Finset.univ.erase C, contactVector R P i ^ 2 * R.A⁻¹ i i ≤ 1 + 1 / R.Lsq := by
    rw [hsplit]
    calc _ ≤ _ := hlower
      _ = 1 + 1 ^ 2 / R.Lsq := hgreen
      _ = 1 + 1 / R.Lsq := by ring
  rw [hpC] at hmain
  have hmsq : (R.contact P C : ℚ) ^ 2 * (1 / 2) ≤ (R.contact P C : ℚ) ^ 2 * R.A⁻¹ C C :=
    mul_le_mul_of_nonneg_left hdC (sq_nonneg _)
  -- `m = 2`
  have hm_le : (R.contact P C : ℚ) ≤ 2 := by nlinarith [hmain, hrest, h1v, hmsq, hm2]
  have hmeq : (R.contact P C : ℚ) = 2 := le_antisymm hm_le hm2
  have hmZ : R.contact P C = 2 := by exact_mod_cast hmeq
  rw [hmeq] at hmain hmsq
  -- `v = 1`
  have hv_le : R.Lsq ≤ 1 := by
    have : (1 : ℚ) ≤ 1 / R.Lsq := by linarith
    rwa [one_le_div R.Lsq_pos] at this
  have hv : R.Lsq = 1 := le_antisymm hv_le hv1
  -- no other contacts
  have hrest0 : ∑ i ∈ Finset.univ.erase C, contactVector R P i ^ 2 * R.A⁻¹ i i = 0 := by
    rw [hv] at hmain
    linarith
  have hother : ∀ i, i ≠ C → R.contact P i = 0 := by
    intro i hi
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (sq_nonneg _) (hinv_nn i i))).mp hrest0 i
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    have h2 : contactVector R P i ^ 2 = 0 := (mul_eq_zero.mp h).resolve_right (hdiag_pos i).ne'
    have h3 : contactVector R P i = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
    have h4 : (R.contact P i : ℚ) = 0 := h3
    exact_mod_cast h4
  exact ⟨hmZ, hℓ1, hv, fun i => by rw [hlam]; rfl, hw, hother, hL⟩

/-- **Corollary 6.4, the exclusion on a counterexample**: the double contact is a type-(U1)
square-one configuration, so Proposition 6.2 (ii) gives `#Sing(X) ≤ 7`. -/
theorem multipleContact_bound (p : ℕ) [CharP k p] (hp : 2 < p) (hrho : 2 < R.S.picardRank)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (C : R.Vertices) (hC : R.w C = 2) (hm : 2 ≤ R.contact P C) :
    R.X.singularPoints.card ≤ 7 := by
  obtain ⟨hm2, -, -, -, -, hother, -⟩ := multipleContact R p (by omega) hrho P hP C hC hm
  exact squareOneBound_U1 R p hp P hP C hC hm2 hother

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06.multipleContact
#print axioms KltDP.Manuscript.S06.multipleContact_bound
