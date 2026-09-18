import KltDP.Manuscript.S06.CubicAdjoint
import KltDP.Manuscript.S06.ThreeContactSingleComponent

/-!
# Manuscript Theorem 6.7: strict adjoint descent from three weight-two contacts

Source: `source/manuscript.tex`, lines 1936–1980, label `thm:three-contact-descent`.

Let `C₀, C₁, C₂ ⊂ D` be pairwise disjoint exceptional `(-2)`-curves meeting the exterior
`(-1)`-curve `P` once each. Then either `#Sing(X) ≤ 7`, or there is an exterior `(-1)`-curve `Q`
disjoint from `P ∪ C₀ ∪ C₁ ∪ C₂` with `0 < L · Q ≤ L · P - L²/2 (< L · P)`, chosen among the
exterior components of the effective adjoint `E ∼ K_S + C₀ + C₁ + C₂ + 2P` of Proposition 6.5.

Proof (manuscript lines 1949–1980): write `E = Σ a_j Q_j + Z` with `Q_j` exterior and `Z`
supported on `D`, and `M = Σ a_j`. If `M = 0` then `E = 0` and Proposition 6.5 gives the bound.
If `M = 1`, `E = R' + Z` with `Z · R' = 0`, so every component `B` of `Z` has
`Z · B = E · B = K_S · B ≥ 0` and negative definiteness forces `Z = 0`; then
`K_S + C₀ + C₁ + C₂ + 2P ∼ R'` and Proposition 6.6 applies. If `M ≥ 2`,
`min_j L·Q_j ≤ (2 L·P - L²)/M ≤ L·P - L²/2`.

Proposition 6.6 (`prop:three-contact-single-component`, the `M = 1` case) is taken as the
explicit hypothesis `hsingle` (its exact conclusion, for the curve `R'` produced here); the file
`S06.ThreeContactSingleComponent` discharges it.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.DisjointNegativeCurvesRank
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04

universe u

namespace KltDP.Manuscript.S06Adj

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

section Descent

variable (P : R.S.PrimeCurve) (C₀ C₁ C₂ : R.Vertices)

/-- Manuscript lines 1969–1974, the case `M = 1`: if `E` has exactly one exterior component `R'`,
with coefficient one, then `E = R'` (the exceptional part `Z` of `E` satisfies `Z · R' = 0`, so
every component `B` of `Z` has `Z · B = E · B = K_S · B ≥ 0`, and negative definiteness gives
`Z = 0`). -/
theorem cubicRemainder_eq_single_of_unique_exterior {E : R.S.WeilDivisor}
    (hE : CubicRemainder R P C₀ C₁ C₂ E) (R' : R.S.PrimeCurve)
    (hR'ext : ¬ IsExceptionalCurve R.π R') (hER' : E R' = 1)
    (hother : ∀ Q : R.S.PrimeCurve, E Q ≠ 0 → ¬ IsExceptionalCurve R.π Q → Q = R') :
    E = Finsupp.single R' 1 := by
  classical
  set Z' : R.S.WeilDivisor := E - Finsupp.single R' 1 with hZ'def
  have hZ'apply : ∀ Q, Z' Q = E Q - if R' = Q then 1 else 0 := by
    intro Q
    simp only [hZ'def, Finsupp.sub_apply, Finsupp.single_apply]
  have hZ'R' : Z' R' = 0 := by
    rw [hZ'apply]
    simp [hER']
  have hZ'other : ∀ Q, Q ≠ R' → Z' Q = E Q := by
    intro Q hQ
    rw [hZ'apply]
    simp [Ne.symm hQ]
  have hZ'eff : EffectiveDivisor Z' := by
    intro Q
    by_cases hQ : Q = R'
    · rw [hQ, hZ'R']
    · rw [hZ'other Q hQ]
      exact hE.effective Q
  have hZ'ne : ∀ Q, Z' Q ≠ 0 → Q ≠ R' ∧ E Q ≠ 0 := by
    intro Q hQ
    have hQR : Q ≠ R' := fun h => hQ (h ▸ hZ'R')
    exact ⟨hQR, by rwa [hZ'other Q hQR] at hQ⟩
  have hZ'exc : ∀ Q, Z' Q ≠ 0 → IsExceptionalCurve R.π Q := by
    intro Q hQ
    obtain ⟨hQR, hEQ⟩ := hZ'ne Q hQ
    by_contra hext
    exact hQR (hother Q hEQ hext)
  -- `R'` is a `(-1)`-curve and `E · R' = -1`
  have hR'ne : E R' ≠ 0 := by rw [hER']; norm_num
  obtain ⟨hR'minus, hKR'⟩ := hE.exterior_minusOne R' hR'ne hR'ext
  have hER'deg : degW R R' E = -1 := by
    rw [CubicRemainder.degW_component R P C₀ C₁ C₂ hE R' hR'ne, hKR']
    push_cast
    ring
  have hEdecomp : E = Z' + Finsupp.single R' 1 := by
    rw [hZ'def]
    abel
  -- `Z' · R' = 0`
  have hZ'R'deg : degW R R' Z' = 0 := by
    have h := hER'deg
    nth_rewrite 1 [hEdecomp] at h
    rw [degW_add, degW_single, inter_self_minusOne R R' hR'minus] at h
    push_cast at h
    linarith
  -- every component of `Z'` is disjoint from `R'`
  have hBR' : ∀ B, Z' B ≠ 0 → (R'.intersectionNumber (R.S.primeCurveCartier R.hreg B) : ℚ) = 0 := by
    have h := hZ'R'deg
    rw [degW_eq_sum] at h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun B hB => mul_nonneg
      (by exact_mod_cast hZ'eff B)
      (inter_nonneg R R' B (Ne.symm (hZ'ne B (Finsupp.mem_support_iff.mp hB)).1)))).mp h
    intro B hB
    have h1 := hterm B (Finsupp.mem_support_iff.mpr hB)
    have hB' : (Z' B : ℚ) ≠ 0 := by exact_mod_cast hB
    exact (mul_eq_zero.mp h1).resolve_left hB'
  -- `Z' · B = E · B - R' · B = K_S · B ≥ 0` for every component `B` of `Z'`
  have hdeg : ∀ B, Z' B ≠ 0 → 0 ≤ degW R B Z' := by
    intro B hB
    obtain ⟨hBR, hEB⟩ := hZ'ne B hB
    have hexc := hZ'exc B hB
    have h1 : degW R B E = degW R B Z' + (B.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) := by
      nth_rewrite 1 [hEdecomp]
      rw [degW_add, degW_single]
      push_cast
      ring
    have h2 : (B.intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) = 0 := by
      rw [inter_comm]
      exact hBR' B hB
    have h3 := CubicRemainder.degW_component R P C₀ C₁ C₂ hE B hEB
    have hK : (R.Kdeg B : ℚ) = R.w ⟨B, hexc⟩ - 2 := R.Kdeg_exceptional ⟨B, hexc⟩
    have h4 := R.two_le_w ⟨B, hexc⟩
    linarith
  have hsq : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg (numW R Z') (numW R Z') := by
    rw [pairing_numW_eq_sum]
    exact Finset.sum_nonneg (fun B hB => mul_nonneg (by exact_mod_cast hZ'eff B)
      (hdeg B (Finsupp.mem_support_iff.mp hB)))
  have hZ'0 : Z' = 0 := eq_zero_of_exceptional_of_square_nonneg R Z' hZ'exc hsq
  rw [hEdecomp, hZ'0, zero_add]

variable (hP : R.IsExteriorMinusOne P) (h01 : C₀ ≠ C₁) (h02 : C₀ ≠ C₂) (h12 : C₁ ≠ C₂)
  (hn01 : ¬ R.graph.Adj C₀ C₁) (hn02 : ¬ R.graph.Adj C₀ C₂) (hn12 : ¬ R.graph.Adj C₁ C₂)
  (hw0 : R.w C₀ = 2) (hw1 : R.w C₁ = 2) (hw2 : R.w C₂ = 2)
  (hc0 : R.contact P C₀ = 1) (hc1 : R.contact P C₁ = 1) (hc2 : R.contact P C₂ = 1)

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- **Manuscript Theorem 6.7 (`thm:three-contact-descent`, lines 1936–1980)**, with
Proposition 6.6 as the explicit hypothesis `hsingle`: either `#Sing(X) ≤ 7`, or there is an
exterior `(-1)`-curve `Q` disjoint from `P ∪ C₀ ∪ C₁ ∪ C₂` with
`0 < L · Q ≤ L · P - L²/2`. -/
theorem threeContactDescent_of (p : ℕ) [CharP k p] (hp : 0 < p)
    (hsingle : ∀ R' : R.S.PrimeCurve, R.IsExteriorMinusOne R' →
      Disjoint (R' : Set R.S.toScheme) (C₀.val : Set R.S.toScheme) →
      Disjoint (R' : Set R.S.toScheme) (C₁.val : Set R.S.toScheme) →
      Disjoint (R' : Set R.S.toScheme) (C₂.val : Set R.S.toScheme) →
      Disjoint (R' : Set R.S.toScheme) (P : Set R.S.toScheme) →
      R.S.LinearlyEquivalent (Finsupp.single R' 1)
        (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2) →
      R.X.singularPoints.card ≤ 7) :
    R.X.singularPoints.card ≤ 7 ∨
      ∃ Q : R.S.PrimeCurve, R.IsExteriorMinusOne Q ∧
        Disjoint (Q : Set R.S.toScheme) (P : Set R.S.toScheme) ∧
        Disjoint (Q : Set R.S.toScheme) (C₀.val : Set R.S.toScheme) ∧
        Disjoint (Q : Set R.S.toScheme) (C₁.val : Set R.S.toScheme) ∧
        Disjoint (Q : Set R.S.toScheme) (C₂.val : Set R.S.toScheme) ∧
        0 < R.Ldeg Q ∧ R.Ldeg Q ≤ R.Ldeg P - R.Lsq / 2 := by
  classical
  obtain ⟨E, hE⟩ :=
    cubicAdjoint R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 p hp
  -- the exterior components of `E`
  set ext : Finset R.S.PrimeCurve := E.support.filter (fun Q => ¬ IsExceptionalCurve R.π Q)
    with hext
  have hmem : ∀ Q, Q ∈ ext ↔ E Q ≠ 0 ∧ ¬ IsExceptionalCurve R.π Q := by
    intro Q
    simp only [hext, Finset.mem_filter, Finsupp.mem_support_iff]
  have hpos : ∀ Q ∈ ext, 0 < E Q :=
    fun Q hQ => lt_of_le_of_ne (hE.effective Q) (Ne.symm ((hmem Q).mp hQ).1)
  -- `M = Σ a_j`
  set M : ℤ := ∑ Q ∈ ext, E Q with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun Q hQ => (hpos Q hQ).le)
  -- the `L`-degree of `E` is carried by its exterior components
  have hLdeg : ∑ Q ∈ ext, (E Q : ℚ) * R.Ldeg Q = 2 * R.Ldeg P - R.Lsq := by
    rw [← hE.Ldeg_eq, LdegW_eq_sum, hext, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    by_cases hQ : ¬ IsExceptionalCurve R.π Q
    · rw [if_pos hQ]
    · rw [if_neg hQ]
      push_neg at hQ
      rw [R.Ldeg_exceptional ⟨Q, hQ⟩, mul_zero]
  have hempty : ext = ∅ → M = 0 := fun h => by rw [hM, h, Finset.sum_empty]
  rcases (by omega : M = 0 ∨ M = 1 ∨ 2 ≤ M) with hM_zero | hM_one | hM_two
  · -- `M = 0`: `E` has no exterior component, so `E = 0` and Proposition 6.5 applies
    left
    refine singularPoints_le_seven_of_cubicRemainder R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12
      hw0 hw1 hw2 hc0 hc1 hc2 p hp hE (Or.inr ?_)
    intro Q hQ
    by_contra hext'
    have hQmem : Q ∈ ext := (hmem Q).mpr ⟨hQ, hext'⟩
    rw [hM] at hM_zero
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun Q hQ => (hpos Q hQ).le)).mp hM_zero Q hQmem
    exact hQ this
  · -- `M = 1`: a single exterior component `R'` with coefficient one; `E = R'`
    left
    have hne : ext.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have := hempty h
      omega
    have hcard : ext.card = 1 := by
      have h1 : ext.card • (1 : ℤ) ≤ ∑ Q ∈ ext, E Q :=
        Finset.card_nsmul_le_sum ext (fun Q => E Q) 1 (fun Q hQ => by
          have := hpos Q hQ
          show (1 : ℤ) ≤ E Q
          omega)
      have h2 := hne.card_pos
      rw [← hM] at h1
      simp only [nsmul_eq_mul, mul_one] at h1
      omega
    obtain ⟨R', hR'⟩ := Finset.card_eq_one.mp hcard
    have hR'mem : R' ∈ ext := by
      rw [hR']
      exact Finset.mem_singleton_self R'
    obtain ⟨hER'ne, hR'ext⟩ := (hmem R').mp hR'mem
    have hER' : E R' = 1 := by
      rw [← hM_one, hM, hR', Finset.sum_singleton]
    have hother : ∀ Q, E Q ≠ 0 → ¬ IsExceptionalCurve R.π Q → Q = R' := by
      intro Q hQ hQext
      have hQmem : Q ∈ ext := (hmem Q).mpr ⟨hQ, hQext⟩
      rw [hR'] at hQmem
      exact Finset.mem_singleton.mp hQmem
    have hEeq := cubicRemainder_eq_single_of_unique_exterior R P C₀ C₁ C₂ hE R' hR'ext hER' hother
    obtain ⟨hminus, -⟩ := hE.exterior_minusOne R' hER'ne hR'ext
    obtain ⟨d0, d1, d2, dP⟩ := hE.disjoint R' hER'ne
    have hclass := hE.class_eq
    rw [hEeq] at hclass
    exact hsingle R' ⟨hminus, hR'ext⟩ d0 d1 d2 dP hclass
  · -- `M ≥ 2`: an exterior component of least `L`-degree
    right
    have hne : ext.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => by
      have := hempty h
      omega)
    have hMQ : (0 : ℚ) < M := by exact_mod_cast (by omega : (0 : ℤ) < M)
    have hM2Q : (2 : ℚ) ≤ M := by exact_mod_cast hM_two
    have hE0 : 0 ≤ 2 * R.Ldeg P - R.Lsq := by
      rw [← hE.Ldeg_eq]
      exact LdegW_nonneg R E hE.effective
    set t : ℚ := (2 * R.Ldeg P - R.Lsq) / M with ht
    by_cases hexists : ∃ Q ∈ ext, R.Ldeg Q ≤ t
    · obtain ⟨Q, hQmem, hQle⟩ := hexists
      obtain ⟨hEQ, hQext⟩ := (hmem Q).mp hQmem
      obtain ⟨hminus, -⟩ := hE.exterior_minusOne Q hEQ hQext
      obtain ⟨d0, d1, d2, dP⟩ := hE.disjoint Q hEQ
      refine ⟨Q, ⟨hminus, hQext⟩, dP, d0, d1, d2, Ldeg_pos R Q hQext, ?_⟩
      have ht2 : t ≤ (2 * R.Ldeg P - R.Lsq) / 2 := by
        rw [ht]
        exact div_le_div_of_nonneg_left hE0 (by norm_num) hM2Q
      linarith
    · exfalso
      push_neg at hexists
      have hlt : ∑ Q ∈ ext, (E Q : ℚ) * t < ∑ Q ∈ ext, (E Q : ℚ) * R.Ldeg Q := by
        refine Finset.sum_lt_sum_of_nonempty hne (fun Q hQ => ?_)
        have := hpos Q hQ
        exact mul_lt_mul_of_pos_left (hexists Q hQ) (by exact_mod_cast this)
      rw [← Finset.sum_mul, hLdeg] at hlt
      have hsum : (∑ Q ∈ ext, (E Q : ℚ)) = (M : ℚ) := by
        rw [hM, Int.cast_sum]
      rw [hsum, ht, mul_div_cancel₀ _ hMQ.ne'] at hlt
      exact lt_irrefl _ hlt

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 in
/-- **Manuscript Theorem 6.7 (`thm:three-contact-descent`, lines 1936–1980)** (characteristic
`p > 2`), with Proposition 6.6 discharged by `threeContactSingleComponent`: either
`#Sing(X) ≤ 7`, or there is an exterior `(-1)`-curve `Q` disjoint from `P ∪ C₀ ∪ C₁ ∪ C₂` with
`0 < L · Q ≤ L · P - L²/2`. -/
theorem threeContactDescent (p : ℕ) [CharP k p] (hp : 2 < p) :
    R.X.singularPoints.card ≤ 7 ∨
      ∃ Q : R.S.PrimeCurve, R.IsExteriorMinusOne Q ∧
        Disjoint (Q : Set R.S.toScheme) (P : Set R.S.toScheme) ∧
        Disjoint (Q : Set R.S.toScheme) (C₀.val : Set R.S.toScheme) ∧
        Disjoint (Q : Set R.S.toScheme) (C₁.val : Set R.S.toScheme) ∧
        Disjoint (Q : Set R.S.toScheme) (C₂.val : Set R.S.toScheme) ∧
        0 < R.Ldeg Q ∧ R.Ldeg Q ≤ R.Ldeg P - R.Lsq / 2 :=
  threeContactDescent_of R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 p
    (by omega) (fun R' hR' d0 d1 d2 dP hclass =>
      threeContactSingleComponent R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1
        hc2 R' hR' d0 d1 d2 dP hclass p hp)

end Descent

end KltDP.Manuscript.S06Adj

namespace KltDP.Manuscript.S06

/-! Re-exports of the headline results of `KltDP.Manuscript.S06Adj` into the manuscript's §6
namespace (the module lives in the sibling namespace `S06Adj` to avoid clashes with the
square-one modules of the same section). -/

alias threeContactDescent_of := KltDP.Manuscript.S06Adj.threeContactDescent_of
alias threeContactDescent := KltDP.Manuscript.S06Adj.threeContactDescent

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06Adj.threeContactDescent_of
#print axioms KltDP.Manuscript.S06Adj.threeContactDescent
#print axioms KltDP.Manuscript.S06Adj.cubicRemainder_eq_single_of_unique_exterior
