import KltDP.Manuscript.S06.CubicAdjoint
import KltDP.Manuscript.S06.SquareOneBound

/-!
# Manuscript Proposition 6.6: a singular-point bound for a single exterior adjoint component

Source: `source/manuscript.tex`, lines 1880–1934, label `prop:three-contact-single-component`.

Setting (characteristic `p > 2`): `C₀, C₁, C₂ ⊂ D` disjoint exceptional `(-2)`-curves meeting the
exterior `(-1)`-curve `P` once each, and an exterior `(-1)`-curve `R'` disjoint from all four with
`K_S + C₀ + C₁ + C₂ + 2P ∼ R'`. Then `#Sing(X) ≤ 7`.

Proof (manuscript lines 1893–1934). The identity gives `K_S² = 1` and `r = L·R' = 2ℓ - v > 0`
(`ℓ = L·P`, `v = L²`). If `#Sing(X) ≥ 8`, Noether and the Picard rank give exactly eight
exceptional curves, all isolated, so `λ_i = (b_i - 2)/b_i`, `v = 1 + Σ (b_i-2)²/b_i` and
`ℓ = 1 - Σ (b_i - 2)(P·D_i)/b_i ≤ 1`. Then `v < 2ℓ ≤ 2` forces `b_i ∈ {2, 3}`; with `k` weight-three
curves and `u` the contacts of `P` with them, `r = 1 - (k + 2u)/3 > 0` forces `u = 0`, `ℓ = 1`; the
projection identity `½ Σ_{b_i=2} (P·D_i)² = 1 + 1/v` is a half-integer, forcing `k = 0`,
`v = ℓ = r = 1` and `Σ (P·D_i)² = 4`, so there is exactly one further component `W` with `P·W = 1`.
Intersecting the identity with `W` gives `R'·W = 2`, all other contacts of `R'` vanish, all
discrepancies vanish so `R'` is shortest, and `W + R'` is a type-(U1) configuration at `R'`;
Proposition 6.2(ii) bounds `#Sing(X) ≤ 4`, a contradiction.

Proposition 6.2(ii) (`prop:square-one-bound`, Lane 16a's `S06.SquareOneBound`) is taken as the
explicit hypothesis `hU1`: a type-(U1) configuration `W + P'` (weight-two `W`, `P'·W = 2`, no other
contact of `P'`) at a shortest exterior `(-1)`-curve `P'` forces `#Sing(X) ≤ 4`.
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

/-! ### Isolated exceptional curves: discrepancies and the diagonal projection identity -/

/-- The discrepancy of an isolated exceptional curve: `λ_i = (b_i - 2)/b_i`. -/
theorem lam_of_isolated (i : R.Vertices) (hiso : ∀ y, ¬ R.graph.Adj i y) :
    R.lam i = (R.w i - 2) / R.w i := by
  classical
  have h := row_equation R i
  rw [Finset.sum_eq_zero (fun u hu => absurd ((R.graph.mem_neighborFinset i u).1 hu) (hiso u)),
    sub_zero] at h
  have hw : R.w i ≠ 0 := by linarith [R.two_le_w i]
  rw [eq_div_iff hw, mul_comm]
  exact h

/-- `v = K_S² + Σ_i (b_i - 2) λ_i`. -/
theorem Lsq_eq_sum : R.Lsq = R.Ksq + ∑ i : R.Vertices, (R.w i - 2) * R.lam i := by
  rw [R.Lsq_eq_Ksq_add_dot]
  rfl

/-- `L · P = 1 - Σ_i (P·D_i) λ_i` for an exterior `(-1)`-curve `P`. -/
theorem Ldeg_eq_one_sub_sum (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P) :
    R.Ldeg P = 1 - ∑ i : R.Vertices, (R.contact P i : ℚ) * R.lam i := by
  have h := rankOneProjection_charge R P hP
  have hdot : dotProduct (contactVector R P) R.lam =
      ∑ i : R.Vertices, (R.contact P i : ℚ) * R.lam i := rfl
  rw [hdot] at h
  linarith

/-- The projection identity for a totally isolated exceptional configuration:
`Σ_i (P·D_i)² / b_i = 1 + (L·P)² / L²`. -/
theorem green_isolated (p : ℕ) [CharP k p] (hp : 0 < p) (P : R.S.PrimeCurve)
    (hP : R.IsExteriorMinusOne P) (hiso : ∀ i j : R.Vertices, ¬ R.graph.Adj i j) :
    ∑ i : R.Vertices, (R.contact P i : ℚ) ^ 2 / R.w i = 1 + (R.Ldeg P) ^ 2 / R.Lsq := by
  classical
  have hg := rankOneProjection_green R p hp P hP
  -- `A` is diagonal, so `A⁻¹ p = (p_i / b_i)_i`
  set u : R.Vertices → ℚ := fun i => contactVector R P i / R.w i with hu
  have hAu : R.A *ᵥ u = contactVector R P := by
    funext i
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · have hw : R.w i ≠ 0 := by linarith [R.two_le_w i]
      rw [R.A_diag, hu]
      field_simp
    · intro j _ hji
      have hA : R.A i j = -R.M i j := rfl
      rw [hA, M_eq_zero_of_not_adj R (Ne.symm hji) (hiso i j), neg_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hinv : R.A⁻¹ *ᵥ contactVector R P = u := by
    rw [← hAu, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R.A (A_det_isUnit R),
      Matrix.one_mulVec]
  rw [hinv] at hg
  rw [← hg]
  simp only [dotProduct, hu, contactVector]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ## Proposition 6.6 -/

section Single

variable (P : R.S.PrimeCurve) (C₀ C₁ C₂ : R.Vertices)

/-- The degrees of `C₀ + C₁ + C₂ + 2P` on the configuration: `(0, 0, 0, 1)`. -/
theorem cubic_degrees_two (hP : R.IsExteriorMinusOne P) (h01 : C₀ ≠ C₁) (h02 : C₀ ≠ C₂)
    (h12 : C₁ ≠ C₂) (hn01 : ¬ R.graph.Adj C₀ C₁) (hn02 : ¬ R.graph.Adj C₀ C₂)
    (hn12 : ¬ R.graph.Adj C₁ C₂) (hw0 : R.w C₀ = 2) (hw1 : R.w C₁ = 2) (hw2 : R.w C₂ = 2)
    (hc0 : R.contact P C₀ = 1) (hc1 : R.contact P C₁ = 1) (hc2 : R.contact P C₂ = 1) :
    degW R C₀.val (cubDiv R P C₀ C₁ C₂ 1 1 1 2) = 0 ∧
    degW R C₁.val (cubDiv R P C₀ C₁ C₂ 1 1 1 2) = 0 ∧
    degW R C₂.val (cubDiv R P C₀ C₁ C₂ 1 1 1 2) = 0 ∧
    degW R P (cubDiv R P C₀ C₁ C₂ 1 1 1 2) = 1 := by
  have i00 := inter_self R C₀
  have i11 := inter_self R C₁
  have i22 := inter_self R C₂
  have i01 := inter_of_not_adj R h01 hn01
  have i10 := inter_of_not_adj R h01.symm (fun h => hn01 h.symm)
  have i02 := inter_of_not_adj R h02 hn02
  have i20 := inter_of_not_adj R h02.symm (fun h => hn02 h.symm)
  have i12 := inter_of_not_adj R h12 hn12
  have i21 := inter_of_not_adj R h12.symm (fun h => hn12 h.symm)
  have iP0 := inter_contact R P C₀ hc0
  have iP1 := inter_contact R P C₁ hc1
  have iP2 := inter_contact R P C₂ hc2
  have i0P := inter_contact' R P C₀ hc0
  have i1P := inter_contact' R P C₁ hc1
  have i2P := inter_contact' R P C₂ hc2
  have iPP := inter_self_minusOne R P hP.1
  simp only [degW_cubDiv, i00, i11, i22, i01, i10, i02, i20, i12, i21, iP0, iP1, iP2, i0P, i1P, i2P,
    iPP, hw0, hw1, hw2]
  norm_num

/-- A prime curve disjoint from a prime curve `P` is different from `P`. -/
theorem ne_of_disjoint (Q P : R.S.PrimeCurve)
    (h : Disjoint (Q : Set R.S.toScheme) (P : Set R.S.toScheme)) : Q ≠ P := by
  intro hQP
  rw [hQP] at h
  have h1 : (P : Set R.S.toScheme) = ∅ := by
    have h2 := Set.disjoint_iff_inter_eq_empty.mp h
    rwa [Set.inter_self] at h2
  exact (KltDP.Geometry.NormalProjectiveSurface.PrimeCurve.nonempty P).ne_empty h1

/-- The integer sum `Σ_{i ∈ s} n_i = 1` of nonnegative integers has exactly one nonzero term,
equal to one. -/
theorem exists_unique_one_of_sum_eq_one {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hsum : ∑ i ∈ s, f i = 1) :
    ∃ W ∈ s, f W = 1 ∧ ∀ i ∈ s, i ≠ W → f i = 0 := by
  classical
  obtain ⟨W, hW, hWne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; norm_num :
    ∑ i ∈ s, f i ≠ 0)
  have hsplit := Finset.add_sum_erase s f hW
  have hrest_nonneg : 0 ≤ ∑ i ∈ s.erase W, f i :=
    Finset.sum_nonneg (fun i hi => hf i (Finset.mem_of_mem_erase hi))
  have hWpos : 0 < f W := lt_of_le_of_ne (hf W hW) (Ne.symm hWne)
  have hW1 : f W = 1 := by omega
  have hrest : ∑ i ∈ s.erase W, f i = 0 := by omega
  refine ⟨W, hW, hW1, fun i hi hiW => ?_⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hf j (Finset.mem_of_mem_erase hj))).mp hrest
    i (Finset.mem_erase.mpr ⟨hiW, hi⟩)

variable (hP : R.IsExteriorMinusOne P) (h01 : C₀ ≠ C₁) (h02 : C₀ ≠ C₂) (h12 : C₁ ≠ C₂)
  (hn01 : ¬ R.graph.Adj C₀ C₁) (hn02 : ¬ R.graph.Adj C₀ C₂) (hn12 : ¬ R.graph.Adj C₁ C₂)
  (hw0 : R.w C₀ = 2) (hw1 : R.w C₁ = 2) (hw2 : R.w C₂ = 2)
  (hc0 : R.contact P C₀ = 1) (hc1 : R.contact P C₁ = 1) (hc2 : R.contact P C₂ = 1)
  (R' : R.S.PrimeCurve) (hR' : R.IsExteriorMinusOne R')
  (d0 : Disjoint (R' : Set R.S.toScheme) (C₀.val : Set R.S.toScheme))
  (d1 : Disjoint (R' : Set R.S.toScheme) (C₁.val : Set R.S.toScheme))
  (d2 : Disjoint (R' : Set R.S.toScheme) (C₂.val : Set R.S.toScheme))
  (dP : Disjoint (R' : Set R.S.toScheme) (P : Set R.S.toScheme))
  (hclass : R.S.LinearlyEquivalent (Finsupp.single R' 1)
    (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2))

include hR' d0 d1 d2 dP in
/-- `R'` meets none of the four curves. -/
theorem single_inter_zero :
    (R'.intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) = 0 ∧
    (R'.intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) = 0 ∧
    (R'.intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) = 0 ∧
    (R'.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 :=
  ⟨inter_eq_zero_of_disjoint R R' C₀.val (exterior_ne_vertex R R' hR'.2 C₀) d0,
    inter_eq_zero_of_disjoint R R' C₁.val (exterior_ne_vertex R R' hR'.2 C₁) d1,
    inter_eq_zero_of_disjoint R R' C₂.val (exterior_ne_vertex R R' hR'.2 C₂) d2,
    inter_eq_zero_of_disjoint R R' P (ne_of_disjoint R R' P dP) dP⟩

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 hR' d0 d1 d2 dP hclass in
/-- Manuscript line 1894: `K_S² = 1` and `r = L·R' = 2 L·P - L²`. -/
theorem single_numbers : R.Ksq = 1 ∧ R.Ldeg R' = 2 * R.Ldeg P - R.Lsq := by
  obtain ⟨e0, e1, e2, eP⟩ := single_inter_zero R P C₀ C₁ C₂ R' hR' d0 d1 d2 dP
  obtain ⟨g0, g1, g2, gP⟩ :=
    cubic_degrees_two R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
  have hnum := numW_eq_of_linearlyEquivalent R hclass
  rw [numW_single, map_add, numW_KS, Int.cast_one, one_smul] at hnum
  set D := numW R (cubDiv R P C₀ C₁ C₂ 1 1 1 2) with hD
  have hK : R.Knum = curveClass R.S R.hreg R' - D := by rw [hnum]; abel
  have hRR : R.S.numericalIntersectionBilinForm R.hreg (curveClass R.S R.hreg R')
      (curveClass R.S R.hreg R') = -1 := by
    rw [curveClass_self_pairing, hR'.1.selfIntersection]; norm_num
  have hRD : R.S.numericalIntersectionBilinForm R.hreg (curveClass R.S R.hreg R') D = 0 := by
    rw [hD, ← degW_eq_pairing, degW_cubDiv, e0, e1, e2, eP]; norm_num
  have hDR : R.S.numericalIntersectionBilinForm R.hreg D (curveClass R.S R.hreg R') = 0 := by
    rw [LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg), hRD]
  have hDD : R.S.numericalIntersectionBilinForm R.hreg D D = 2 := by
    rw [hD, pairing_cubDiv, g0, g1, g2, gP]; norm_num
  refine ⟨?_, ?_⟩
  · unfold ResolutionDatum.Ksq
    rw [hK, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.sub_right, hRR, hRD, hDR, hDD]
    norm_num
  · have h := LdegW_eq_pairing R (Finsupp.single R' 1)
    rw [LdegW_eq_sum, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, Int.cast_one, one_mul, numW_single, Int.cast_one, one_smul,
      Lnum_pairing_curveClass] at h
    have hR'class : curveClass R.S R.hreg R' = R.Knum + D := by rw [hK]; abel
    rw [← Lnum_pairing_curveClass, hR'class, LinearMap.BilinForm.add_right, hD,
      Lnum_pairing_cubDiv, LinearMap.BilinForm.IsSymm.eq
        (R.S.numericalIntersectionBilinForm_isSymm R.hreg) R.Lnum R.Knum, R.Knum_pairing_Lnum]
    push_cast
    ring

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 hR' d0 d1 d2 dP hclass in
/-- Manuscript lines 1896–1898: eight exceptional curves, and with `#Sing(X) ≥ 8` all of them are
isolated. -/
theorem eight_isolated (p : ℕ) [CharP k p] (hp : 0 < p) (h8 : 8 ≤ R.X.singularPoints.card) :
    Fintype.card R.Vertices = 8 ∧ ∀ i j : R.Vertices, ¬ R.graph.Adj i j := by
  classical
  obtain ⟨hKsq, -⟩ := single_numbers R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1
    hc2 R' hR' d0 d1 d2 dP hclass
  have hN := R.hmin.noetherRelation_of_kltDelPezzo R.hDP R.hrank p hp R.KS R.eKS
  change R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 at hN
  have hKsq' := R.Ksq_eq_intersectionPairing
  rw [hKsq] at hKsq'
  have hKint : R.S.intersectionPairing R.hreg R.KS R.KS = 1 := by exact_mod_cast hKsq'.symm
  have hρ := R.hmin.picardRank_eq_of_klt R.hklt p hp
  rw [R.hrank, Nat.card_eq_fintype_card] at hρ
  have hρ' : (R.S.picardRank : ℤ) = 1 + (Fintype.card R.Vertices : ℤ) := by exact_mod_cast hρ
  have hcardZ : (Fintype.card R.Vertices : ℤ) = 8 := by
    rw [hKint] at hN
    linarith
  have hcard : Fintype.card R.Vertices = 8 := by exact_mod_cast hcardZ
  refine ⟨hcard, ?_⟩
  obtain ⟨hfin, hcount, -, -⟩ := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  letI := hfin
  letI : Fintype (ActualExceptionalIncidence.graph R.π).ConnectedComponent := Fintype.ofFinite _
  rw [hcount, Nat.card_eq_fintype_card] at h8
  have hsurj : Function.Surjective
      (fun v : R.Vertices => (ActualExceptionalIncidence.graph R.π).connectedComponentMk v) :=
    fun c => SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c
  have hle := Fintype.card_le_of_surjective _ hsurj
  have heq : Fintype.card R.Vertices =
      Fintype.card (ActualExceptionalIncidence.graph R.π).ConnectedComponent := by omega
  have hbij := (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, heq⟩
  intro i j hadj
  have hij : i = j := hbij.1 (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj)
  rw [hij] at hadj
  exact R.graph.loopless _ hadj

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 hR' d0 d1 d2 dP hclass in
/-- **Manuscript Proposition 6.6 (`prop:three-contact-single-component`, lines 1880–1934)**, with
Proposition 6.2(ii) as the explicit hypothesis `hU1`. -/
theorem threeContactSingleComponent_of (p : ℕ) [CharP k p] (hp : 2 < p)
    (hU1 : ∀ (P' : R.S.PrimeCurve) (W : R.Vertices), R.IsShortestExteriorMinusOne P' →
      R.w W = 2 → R.contact P' W = 2 → (∀ i : R.Vertices, i ≠ W → R.contact P' i = 0) →
      R.X.singularPoints.card ≤ 7) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  have hp0 : 0 < p := by omega
  by_contra h8
  push_neg at h8
  have h8' : 8 ≤ R.X.singularPoints.card := h8
  obtain ⟨hKsq, hr⟩ := single_numbers R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0
    hc1 hc2 R' hR' d0 d1 d2 dP hclass
  obtain ⟨-, hiso⟩ := eight_isolated R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1
    hc2 R' hR' d0 d1 d2 dP hclass p hp0 h8'
  -- `r = 2ℓ - v > 0`
  have hrpos : 0 < 2 * R.Ldeg P - R.Lsq := by
    rw [← hr]
    exact Ldeg_pos R R' hR'.2
  -- integer weights `a_i = b_i - 2 ≥ 0` and contacts `p_i ≥ 0`
  set a : R.Vertices → ℤ := fun i => -(i.val.selfIntersectionNumber R.hreg) - 2 with ha
  have hw : ∀ i, R.w i = (a i : ℚ) + 2 := by
    intro i
    rw [w_eq_int_cast, ha]
    push_cast
    ring
  have ha0 : ∀ i, 0 ≤ a i := by
    intro i
    have h := R.two_le_w i
    rw [hw] at h
    have : (0 : ℚ) ≤ a i := by linarith
    exact_mod_cast this
  set pc : R.Vertices → ℤ := fun i => R.contact P i with hpc
  have hpc0 : ∀ i, 0 ≤ pc i := fun i => contact_nonneg_of_not_exceptional R P hP.2 i
  have hlam : ∀ i, R.lam i = (a i : ℚ) / ((a i : ℚ) + 2) := by
    intro i
    rw [lam_of_isolated R i (hiso i), hw]
    ring_nf
  -- `v = 1 + Σ (b_i-2) λ_i`, `ℓ = 1 - Σ p_i λ_i`
  have hv := Lsq_eq_sum R
  rw [hKsq] at hv
  have hl := Ldeg_eq_one_sub_sum R P hP
  have hterm_nonneg : ∀ i, 0 ≤ (R.w i - 2) * R.lam i :=
    fun i => mul_nonneg (by linarith [R.two_le_w i]) (R.lam_nonneg i)
  have hlterm_nonneg : ∀ i, 0 ≤ (R.contact P i : ℚ) * R.lam i :=
    fun i => mul_nonneg (by exact_mod_cast hpc0 i) (R.lam_nonneg i)
  have hl1 : R.Ldeg P ≤ 1 := by
    rw [hl]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hlterm_nonneg i)]
  -- `b_i ∈ {2, 3}`
  have ha1 : ∀ i, a i ≤ 1 := by
    intro i
    by_contra hlt
    push_neg at hlt
    have h2 : (2 : ℤ) ≤ a i := hlt
    have h2Q : (2 : ℚ) ≤ a i := by exact_mod_cast h2
    have hsingle : (R.w i - 2) * R.lam i ≤ ∑ j : R.Vertices, (R.w j - 2) * R.lam j :=
      Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
    have hterm : (R.w i - 2) * R.lam i = (a i : ℚ) ^ 2 / ((a i : ℚ) + 2) := by
      rw [hlam, hw]
      ring
    have hge : (1 : ℚ) ≤ (a i : ℚ) ^ 2 / ((a i : ℚ) + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  -- the weight-three count `K` and the contact sum `U`
  have hcase : ∀ i, a i = 0 ∨ a i = 1 := fun i => by have := ha0 i; have := ha1 i; omega
  have hterm_v : ∀ i, (R.w i - 2) * R.lam i = (a i : ℚ) / 3 := by
    intro i
    rw [hlam, hw]
    rcases hcase i with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hterm_l : ∀ i, (R.contact P i : ℚ) * R.lam i = ((pc i * a i : ℤ) : ℚ) / 3 := by
    intro i
    rw [hlam]
    rcases hcase i with h | h
    · rw [h]; simp [hpc]
    · rw [h]; simp [hpc]; ring
  set K : ℤ := ∑ i : R.Vertices, a i with hK
  set U : ℤ := ∑ i : R.Vertices, pc i * a i with hU
  have hvK : R.Lsq = 1 + (K : ℚ) / 3 := by
    rw [hv, Finset.sum_congr rfl (fun i _ => hterm_v i), ← Finset.sum_div, hK]
    push_cast
    ring
  have hlU : R.Ldeg P = 1 - (U : ℚ) / 3 := by
    rw [hl, Finset.sum_congr rfl (fun i _ => hterm_l i), ← Finset.sum_div, hU]
    push_cast
    ring
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun i _ => ha0 i)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun i _ => mul_nonneg (hpc0 i) (ha0 i))
  have hKU : K + 2 * U < 3 := by
    have h := hrpos
    rw [hvK, hlU] at h
    have h' : (K : ℚ) + 2 * U < 3 := by linarith
    exact_mod_cast h'
  -- `U = 0`
  have hUzero : U = 0 := by
    rcases eq_or_ne U 0 with hne | hne
    · exact hne
    exfalso
    have hne' : ∑ i : R.Vertices, pc i * a i ≠ 0 := by rw [← hU]; exact hne
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    have hai : a i ≠ 0 := fun h => hi (by rw [h, mul_zero])
    have hai1 : a i = 1 := by have := hcase i; omega
    have hK1 : a i ≤ K := Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)
    have hU1' : pc i * a i ≤ U := Finset.single_le_sum
      (fun j _ => mul_nonneg (hpc0 j) (ha0 j)) (Finset.mem_univ i)
    have hpi : 1 ≤ pc i := by
      have := hpc0 i
      rw [hai1, mul_one] at hi
      omega
    rw [hai1, mul_one] at hU1'
    omega
  have hpa : ∀ i, pc i * a i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hpc0 j) (ha0 j))).mp
      (by rw [← hU]; exact hUzero) i (Finset.mem_univ i)
  have hl_one : R.Ldeg P = 1 := by
    rw [hlU, hUzero]
    norm_num
  -- the projection identity: `Σ p_i² / 2 = 1 + 1/v`
  have hg := green_isolated R p hp0 P hP hiso
  have hgterm : ∀ i, (R.contact P i : ℚ) ^ 2 / R.w i = ((pc i ^ 2 : ℤ) : ℚ) / 2 := by
    intro i
    rw [hw]
    rcases hcase i with h | h
    · rw [h]; simp [hpc]
    · have hp0' : pc i = 0 := by have := hpa i; rw [h, mul_one] at this; exact this
      have hp0'' : R.contact P i = 0 := hp0'
      rw [h, hp0'', hp0']; simp
  set S : ℤ := ∑ i : R.Vertices, pc i ^ 2 with hS
  have hgS : (S : ℚ) / 2 = 1 + 1 / R.Lsq := by
    rw [hl_one, one_pow] at hg
    rw [← hg, Finset.sum_congr rfl (fun i _ => hgterm i), ← Finset.sum_div, hS]
    push_cast
    ring
  -- `K ∈ {0, 1, 2}` and the half-integrality force `K = 0`, `S = 4`
  have hK3 : K < 3 := by omega
  have hSK : (S : ℚ) * (3 + K) = 12 + 2 * K := by
    rw [hvK] at hgS
    have hK3Q : (0 : ℚ) < 3 + K := by
      have : (0 : ℚ) ≤ K := by exact_mod_cast hK0
      linarith
    have h1 : 1 + (K : ℚ) / 3 = (3 + K) / 3 := by ring
    rw [h1, one_div_div] at hgS
    field_simp at hgS
    linarith
  have hSKZ : S * (3 + K) = 12 + 2 * K := by exact_mod_cast hSK
  have hKzero : K = 0 := by
    rcases (by omega : K = 0 ∨ K = 1 ∨ K = 2) with h | h | h
    · exact h
    · rw [h] at hSKZ; omega
    · rw [h] at hSKZ; omega
  have hS4 : S = 4 := by
    rw [hKzero] at hSKZ
    omega
  -- all weights are two and all discrepancies vanish
  have ha_zero : ∀ i, a i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha0 j)).mp (by rw [← hK]; exact hKzero) i
      (Finset.mem_univ i)
  have hw2' : ∀ i, R.w i = 2 := fun i => by rw [hw, ha_zero]; norm_num
  have hlam0 : ∀ i, R.lam i = 0 := fun i => by rw [hlam, ha_zero]; norm_num
  have hv1 : R.Lsq = 1 := by rw [hvK, hKzero]; norm_num
  -- exactly one further contact `W` with `P · W = 1`
  have hpcC : pc C₀ = 1 ∧ pc C₁ = 1 ∧ pc C₂ = 1 := ⟨hc0, hc1, hc2⟩
  set rest : Finset R.Vertices := ((Finset.univ.erase C₀).erase C₁).erase C₂ with hrest
  have hsplit : ∑ i : R.Vertices, pc i ^ 2 = pc C₀ ^ 2 + pc C₁ ^ 2 + pc C₂ ^ 2 +
      ∑ i ∈ rest, pc i ^ 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ C₀),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ C₁⟩),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h12.symm,
        Finset.mem_erase.mpr ⟨h02.symm, Finset.mem_univ C₂⟩⟩)]
    ring
  have hrest1 : ∑ i ∈ rest, pc i ^ 2 = 1 := by
    have := hS
    rw [hsplit, hpcC.1, hpcC.2.1, hpcC.2.2] at this
    omega
  obtain ⟨W, hWrest, hW1, hWother⟩ := exists_unique_one_of_sum_eq_one rest (fun i => pc i ^ 2)
    (fun i _ => sq_nonneg _) hrest1
  have hWne : W ≠ C₂ ∧ W ≠ C₁ ∧ W ≠ C₀ := by
    rw [hrest] at hWrest
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hWrest
    exact hWrest
  have hpW : pc W = 1 := by
    have h := hpc0 W
    have h1 : pc W ^ 2 = 1 := hW1
    nlinarith
  have hpother : ∀ i : R.Vertices, i ≠ C₀ → i ≠ C₁ → i ≠ C₂ → i ≠ W → pc i = 0 := by
    intro i hi0 hi1 hi2 hiW
    have hmem : i ∈ rest := by
      rw [hrest]
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨hi2, hi1, hi0⟩
    have h := hWother i hmem hiW
    have h' : pc i ^ 2 = 0 := h
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h'
  -- the contacts of `R'`: `R' · W = 2`, all others zero
  have hdegR' : ∀ i : R.Vertices, (R'.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) =
      (R.Kdeg i.val : ℚ) + ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) +
      ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) +
      ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) +
      2 * ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
    intro i
    have h := congrArg (R.S.numericalRestrictionDegree i.val) (numW_eq_of_linearlyEquivalent R hclass)
    have h1 : R.S.numericalRestrictionDegree i.val (numW R (Finsupp.single R' 1)) =
        ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg R') : ℚ) := by
      rw [← degW, degW_single, Int.cast_one, one_mul]
    have h2 : R.S.numericalRestrictionDegree i.val
        (numW R (R.S.cartierToWeilHom R.KS + cubDiv R P C₀ C₁ C₂ 1 1 1 2)) =
        (R.Kdeg i.val : ℚ) + ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg C₀.val) : ℚ) +
        ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg C₁.val) : ℚ) +
        ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg C₂.val) : ℚ) +
        2 * ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
      rw [map_add, numW_KS, map_add, KltDP.Manuscript.S03.numericalRestrictionDegree_Knum]
      have : R.S.numericalRestrictionDegree i.val (numW R (cubDiv R P C₀ C₁ C₂ 1 1 1 2)) =
          degW R i.val (cubDiv R P C₀ C₁ C₂ 1 1 1 2) := rfl
      rw [this, degW_cubDiv]
      push_cast
      ring
    rw [h1, h2] at h
    rw [inter_comm R R' i.val, h]
  have hKdeg0 : ∀ i : R.Vertices, (R.Kdeg i.val : ℚ) = 0 := by
    intro i
    rw [R.Kdeg_exceptional]
    show R.w i - 2 = 0
    rw [hw2']; norm_num
  have hiP : ∀ i : R.Vertices, ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) =
      (pc i : ℚ) := fun i => by rw [inter_comm]; try rfl
  have hcontactW : R.contact R' W = 2 := by
    have h := hdegR' W
    rw [hKdeg0, inter_of_not_adj R hWne.2.2 (hiso W C₀), inter_of_not_adj R hWne.2.1 (hiso W C₁),
      inter_of_not_adj R hWne.1 (hiso W C₂), hiP, hpW] at h
    have h' : (R.contact R' W : ℚ) = 2 := by rw [h]; try norm_num
    exact_mod_cast h'
  have hcontactOther : ∀ i : R.Vertices, i ≠ W → R.contact R' i = 0 := by
    intro i hiW
    have h := hdegR' i
    rw [hKdeg0, hiP] at h
    have h' : (R.contact R' i : ℚ) = 0 := by
      rw [h]
      by_cases hi0 : i = C₀
      · subst hi0
        rw [inter_self, inter_of_not_adj R h01 hn01, inter_of_not_adj R h02 hn02, hw0]
        have : (pc i : ℚ) = 1 := by exact_mod_cast hpcC.1
        rw [this]; try norm_num
      by_cases hi1 : i = C₁
      · subst hi1
        rw [inter_self, inter_of_not_adj R h01.symm (fun h => hn01 h.symm),
          inter_of_not_adj R h12 hn12, hw1]
        have : (pc i : ℚ) = 1 := by exact_mod_cast hpcC.2.1
        rw [this]; try norm_num
      by_cases hi2 : i = C₂
      · subst hi2
        rw [inter_self, inter_of_not_adj R h02.symm (fun h => hn02 h.symm),
          inter_of_not_adj R h12.symm (fun h => hn12 h.symm), hw2]
        have : (pc i : ℚ) = 1 := by exact_mod_cast hpcC.2.2
        rw [this]; try norm_num
      rw [inter_of_not_adj R hi0 (hiso i C₀), inter_of_not_adj R hi1 (hiso i C₁),
        inter_of_not_adj R hi2 (hiso i C₂)]
      have : (pc i : ℚ) = 0 := by exact_mod_cast hpother i hi0 hi1 hi2 hiW
      rw [this]; try norm_num
    exact_mod_cast h'
  -- `R'` is shortest: every exterior `(-1)`-curve has `L`-degree one
  have hLdeg_one : ∀ Q : R.S.PrimeCurve, R.IsExteriorMinusOne Q → R.Ldeg Q = 1 := by
    intro Q hQ
    rw [R.Ldeg_eq_neg_Kdeg_sub, Kdeg_eq_neg_one_of_isMinusOne R Q hQ.1]
    simp only [hlam0, zero_mul, Finset.sum_const_zero]
    push_cast
    ring
  have hshort : R.IsShortestExteriorMinusOne R' :=
    ⟨hR', fun Q hQ => by rw [hLdeg_one R' hR', hLdeg_one Q hQ]⟩
  -- Proposition 6.2(ii) gives `#Sing(X) ≤ 7` (indeed `≤ 4`), a contradiction
  have h4 := hU1 R' W hshort (hw2' W) hcontactW hcontactOther
  omega

include hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2 hR' d0 d1 d2 dP hclass in
/-- **Manuscript Proposition 6.6 (`prop:three-contact-single-component`, lines 1880–1934)**, with
Proposition 6.2(ii) discharged by `KltDP.Manuscript.S06.squareOneBound_U1`. -/
theorem threeContactSingleComponent (p : ℕ) [CharP k p] (hp : 2 < p) :
    R.X.singularPoints.card ≤ 7 :=
  threeContactSingleComponent_of R P C₀ C₁ C₂ hP h01 h02 h12 hn01 hn02 hn12 hw0 hw1 hw2 hc0 hc1 hc2
    R' hR' d0 d1 d2 dP hclass p hp
    (fun P' W hP' hW hPW hother => KltDP.Manuscript.S06.squareOneBound_U1 R p hp P' hP' W hW hPW hother)

end Single

end KltDP.Manuscript.S06Adj

namespace KltDP.Manuscript.S06

/-! Re-exports of the headline results of `KltDP.Manuscript.S06Adj` into the manuscript's §6
namespace (the module lives in the sibling namespace `S06Adj` to avoid clashes with the
square-one modules of the same section). -/

alias threeContactSingleComponent_of := KltDP.Manuscript.S06Adj.threeContactSingleComponent_of
alias threeContactSingleComponent := KltDP.Manuscript.S06Adj.threeContactSingleComponent

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06Adj.threeContactSingleComponent_of
#print axioms KltDP.Manuscript.S06Adj.threeContactSingleComponent
#print axioms KltDP.Manuscript.S06Adj.green_isolated
