import KltDP.Manuscript.S06.SquareOneAdjoint
import KltDP.Manuscript.S05.EightCurveForest
import KltDP.Geometry.KltResolutionNoetherRelation
import KltDP.Geometry.KltResolutionPicardRank

/-!
# Manuscript Proposition 6.2: singular-point bounds for square-one configurations

Source: `source/manuscript.tex`, lines 1640–1718, label `prop:square-one-bound`.

For the resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface in characteristic
`p > 2` and a *shortest* exterior `(-1)`-curve `P` (`R.IsShortestExteriorMinusOne P`):

* (i) `squareOneBound_i`: if `C ⊂ D` has weight two and `m = P · C ≥ 2`, then `P` is the only
  exterior null curve of the nef and big class `G = C + mP` (projection of `L` to the negative
  definite `G^⊥` and Hodge index on the orthogonal pair `P, Q`);
* (ii) `squareOneBound_U1`, `squareOneBound_U2`: a configuration of type (U1) or (U2) centred at
  `P` forces `K_S + A ∼ 0`, all exceptional weights two, `λ = 0`, `L ≡ -K_S`, `L² = 1`,
  `ρ(S) = 9`, eight exceptional curves, and (Lemma 5.4) at most four connected components,
  hence `#Sing(X) ≤ 4 ≤ 7`;
* (iii) `squareOneBound_U3`: a configuration of type (U3) forces `-K_S ∼ B + P`, `B` isolated,
  the other eight exceptional curves of weight two and disjoint from `P`, `K_S² = 0`,
  `ρ(S) = 10`, and (Lemma 5.4 on `D - B` with `U = ⟨B, P⟩` of determinant `-1`) at most five
  connected components, hence `#Sing(X) ≤ 5 ≤ 7`.

The structural clauses are stated as separate lemmas (`squareOneStructure_of_Knum_eq_neg`,
`squareOneStructure_U3`); the singular-point bounds `R.X.singularPoints.card ≤ 7` are the main
statements. Shortestness enters only through `hP.2` applied to the exterior null curves
produced by Lemma 6.1, which are `(-1)`-curves by Lemma 2.9.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Lattices.SmallADEForestLattice
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S05

universe u

namespace KltDP.Manuscript.S06

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

local notation "𝒞" => DisjointNegativeCurvesRank.curveClass R.S R.hreg
local notation "𝔅" => R.S.numericalIntersectionBilinForm R.hreg

/-! ### The square-one classes are nef with square one and `K_S · A = -1` -/

theorem squareOneClass_U1 (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (W : R.Vertices) (hW : R.w W = 2) (hPW : R.contact P W = 2) :
    (∀ C, 0 ≤ R.S.numericalRestrictionDegree C (𝒞 W.val + 𝒞 P)) ∧
      𝔅 (𝒞 W.val + 𝒞 P) (𝒞 W.val + 𝒞 P) = 1 ∧ 𝔅 R.Knum (𝒞 W.val + 𝒞 P) = -1 := by
  have hPW' : P ≠ W.val := fun h => hP.2 (h ▸ W.property)
  have hWW : 𝔅 (𝒞 W.val) (𝒞 W.val) = -2 := by rw [pairing_vertex_self, hW]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hPWp : 𝔅 (𝒞 P) (𝒞 W.val) = 2 := by rw [pairing_contact, hPW]; norm_num
  have hWPp : 𝔅 (𝒞 W.val) (𝒞 P) = 2 := by rw [pairing_symm, hPWp]
  have hKW : 𝔅 R.Knum (𝒞 W.val) = 0 := by rw [Knum_pairing_vertex, hW]; norm_num
  have hKP : 𝔅 R.Knum (𝒞 P) = -1 := Knum_pairing_minusOne R P hP.1
  refine ⟨?_, ?_, ?_⟩
  · intro C
    rw [deg_eq_pairing, LinearMap.BilinForm.add_left]
    by_cases hCW : C = W.val
    · rw [hCW, hWW, hPWp]; norm_num
    by_cases hCP : C = P
    · rw [hCP, hWPp, hPP]; norm_num
    exact add_nonneg (pairing_nonneg_of_ne R _ _ (Ne.symm hCW))
      (pairing_nonneg_of_ne R _ _ (Ne.symm hCP))
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hWW, hPP, hPWp, hWPp]
    norm_num
  · rw [LinearMap.BilinForm.add_right, hKW, hKP]; norm_num

theorem squareOneClass_U2 (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (U V : R.Vertices) (hwU : R.w U = 2) (hwV : R.w V = 2) (hadj : R.graph.Adj U V)
    (hPU : R.contact P U = 1) (hPV : R.contact P V = 1) :
    (∀ C, 0 ≤ R.S.numericalRestrictionDegree C (𝒞 U.val + 𝒞 V.val + 𝒞 P)) ∧
      𝔅 (𝒞 U.val + 𝒞 V.val + 𝒞 P) (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 1 ∧
      𝔅 R.Knum (𝒞 U.val + 𝒞 V.val + 𝒞 P) = -1 := by
  have hUU : 𝔅 (𝒞 U.val) (𝒞 U.val) = -2 := by rw [pairing_vertex_self, hwU]
  have hVV : 𝔅 (𝒞 V.val) (𝒞 V.val) = -2 := by rw [pairing_vertex_self, hwV]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hUVp : 𝔅 (𝒞 U.val) (𝒞 V.val) = 1 := by rw [pairing_vertices, M_eq_one_of_adj R hadj]
  have hVUp : 𝔅 (𝒞 V.val) (𝒞 U.val) = 1 := by rw [pairing_symm, hUVp]
  have hPUp : 𝔅 (𝒞 P) (𝒞 U.val) = 1 := by rw [pairing_contact, hPU]; norm_num
  have hUPp : 𝔅 (𝒞 U.val) (𝒞 P) = 1 := by rw [pairing_symm, hPUp]
  have hPVp : 𝔅 (𝒞 P) (𝒞 V.val) = 1 := by rw [pairing_contact, hPV]; norm_num
  have hVPp : 𝔅 (𝒞 V.val) (𝒞 P) = 1 := by rw [pairing_symm, hPVp]
  have hKU : 𝔅 R.Knum (𝒞 U.val) = 0 := by rw [Knum_pairing_vertex, hwU]; norm_num
  have hKV : 𝔅 R.Knum (𝒞 V.val) = 0 := by rw [Knum_pairing_vertex, hwV]; norm_num
  have hKP : 𝔅 R.Knum (𝒞 P) = -1 := Knum_pairing_minusOne R P hP.1
  refine ⟨?_, ?_, ?_⟩
  · intro C
    rw [deg_eq_pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left]
    by_cases hCU : C = U.val
    · rw [hCU, hUU, hVUp, hPUp]; norm_num
    by_cases hCV : C = V.val
    · rw [hCV, hUVp, hVV, hPVp]; norm_num
    by_cases hCP : C = P
    · rw [hCP, hUPp, hVPp, hPP]; norm_num
    exact add_nonneg (add_nonneg (pairing_nonneg_of_ne R _ _ (Ne.symm hCU))
      (pairing_nonneg_of_ne R _ _ (Ne.symm hCV))) (pairing_nonneg_of_ne R _ _ (Ne.symm hCP))
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hUU, hVV, hPP, hUVp,
      hVUp, hPUp, hUPp, hPVp, hVPp]
    norm_num
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, hKU, hKV, hKP]; norm_num

theorem squareOneClass_U3 (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (B : R.Vertices) (hwB : R.w B = 3) (hPB : R.contact P B = 2) :
    (∀ C, 0 ≤ R.S.numericalRestrictionDegree C (𝒞 B.val + (2 : ℚ) • 𝒞 P)) ∧
      𝔅 (𝒞 B.val + (2 : ℚ) • 𝒞 P) (𝒞 B.val + (2 : ℚ) • 𝒞 P) = 1 ∧
      𝔅 R.Knum (𝒞 B.val + (2 : ℚ) • 𝒞 P) = -1 := by
  have hBB : 𝔅 (𝒞 B.val) (𝒞 B.val) = -3 := by rw [pairing_vertex_self, hwB]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hPBp : 𝔅 (𝒞 P) (𝒞 B.val) = 2 := by rw [pairing_contact, hPB]; norm_num
  have hBPp : 𝔅 (𝒞 B.val) (𝒞 P) = 2 := by rw [pairing_symm, hPBp]
  have hKB : 𝔅 R.Knum (𝒞 B.val) = 1 := by rw [Knum_pairing_vertex, hwB]; norm_num
  have hKP : 𝔅 R.Knum (𝒞 P) = -1 := Knum_pairing_minusOne R P hP.1
  refine ⟨?_, ?_, ?_⟩
  · intro C
    rw [deg_eq_pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
    by_cases hCB : C = B.val
    · rw [hCB, hBB, hPBp]; norm_num
    by_cases hCP : C = P
    · rw [hCP, hBPp, hPP]; norm_num
    have h1 := pairing_nonneg_of_ne R B.val C (Ne.symm hCB)
    have h2 := pairing_nonneg_of_ne R P C (Ne.symm hCP)
    linarith
  · simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hBB, hPP, hPBp, hBPp]
    norm_num
  · rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hKB, hKP]; norm_num

/-! ### Counting components and singular points -/

/-- The components of the exceptional forest are covered by the components of the induced
subforest on `F` together with the vertices outside `F`. -/
theorem card_components_le [DecidableEq R.Vertices] (F : Finset R.Vertices) :
    Nat.card R.graph.ConnectedComponent ≤
      Nat.card (R.graph.induce (F : Set R.Vertices)).ConnectedComponent +
        (Finset.univ \ F).card := by
  classical
  let s : Set R.Vertices := (F : Set R.Vertices)
  let G := R.graph.induce s
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype R.graph.ConnectedComponent := Fintype.ofFinite _
  let ι : G →g R.graph := ⟨Subtype.val, fun h => h⟩
  let φ : G.ConnectedComponent ⊕ ↥(Finset.univ \ F) → R.graph.ConnectedComponent :=
    Sum.elim (fun c => c.map ι) (fun v => R.graph.connectedComponentMk v.val)
  have hφ : Function.Surjective φ := by
    intro c
    refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
    by_cases hv : v ∈ F
    · exact ⟨Sum.inl (G.connectedComponentMk ⟨v, hv⟩), rfl⟩
    · exact ⟨Sum.inr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩, rfl⟩
  have hcard := Fintype.card_le_of_surjective φ hφ
  rw [Fintype.card_sum, Fintype.card_coe] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcard

/-- `#Sing(X)` is the number of connected components of the exceptional forest (union). -/
theorem singularPoints_card_eq :
    R.X.singularPoints.card = Nat.card R.graph.ConnectedComponent :=
  (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.1

/-! ### (i) The projection inequality -/

set_option maxHeartbeats 1000000 in
/-- **Proposition 6.2 (i)** (manuscript lines 1666–1675): for a weight-two `C ⊂ D` with
`m = P · C ≥ 2` and `P` shortest, `P` is the only exterior null curve of `G = C + mP`. -/
theorem squareOneBound_i (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (C : R.Vertices) (hC : R.w C = 2) (hm : 2 ≤ R.contact P C)
    (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q)
    (hnull : R.S.numericalRestrictionDegree Q (𝒞 C.val + (R.contact P C : ℚ) • 𝒞 P) = 0) :
    Q = P := by
  classical
  have hm2 : (2 : ℚ) ≤ (R.contact P C : ℚ) := by exact_mod_cast hm
  have hmm : (4 : ℚ) ≤ (R.contact P C : ℚ) * (R.contact P C : ℚ) := by
    have := mul_le_mul hm2 hm2 (by norm_num) (by linarith)
    linarith
  set m : ℚ := (R.contact P C : ℚ) with hmdef
  have hCC : 𝔅 (𝒞 C.val) (𝒞 C.val) = -2 := by rw [pairing_vertex_self, hC]
  have hPC : 𝔅 (𝒞 P) (𝒞 C.val) = m := pairing_contact R P C
  have hCP : 𝔅 (𝒞 C.val) (𝒞 P) = m := by rw [pairing_symm, hPC]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1.1
  set G : R.S.NumericalClassGroup := 𝒞 C.val + m • 𝒞 P with hGdef
  have hdegG : ∀ X, R.S.numericalRestrictionDegree X G =
      𝔅 (𝒞 C.val) (𝒞 X) + m * 𝔅 (𝒞 P) (𝒞 X) := by
    intro X
    rw [hGdef, deg_eq_pairing, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left]
  have hGP : R.S.numericalRestrictionDegree P G = 0 := by rw [hdegG, hCP, hPP]; ring
  have hGC : R.S.numericalRestrictionDegree C.val G = m * m - 2 := by rw [hdegG, hCC, hPC]; ring
  have hnef : ∀ X, 0 ≤ R.S.numericalRestrictionDegree X G := by
    intro X
    by_cases hXC : X = C.val
    · rw [hXC, hGC]; linarith
    by_cases hXP : X = P
    · rw [hXP, hGP]
    rw [hdegG]
    have h1 := pairing_nonneg_of_ne R C.val X (Ne.symm hXC)
    have h2 := pairing_nonneg_of_ne R P X (Ne.symm hXP)
    exact add_nonneg h1 (mul_nonneg (by linarith) h2)
  have hbig : 0 < 𝔅 G G := by
    rw [hGdef]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hCC, hCP, hPC, hPP]
    linarith
  refine Classical.byContradiction fun hQP => ?_
  obtain ⟨hQm, -⟩ := exteriorNullCurve_isMinusOne R G hnef hbig Q hQ hnull
  have hQP0 : 𝔅 (𝒞 Q) (𝒞 P) = 0 := by
    rw [DisjointNegativeCurvesRank.curveClass_pairing,
      exteriorNullCurves_intersectionPairing_eq_zero R G hnef hbig Q P hQ hP.1.2 hnull hGP hQP]
    simp
  have hPQ0 : 𝔅 (𝒞 P) (𝒞 Q) = 0 := by rw [pairing_symm, hQP0]
  have hCQ0 : 𝔅 (𝒞 C.val) (𝒞 Q) = 0 := by
    have h := hnull
    rw [hdegG, hPQ0, mul_zero, add_zero] at h
    exact h
  have hQC0 : 𝔅 (𝒞 Q) (𝒞 C.val) = 0 := by rw [pairing_symm, hCQ0]
  have hQQ : 𝔅 (𝒞 Q) (𝒞 Q) = -1 := pairing_minusOne_self R Q hQm
  -- degrees of `L`
  have hℓpos : 0 < R.Ldeg P := Ldeg_pos R P hP.1.2
  have hvpos : 0 < R.Lsq := R.Lsq_pos
  have hLQge : R.Ldeg P ≤ R.Ldeg Q := hP.2 Q ⟨hQm, hQ⟩
  have hLC : 𝔅 R.Lnum (𝒞 C.val) = 0 := by rw [Lnum_pairing, R.Ldeg_exceptional C]
  have hLP : 𝔅 R.Lnum (𝒞 P) = R.Ldeg P := Lnum_pairing R P
  have hLQ : 𝔅 R.Lnum (𝒞 Q) = R.Ldeg Q := Lnum_pairing R Q
  have hLL : 𝔅 R.Lnum R.Lnum = R.Lsq := rfl
  have hm22 : 0 < m * m - 2 := by linarith
  -- the auxiliary class `z ∈ G^⊥` orthogonal to `P` and `Q`
  set a : ℚ := m * R.Ldeg P / (m * m - 2) with hadef
  have ha : a * (m * m - 2) = m * R.Ldeg P := by
    rw [hadef]
    field_simp
  set z : R.S.NumericalClassGroup :=
    R.Lnum - a • 𝒞 C.val - (a * m) • 𝒞 P + R.Ldeg P • 𝒞 P + R.Ldeg Q • 𝒞 Q with hzdef
  have hGz : 𝔅 G z = 0 := by
    rw [hGdef, hzdef]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, hCC, hCP, hPC, hPP, hCQ0, hPQ0,
      pairing_symm R (𝒞 C.val) R.Lnum, pairing_symm R (𝒞 P) R.Lnum, hLC, hLP]
    linear_combination (-1 : ℚ) * ha
  have hzz : 𝔅 z z = R.Lsq - a * m * R.Ldeg P + R.Ldeg P * R.Ldeg P + R.Ldeg Q * R.Ldeg Q := by
    rw [hzdef]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hCC, hCP, hPC, hPP, hCQ0,
      hPQ0, hQC0, hQP0, hQQ, pairing_symm R (𝒞 C.val) R.Lnum, pairing_symm R (𝒞 P) R.Lnum,
      pairing_symm R (𝒞 Q) R.Lnum, hLC, hLP, hLQ, hLL]
    linear_combination a * ha
  have hz2 : 𝔅 z z ≤ 0 := by
    by_cases hz0 : 0 ≤ 𝔅 z z
    · have hz := NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal R.S R.hreg G z
        hbig hGz hz0
      rw [hz]
      simp
    · linarith
  have h1 : (m * m - 2) * 𝔅 z z ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hz2 hm22.le
    rwa [mul_zero] at this
  rw [hzz] at h1
  have h3 : (m * m - 2) * (a * m * R.Ldeg P) = m * m * R.Ldeg P * R.Ldeg P := by
    rw [show (m * m - 2) * (a * m * R.Ldeg P) = (a * (m * m - 2)) * (m * R.Ldeg P) by ring, ha]
    ring
  have h4 : 0 ≤ (m * m - 2) * ((R.Ldeg Q - R.Ldeg P) * (R.Ldeg Q + R.Ldeg P)) :=
    mul_nonneg hm22.le (mul_nonneg (by linarith) (by linarith))
  have h5 : 0 ≤ (m * m - 4) * (R.Ldeg P * R.Ldeg P) :=
    mul_nonneg (by linarith) (mul_nonneg hℓpos.le hℓpos.le)
  have h6 : 0 < (m * m - 2) * R.Lsq := mul_pos hm22 hvpos
  linarith [h1, h3, h4, h5, h6]

/-- A curve with positive coefficient in an effective `N` has `L`-degree at most `L · N`. -/
theorem Ldeg_le_of_pos_coeff (N : R.S.WeilDivisor) (hN : EffectiveDivisor N) (Q : R.S.PrimeCurve)
    (hQ : 0 < N Q) : R.Ldeg Q ≤ N.sum fun C a => (a : ℚ) * R.Ldeg C := by
  classical
  unfold Finsupp.sum
  have hQmem : Q ∈ N.support := Finsupp.mem_support_iff.mpr hQ.ne'
  rw [← Finset.add_sum_erase _ _ hQmem]
  dsimp only
  have h0 : 0 ≤ ∑ C ∈ N.support.erase Q, (N C : ℚ) * R.Ldeg C :=
    Finset.sum_nonneg (fun C _ => mul_nonneg (by exact_mod_cast hN C) (R.Ldeg_nonneg C))
  have h1 : (1 : ℚ) ≤ N Q := by exact_mod_cast hQ
  have h2 : R.Ldeg Q ≤ (N Q : ℚ) * R.Ldeg Q := by
    have := mul_le_mul_of_nonneg_right h1 (R.Ldeg_nonneg Q)
    linarith
  linarith

/-! ### (ii) Types (U1) and (U2) -/

/-- The Picard identity `K_S + A ∼ N` in numerical form. -/
theorem numW_of_pic (N : R.S.WeilDivisor) (x y z : R.S.PrimeCurve)
    (hPic : cartierPicardClass R.S.toScheme R.KS * R.curvePic x * R.curvePic y * R.curvePic z =
      R.S.regularWeilPicardClass R.hreg N) :
    R.Knum + 𝒞 x + 𝒞 y + 𝒞 z = numW R N := by
  have h := congrArg (fun c => R.S.picardNumericalMap (Additive.ofMul c)) hPic
  simp only [ofMul_mul, map_add, R.S.picardNumericalMap_regularWeilPicardClass R.hreg] at h
  exact h

theorem numW_of_pic₂ (N : R.S.WeilDivisor) (x y : R.S.PrimeCurve)
    (hPic : cartierPicardClass R.S.toScheme R.KS * R.curvePic x * R.curvePic y =
      R.S.regularWeilPicardClass R.hreg N) :
    R.Knum + 𝒞 x + 𝒞 y = numW R N := by
  have h := congrArg (fun c => R.S.picardNumericalMap (Additive.ofMul c)) hPic
  simp only [ofMul_mul, map_add, R.S.picardNumericalMap_regularWeilPicardClass R.hreg] at h
  exact h

theorem numW_of_pic_U3 (N : R.S.WeilDivisor) (x P : R.S.PrimeCurve)
    (hPic : cartierPicardClass R.S.toScheme R.KS * R.curvePic x * R.curvePic P ^ 2 =
      R.curvePic P * R.S.regularWeilPicardClass R.hreg N) :
    R.Knum + 𝒞 x + (2 : ℚ) • 𝒞 P = 𝒞 P + numW R N := by
  have h := congrArg (fun c => R.S.picardNumericalMap (Additive.ofMul c)) hPic
  simp only [ofMul_mul, ofMul_pow, map_add, map_nsmul,
    R.S.picardNumericalMap_regularWeilPicardClass R.hreg] at h
  have h2 : (2 : ℚ) • 𝒞 P = 2 • 𝒞 P := by rw [two_smul, two_nsmul]
  rw [h2]
  exact h

/-- **Proposition 6.2 (ii), structure**: if `-K_S ≡ a` with `a` nef of square one, then all
exceptional weights are two, `λ = 0`, `L ≡ a ≡ -K_S`, `L² = K_S² = 1`, `ρ(S) = 9`, there are
eight exceptional curves, and (Lemma 5.4) `#Sing(X) ≤ 4`. -/
theorem squareOneStructure_of_Knum_eq_neg (p : ℕ) [CharP k p] (hp : 2 < p)
    (a : R.S.NumericalClassGroup) (hnef : ∀ C, 0 ≤ R.S.numericalRestrictionDegree C a)
    (ha2 : 𝔅 a a = 1) (hK : R.Knum = -a) :
    (∀ i, R.w i = 2) ∧ (∀ i, R.lam i = 0) ∧ R.Lnum = a ∧ R.Lsq = 1 ∧ R.Ksq = 1 ∧
      R.S.picardRank = 9 ∧ Fintype.card R.Vertices = 8 ∧ R.X.singularPoints.card ≤ 4 := by
  classical
  have hp0 : 0 < p := by omega
  have hw : ∀ i, R.w i = 2 := by
    intro i
    have h1 : 𝔅 R.Knum (𝒞 i.val) = R.w i - 2 := Knum_pairing_vertex R i
    rw [hK, LinearMap.BilinForm.neg_left, ← deg_eq_pairing] at h1
    have h2 := hnef i.val
    have h3 := R.two_le_w i
    linarith
  have hq : R.q = 0 := by
    funext i
    show R.w i - 2 = 0
    rw [hw i]
    norm_num
  have hlam : R.lam = 0 := by
    rw [← A_inv_mulVec_q R, hq, Matrix.mulVec_zero]
  have hL : R.Lnum = a := by
    rw [R.Lnum_eq, hK, hlam]
    simp
  have hLsq : R.Lsq = 1 := by
    show 𝔅 R.Lnum R.Lnum = 1
    rw [hL, ha2]
  have hKsq : R.Ksq = 1 := by
    show 𝔅 R.Knum R.Knum = 1
    rw [hK, LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg, ha2]
  have hKK : R.S.intersectionPairing R.hreg R.KS R.KS = 1 := by
    have h := R.Ksq_eq_intersectionPairing
    rw [hKsq] at h
    exact_mod_cast h.symm
  have hN := R.hmin.noetherRelation_of_kltDelPezzo R.hDP R.hrank p hp0 R.KS R.eKS
  change R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 at hN
  have hrho : R.S.picardRank = 9 := by omega
  have hρ := R.hmin.picardRank_eq_of_klt R.hklt p hp0
  rw [R.hrank] at hρ
  have h6 : Nat.card (ActualExceptionalIncidence.Vertices R.π) = Fintype.card R.Vertices :=
    Nat.card_eq_fintype_card
  have hcard : Fintype.card R.Vertices = 8 := by omega
  -- Lemma 5.4 with `F = D` and `U = ℤ K_S`
  have hKcls : R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (Kcls R) = 1 := by
    rw [integralPicardIntersectionBilinForm_apply]
    simp only [Kcls, cartierPicardHom_apply, toMul_ofMul]
    rw [R.S.picardPairing_class R.hreg, hKK]
  let u : PUnit.{u + 1} → Additive R.S.toScheme.Pic := fun _ => Kcls R
  have hu : (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg) u).det.natAbs = 1 := by
    rw [Matrix.det_unique]
    show (R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (Kcls R)).natAbs = 1
    rw [hKcls]
    rfl
  have hperp : ∀ v ∈ (Finset.univ : Finset R.Vertices), ∀ i : PUnit.{u + 1},
      R.S.integralPicardIntersectionBilinForm R.hreg (cls R v) (u i) = 0 := by
    intro v _ i
    have h := pairing_Kcls_cls R v
    rw [hw v] at h
    have h' : (R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (cls R v) : ℚ) = 0 := by
      rw [h]
      norm_num
    have h'' : R.S.integralPicardIntersectionBilinForm R.hreg (Kcls R) (cls R v) = 0 := by
      exact_mod_cast h'
    show R.S.integralPicardIntersectionBilinForm R.hreg (cls R v) (Kcls R) = 0
    rw [(R.S.integralPicardIntersectionBilinForm_isSymm R.hreg).eq]
    exact h''
  have hcomp := eightWeightTwoCurves R p hp (Finset.univ : Finset R.Vertices)
    (by rw [Finset.card_univ, hcard]) (fun v _ => hw v) (fun v _ y _ => Finset.mem_univ y) u hu
    hperp (by rw [Fintype.card_punit, hcard])
  have hle := card_components_le R (Finset.univ : Finset R.Vertices)
  rw [Finset.sdiff_self, Finset.card_empty, add_zero] at hle
  refine ⟨hw, fun i => by rw [hlam]; rfl, hL, hLsq, hKsq, hrho, hcard, ?_⟩
  rw [singularPoints_card_eq]
  omega

/-- **Proposition 6.2 (ii), type (U1)**: `#Sing(X) ≤ 7`. -/
theorem squareOneBound_U1 (p : ℕ) [CharP k p] (hp : 2 < p)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (W : R.Vertices) (hW : R.w W = 2) (hPW : R.contact P W = 2)
    (hother : ∀ i : R.Vertices, i ≠ W → R.contact P i = 0) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  obtain ⟨N, hN, hPic, hL, hnull, hdisj, hpos, hiff⟩ :=
    squareOneAdjoint_U1 R p (by omega) P hP.1 W hW hPW hother
  obtain ⟨hnefA, hA2, hKA⟩ := squareOneClass_U1 R P hP.1 W hW hPW
  -- shortestness excludes every exterior `A`-null curve outside `Supp A`
  have hno : ¬ ∃ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q ∧
      R.S.numericalRestrictionDegree Q (𝒞 W.val + 𝒞 P) = 0 ∧
      Q ∉ (Finsupp.single W.val (1 : ℤ) + Finsupp.single P 1).support := by
    rintro ⟨Q, hQ, hQnull, hQA⟩
    have hQpos := hpos Q hQ hQnull hQA
    obtain ⟨hQm, -⟩ := exteriorNullCurve_isMinusOne R _ hnefA (by rw [hA2]; norm_num) Q hQ hQnull
    have hle : R.Ldeg P ≤ R.Ldeg Q := hP.2 Q ⟨hQm, hQ⟩
    have hle2 := Ldeg_le_of_pos_coeff R N hN Q hQpos
    rw [hL] at hle2
    have hv := R.Lsq_pos
    linarith
  have hN0 : N = 0 := hiff.mpr hno
  rw [hN0] at hPic
  have hK : R.Knum = -(𝒞 W.val + 𝒞 P) := by
    have h := numW_of_pic₂ R 0 W.val P hPic
    rw [numW_zero] at h
    have h2 : R.Knum + (𝒞 W.val + 𝒞 P) = 0 := by
      rw [← add_assoc]
      exact h
    exact eq_neg_of_add_eq_zero_left h2
  have := (squareOneStructure_of_Knum_eq_neg R p hp _ hnefA hA2 hK).2.2.2.2.2.2.2
  omega

/-- **Proposition 6.2 (ii), type (U2)**: `#Sing(X) ≤ 7`. -/
theorem squareOneBound_U2 (p : ℕ) [CharP k p] (hp : 2 < p)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (U V : R.Vertices) (hUV : U ≠ V) (hwU : R.w U = 2) (hwV : R.w V = 2)
    (hadj : R.graph.Adj U V) (hPU : R.contact P U = 1) (hPV : R.contact P V = 1)
    (hother : ∀ i : R.Vertices, i ≠ U → i ≠ V → R.contact P i = 0)
    (hdistinct :
      Disjoint ((U.val : Set R.S.toScheme) ∩ (V.val : Set R.S.toScheme))
        ((U.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme)) ∧
      Disjoint ((U.val : Set R.S.toScheme) ∩ (V.val : Set R.S.toScheme))
        ((V.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme)) ∧
      Disjoint ((U.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme))
        ((V.val : Set R.S.toScheme) ∩ (P : Set R.S.toScheme))) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  obtain ⟨N, hN, hPic, hL, hnull, hdisj, hpos, hiff⟩ :=
    squareOneAdjoint_U2 R p (by omega) P hP.1 U V hUV hwU hwV hadj hPU hPV hother hdistinct
  obtain ⟨hnefA, hA2, hKA⟩ := squareOneClass_U2 R P hP.1 U V hwU hwV hadj hPU hPV
  have hno : ¬ ∃ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q ∧
      R.S.numericalRestrictionDegree Q (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 0 ∧
      Q ∉ (Finsupp.single U.val (1 : ℤ) + Finsupp.single V.val 1 +
        Finsupp.single P 1).support := by
    rintro ⟨Q, hQ, hQnull, hQA⟩
    have hQpos := hpos Q hQ hQnull hQA
    obtain ⟨hQm, -⟩ := exteriorNullCurve_isMinusOne R _ hnefA (by rw [hA2]; norm_num) Q hQ hQnull
    have hle : R.Ldeg P ≤ R.Ldeg Q := hP.2 Q ⟨hQm, hQ⟩
    have hle2 := Ldeg_le_of_pos_coeff R N hN Q hQpos
    rw [hL] at hle2
    have hv := R.Lsq_pos
    linarith
  have hN0 : N = 0 := hiff.mpr hno
  rw [hN0] at hPic
  have hK : R.Knum = -(𝒞 U.val + 𝒞 V.val + 𝒞 P) := by
    have h := numW_of_pic R 0 U.val V.val P hPic
    rw [numW_zero] at h
    have h2 : R.Knum + (𝒞 U.val + 𝒞 V.val + 𝒞 P) = 0 := by
      rw [← add_assoc, ← add_assoc]
      exact h
    exact eq_neg_of_add_eq_zero_left h2
  have := (squareOneStructure_of_Knum_eq_neg R p hp _ hnefA hA2 hK).2.2.2.2.2.2.2
  omega

/-! ### (iii) Type (U3) -/

/-- **Proposition 6.2 (iii), structure**: if `-K_S ≡ B + P` with `B ⊂ D` of weight three and
`P · B = 2`, then every other exceptional curve has weight two and is disjoint from `B` and
`P`, `B` is isolated, `K_S² = 0`, `ρ(S) = 10`, there are nine exceptional curves, `λ_B = 1/3`,
`λ = 0` elsewhere, `L ≡ (2/3) B + P`, `L² = L · P = 1/3`, and (Lemma 5.4 on `D - B` with
`U = ⟨B, P⟩`) `#Sing(X) ≤ 5`. -/
theorem squareOneStructure_U3 (p : ℕ) [CharP k p] (hp : 2 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P)
    (B : R.Vertices) (hwB : R.w B = 3) (hPB : R.contact P B = 2)
    (hK : R.Knum = -(𝒞 B.val + 𝒞 P)) :
    (∀ i, i ≠ B → R.w i = 2 ∧ ¬ R.graph.Adj B i ∧ R.contact P i = 0) ∧
      (∀ y, ¬ R.graph.Adj B y) ∧ R.Ksq = 0 ∧ R.S.picardRank = 10 ∧
      Fintype.card R.Vertices = 9 ∧
      R.lam B = 1 / 3 ∧ (∀ i, i ≠ B → R.lam i = 0) ∧
      R.Lnum = (2 / 3 : ℚ) • 𝒞 B.val + 𝒞 P ∧ R.Lsq = 1 / 3 ∧ R.Ldeg P = 1 / 3 ∧
      R.X.singularPoints.card ≤ 5 := by
  classical
  have hp0 : 0 < p := by omega
  have hBB : 𝔅 (𝒞 B.val) (𝒞 B.val) = -3 := by rw [pairing_vertex_self, hwB]
  have hPP : 𝔅 (𝒞 P) (𝒞 P) = -1 := pairing_minusOne_self R P hP.1
  have hPBp : 𝔅 (𝒞 P) (𝒞 B.val) = 2 := by rw [pairing_contact, hPB]; norm_num
  have hBPp : 𝔅 (𝒞 B.val) (𝒞 P) = 2 := by rw [pairing_symm, hPBp]
  have hother : ∀ i, i ≠ B → R.w i = 2 ∧ ¬ R.graph.Adj B i ∧ R.contact P i = 0 := by
    intro i hi
    have h1 : 𝔅 R.Knum (𝒞 i.val) = R.w i - 2 := Knum_pairing_vertex R i
    rw [hK, LinearMap.BilinForm.neg_left, LinearMap.BilinForm.add_left, pairing_vertices,
      pairing_contact] at h1
    have h2 := R.M_offDiag_nonneg B i (Ne.symm hi)
    have h3 : (0 : ℚ) ≤ (R.contact P i : ℚ) := by
      exact_mod_cast contact_nonneg_of_not_exceptional R P hP.2 i
    have h4 := R.two_le_w i
    have hw : R.w i = 2 := by linarith
    have hM : R.M B i = 0 := by linarith
    have hc : (R.contact P i : ℚ) = 0 := by linarith
    exact ⟨hw, not_adj_of_M_eq_zero R (Ne.symm hi) hM, by exact_mod_cast hc⟩
  have hBiso : ∀ y, ¬ R.graph.Adj B y := by
    intro y hy
    by_cases hyB : y = B
    · subst hyB
      exact R.graph.loopless _ hy
    · exact (hother y hyB).2.1 hy
  have hKsq : R.Ksq = 0 := by
    show 𝔅 R.Knum R.Knum = 0
    rw [hK]
    simp only [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hBB, hPP, hPBp, hBPp]
    norm_num
  have hKK : R.S.intersectionPairing R.hreg R.KS R.KS = 0 := by
    have h := R.Ksq_eq_intersectionPairing
    rw [hKsq] at h
    exact_mod_cast h.symm
  have hN := R.hmin.noetherRelation_of_kltDelPezzo R.hDP R.hrank p hp0 R.KS R.eKS
  change R.S.intersectionPairing R.hreg R.KS R.KS + (R.S.picardRank : ℤ) = 10 at hN
  have hrho : R.S.picardRank = 10 := by omega
  have hρ := R.hmin.picardRank_eq_of_klt R.hklt p hp0
  rw [R.hrank] at hρ
  have h6 : Nat.card (ActualExceptionalIncidence.Vertices R.π) = Fintype.card R.Vertices :=
    Nat.card_eq_fintype_card
  have hcard : Fintype.card R.Vertices = 9 := by omega
  -- the discrepancies: `λ_B = 1/3`, zero elsewhere
  let lam' : R.Vertices → ℚ := fun i => if i = B then 1 / 3 else 0
  have hlB : lam' B = 1 / 3 := by simp [lam']
  have hlO : ∀ u, u ≠ B → lam' u = 0 := fun u hu => by simp [lam', hu]
  have hAlam' : R.A *ᵥ lam' = R.q := by
    funext i
    rw [KltDP.Manuscript.S04.A_mulVec_apply]
    by_cases hi : i = B
    · rw [hi, hlB, Finset.sum_eq_zero (fun u hu =>
        absurd ((R.graph.mem_neighborFinset B u).1 hu) (hBiso u))]
      show R.w B * (1 / 3) - 0 = R.w B - 2
      rw [hwB]
      norm_num
    · rw [hlO i hi, Finset.sum_eq_zero (fun u hu => by
        have hadj := (R.graph.mem_neighborFinset i u).1 hu
        exact hlO u (fun h => hBiso i (h ▸ hadj.symm)))]
      show R.w i * 0 - 0 = R.w i - 2
      rw [(hother i hi).1]
      norm_num
  have hlam : R.lam = lam' := by
    rw [← A_inv_mulVec_q R, ← hAlam', Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul R.A (A_det_isUnit R), Matrix.one_mulVec]
  have hlamB : R.lam B = 1 / 3 := by rw [hlam, hlB]
  have hlamO : ∀ i, i ≠ B → R.lam i = 0 := fun i hi => by rw [hlam, hlO i hi]
  have hL : R.Lnum = (2 / 3 : ℚ) • 𝒞 B.val + 𝒞 P := by
    have hsum : ∑ i : R.Vertices, R.lam i • 𝒞 i.val = (1 / 3 : ℚ) • 𝒞 B.val := by
      rw [Finset.sum_eq_single B (fun i _ hi => by rw [hlamO i hi, zero_smul])
        (fun h => absurd (Finset.mem_univ B) h), hlamB]
    rw [R.Lnum_eq, hK, hsum, neg_add, neg_neg, ← sub_eq_add_neg, add_sub_right_comm]
    congr 1
    rw [show (2 / 3 : ℚ) = 1 - 1 / 3 by norm_num, sub_smul, one_smul]
  have hLsq : R.Lsq = 1 / 3 := by
    show 𝔅 R.Lnum R.Lnum = 1 / 3
    rw [hL]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hBB, hPP, hPBp, hBPp]
    norm_num
  have hLP : R.Ldeg P = 1 / 3 := by
    rw [← Lnum_pairing, hL, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hBPp, hPP]
    norm_num
  -- Lemma 5.4 on `F = D - B` with `U = ⟨B, P⟩`
  set F : Finset R.Vertices := Finset.univ.erase B with hFdef
  have hF : F.card = 8 := by
    rw [hFdef, Finset.card_erase_of_mem (Finset.mem_univ B), Finset.card_univ, hcard]
  have hwF : ∀ v ∈ F, R.w v = 2 := fun v hv => (hother v (Finset.mem_erase.mp hv).1).1
  have hclosed : ∀ v ∈ F, ∀ y, R.graph.Adj v y → y ∈ F := by
    intro v hv y hy
    rw [hFdef, Finset.mem_erase]
    refine ⟨fun h => ?_, Finset.mem_univ y⟩
    subst h
    exact hBiso v hy.symm
  let u : ULift.{u} (Fin 2) → Additive R.S.toScheme.Pic :=
    fun i => ![cls R B, primeClass R P] i.down
  have h00 : R.S.integralPicardIntersectionBilinForm R.hreg (cls R B) (cls R B) = -3 := by
    have h := pairing_cls R B B
    rw [M_diag, hwB] at h
    exact_mod_cast h
  have h01 : R.S.integralPicardIntersectionBilinForm R.hreg (cls R B) (primeClass R P) = 2 := by
    have h := pairing_cls_prime R P B
    rw [contact_apply, hPB] at h
    exact_mod_cast h
  have h10 : R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R P) (cls R B) = 2 := by
    have h := pairing_prime_cls R P B
    rw [contact_apply, hPB] at h
    exact_mod_cast h
  have h11 : R.S.integralPicardIntersectionBilinForm R.hreg (primeClass R P) (primeClass R P) =
      -1 := pairing_prime_self R P hP.1
  have hu : (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg) u).det.natAbs = 1 := by
    have hsub : (familyGram (R.S.integralPicardIntersectionBilinForm R.hreg) u).submatrix
        Equiv.ulift.symm Equiv.ulift.symm = !![-3, 2; 2, -1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [familyGram, u, h00, h01, h10, h11]
    rw [← Matrix.det_submatrix_equiv_self Equiv.ulift.symm, hsub, Matrix.det_fin_two_of]
    rfl
  have hperp : ∀ v ∈ F, ∀ i : ULift.{u} (Fin 2),
      R.S.integralPicardIntersectionBilinForm R.hreg (cls R v) (u i) = 0 := by
    intro v hv i
    have hvB : v ≠ B := (Finset.mem_erase.mp hv).1
    obtain ⟨_, hadj, hc⟩ := hother v hvB
    rcases i with ⟨i⟩
    fin_cases i
    · show R.S.integralPicardIntersectionBilinForm R.hreg (cls R v) (cls R B) = 0
      have h := pairing_cls R v B
      rw [M_eq_zero_of_not_adj R hvB (fun h' => hadj h'.symm)] at h
      exact_mod_cast h
    · show R.S.integralPicardIntersectionBilinForm R.hreg (cls R v) (primeClass R P) = 0
      have h := pairing_cls_prime R P v
      rw [contact_apply, hc] at h
      exact_mod_cast h
  have hfull : Fintype.card (ULift.{u} (Fin 2)) + 8 = Fintype.card R.Vertices + 1 := by
    rw [Fintype.card_ulift, Fintype.card_fin, hcard]
  have hcomp := eightWeightTwoCurves R p hp F hF hwF hclosed u hu hperp hfull
  have hle := card_components_le R F
  have hsd : Finset.univ \ F = {B} := by
    rw [hFdef]
    ext x
    simp [Finset.mem_erase]
  rw [hsd, Finset.card_singleton] at hle
  refine ⟨hother, hBiso, hKsq, hrho, hcard, hlamB, hlamO, hL, hLsq, hLP, ?_⟩
  rw [singularPoints_card_eq]
  omega

/-- **Proposition 6.2 (iii), type (U3)**: `#Sing(X) ≤ 7`. -/
theorem squareOneBound_U3 (p : ℕ) [CharP k p] (hp : 2 < p)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (B : R.Vertices) (hwB : R.w B = 3) (hPB : R.contact P B = 2)
    (hother : ∀ i : R.Vertices, i ≠ B → R.contact P i = 0) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  obtain ⟨N, hN, hPic, hL, hnull, hdisj, hpos, hiff⟩ :=
    squareOneAdjoint_U3 R p (by omega) P hP.1 B hwB hPB hother
  obtain ⟨hnefA, hA2, hKA⟩ := squareOneClass_U3 R P hP.1 B hwB hPB
  have hno : ¬ ∃ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q ∧
      R.S.numericalRestrictionDegree Q (𝒞 B.val + (2 : ℚ) • 𝒞 P) = 0 ∧
      Q ∉ (Finsupp.single B.val (1 : ℤ) + Finsupp.single P 2).support := by
    rintro ⟨Q, hQ, hQnull, hQA⟩
    have hQpos := hpos Q hQ hQnull hQA
    obtain ⟨hQm, -⟩ := exteriorNullCurve_isMinusOne R _ hnefA (by rw [hA2]; norm_num) Q hQ hQnull
    have hle : R.Ldeg P ≤ R.Ldeg Q := hP.2 Q ⟨hQm, hQ⟩
    have hle2 := Ldeg_le_of_pos_coeff R N hN Q hQpos
    rw [hL] at hle2
    have hv := R.Lsq_pos
    linarith
  have hN0 : N = 0 := hiff.mpr hno
  rw [hN0] at hPic
  have hK : R.Knum = -(𝒞 B.val + 𝒞 P) := by
    have h := numW_of_pic_U3 R 0 B.val P hPic
    rw [numW_zero, add_zero] at h
    -- h : Knum + B + 2 • P = P
    have h2 : R.Knum + (𝒞 B.val + 𝒞 P) = 0 := by
      have h3 : R.Knum + 𝒞 B.val + (2 : ℚ) • 𝒞 P - 𝒞 P = 0 := by rw [h, sub_self]
      rw [← h3, two_smul]
      abel
    exact eq_neg_of_add_eq_zero_left h2
  have := (squareOneStructure_U3 R p hp P hP.1 B hwB hPB hK).2.2.2.2.2.2.2.2.2.2
  omega

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06.squareOneBound_i
#print axioms KltDP.Manuscript.S06.squareOneStructure_of_Knum_eq_neg
#print axioms KltDP.Manuscript.S06.squareOneBound_U1
#print axioms KltDP.Manuscript.S06.squareOneBound_U2
#print axioms KltDP.Manuscript.S06.squareOneStructure_U3
#print axioms KltDP.Manuscript.S06.squareOneBound_U3
