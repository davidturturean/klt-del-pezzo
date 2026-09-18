import KltDP.Manuscript.Datum.AnticanonicalDegrees
import KltDP.Manuscript.S07.AdjointConfiguration
import KltDP.Geometry.KltExceptionalOrthogonalRank
import KltDP.Geometry.AmpleQCartierPullbackDegrees
import KltDP.Geometry.PrimeCurvePairingSupport
import KltDP.LinearAlgebra.Stieltjes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Manuscript Lemma 2.8: the rank-one projection identity

Source: `source/manuscript.tex`, lines 604–636, label `lem:projection`.

For the resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface and an exterior
`(-1)`-curve `P` with contact vector `p_i = P · D_i`:

* `rankOneProjection_green`: `pᵀ A⁻¹ p = 1 + (L·P)² / L²` (the manuscript's (eq:green));
* `rankOneProjection_green_gt_one`: `pᵀ A⁻¹ p > 1`;
* `rankOneProjection_charge`: `pᵀ λ = 1 - L·P` (the manuscript's (eq:green-charge));
* `rankOneProjection_charge_lt_one`: `pᵀ λ < 1`;
* `A_inv_mulVec_q`: `A⁻¹ q = λ`, so `pᵀ A⁻¹ q = pᵀ λ`.

Proof of the first identity (manuscript lines 626–635): with `u = A⁻¹ p` the class
`P̄ = [P] + Σ u_i [D_i]` is orthogonal to every `D_j`, hence lies in the exceptional
orthogonal of `N¹(S)_ℚ`. That space is one-dimensional
(`IsMinimalResolution.finrank_exceptionalOrthogonal_eq_one_of_klt`, which requires the
characteristic hypotheses `(p : ℕ) [CharP k p] (hp : 0 < p)` — these are therefore taken as
explicit hypotheses of the two theorems using it) and contains `[L] ≠ 0`, so `P̄ = a [L]`;
pairing with `[L]` gives `a = (L·P)/L²`, and `P̄² = P̄ · P = -1 + pᵀ u` since `P̄ ⊥ D_i`.

The second identity is `Ldeg_eq_neg_Kdeg_sub` with `K_S · P = -1` (adjunction for the
rational curve `P` of square `-1`).

All objects are the actual union objects; nothing is assumed beyond the datum.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript

universe u

namespace KltDP.Manuscript.S02

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-- The contact vector `p_i = P · D_i` of a prime curve, as rationals. -/
def contactVector (P : R.S.PrimeCurve) : R.Vertices → ℚ := fun i => (R.contact P i : ℚ)

/-! ### Pairings of curve classes in `N¹(S)_ℚ` -/

/-- `[C] · [E] = C · E` (the intersection number of `C` with the prime Cartier divisor of `E`). -/
theorem curveClass_pairing_eq_intersectionNumber (C E : R.S.PrimeCurve) :
    R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg E) =
      (C.intersectionNumber (R.S.primeCurveCartier R.hreg E) : ℚ) := by
  rw [DisjointNegativeCurvesRank.curveClass_pairing R.S R.hreg,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg]

/-- `[C] · [C] = C²`. -/
theorem curveClass_self_pairing (C : R.S.PrimeCurve) :
    R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C) =
      (C.selfIntersectionNumber R.hreg : ℚ) :=
  curveClass_pairing_eq_intersectionNumber R C C

/-- `[D_i] · [D_j] = M_ij`. -/
theorem curveClass_pairing_vertices (i j : R.Vertices) :
    R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg j.val) = R.M i j :=
  DisjointNegativeCurvesRank.curveClass_pairing R.S R.hreg i.val j.val

/-- The intersection matrix of the exceptional curves is symmetric. -/
theorem M_symm (i j : R.Vertices) : R.M i j = R.M j i := by
  change (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) : ℚ) =
    (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg j.val)
      (R.S.primeCurveCartier R.hreg i.val) : ℚ)
  rw [R.S.intersectionPairing_symm R.hreg]

/-- `[P] · [D_i] = p_i`. -/
theorem curveClass_pairing_contact (P : R.S.PrimeCurve) (i : R.Vertices) :
    R.S.numericalIntersectionBilinForm R.hreg
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg P)
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val) = contactVector R P i :=
  curveClass_pairing_eq_intersectionNumber R P i.val

/-- `[L] · [C] = L · C`. -/
theorem Lnum_pairing_curveClass (C : R.S.PrimeCurve) :
    R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg C) = R.Ldeg C := by
  rw [DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg, R.numericalRestrictionDegree_Lnum]

/-! ### Degrees on exterior curves -/

/-- `L · C > 0` for every exterior prime curve: the pullback of an ample divisor has positive
degree on a curve which is not contracted. -/
theorem Ldeg_pos (C : R.S.PrimeCurve) (hC : ¬ IsExceptionalCurve R.π C) : 0 < R.Ldeg C := by
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  unfold ResolutionDatum.Ldeg
  rw [hL, map_smul, RationalWeilIntersection.degreeLinearMap_rationalCartier, smul_eq_mul]
  have hpos := AmplePullbackCurvePositive.intersectionNumber_pos R.π A hample C hC
  exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr hn)) (by exact_mod_cast hpos)

/-- `K_S · P = -1` for a `(-1)`-curve `P` (adjunction for a rational curve of square `-1`). -/
theorem Kdeg_eq_neg_one_of_isMinusOne (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    R.Kdeg P = -1 := by
  obtain ⟨e, he⟩ := hP.isoProjectiveLine
  have h := CompatibleRationalAdjunctionDegree.canonical_intersection_eq R.S R.hreg R.KS R.eKS
    P e he
  rw [hP.selfIntersection] at h
  unfold ResolutionDatum.Kdeg
  rw [h]
  norm_num

/-! ### The inverse of `A` -/

/-- `A` is invertible (positive definite over `ℚ`). -/
theorem A_det_isUnit [DecidableEq R.Vertices] : IsUnit R.A.det :=
  (Matrix.isUnit_iff_isUnit_det R.A).mp (KltDP.LinearAlgebra.isUnit_of_posDef R.A_posDef)

/-- `A (A⁻¹ x) = x`. -/
theorem A_mulVec_inv_mulVec [DecidableEq R.Vertices] (x : R.Vertices → ℚ) :
    R.A *ᵥ (R.A⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R.A (A_det_isUnit R), Matrix.one_mulVec]

/-- `A⁻¹ q = λ` (the manuscript's `pᵀ A⁻¹ q = pᵀ λ`). -/
theorem A_inv_mulVec_q [DecidableEq R.Vertices] : R.A⁻¹ *ᵥ R.q = R.lam := by
  rw [← R.A_mulVec_lam, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R.A (A_det_isUnit R),
    Matrix.one_mulVec]

/-! ### Manuscript Lemma 2.8 -/

/-- Manuscript Lemma 2.8 (`lem:projection`, lines 610–636), first identity (eq:green):
`pᵀ A⁻¹ p = 1 + (L·P)² / K_X²` for an exterior `(-1)`-curve `P`, with `K_X² = L²`.

The characteristic hypotheses `(p : ℕ) [CharP k p] (hp : 0 < p)` are those of the union's
Picard-rank theorem `IsMinimalResolution.picardRank_eq_of_klt`, which makes the exceptional
orthogonal one-dimensional. -/
theorem rankOneProjection_green [DecidableEq R.Vertices]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P) :
    dotProduct (contactVector R P) (R.A⁻¹ *ᵥ contactVector R P) =
      1 + (R.Ldeg P) ^ 2 / R.Lsq := by
  -- the coefficient vector `u = A⁻¹ p`, with `A u = p` and `M u = -p`
  obtain ⟨u, hu⟩ : ∃ u : R.Vertices → ℚ, u = R.A⁻¹ *ᵥ contactVector R P := ⟨_, rfl⟩
  rw [← hu]
  have hAu : R.A *ᵥ u = contactVector R P := by
    rw [hu]
    exact A_mulVec_inv_mulVec R (contactVector R P)
  have hMu : R.M *ᵥ u = -contactVector R P := by
    have hM : R.M = -R.A := by
      show R.M = -(-R.M)
      rw [neg_neg]
    rw [hM, Matrix.neg_mulVec, hAu]
  -- the projected class `P̄ = [P] + Σ u_i [D_i]`
  obtain ⟨Pbar, hPbar⟩ : ∃ Pbar : R.S.NumericalClassGroup,
      Pbar = DisjointNegativeCurvesRank.curveClass R.S R.hreg P +
        ∑ i : R.Vertices, u i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val :=
    ⟨_, rfl⟩
  -- (1) `P̄ · D_j = p_j + (M u)_j = 0`
  have hvertex : ∀ j : R.Vertices, R.S.numericalIntersectionBilinForm R.hreg Pbar
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg j.val) = 0 := by
    intro j
    rw [hPbar, LinearMap.BilinForm.add_left, LinearMap.BilinForm.sum_left,
      curveClass_pairing_contact R P j]
    have hsum : ∑ i : R.Vertices, R.S.numericalIntersectionBilinForm R.hreg
        (u i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val)
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg j.val) = (R.M *ᵥ u) j := by
      simp only [LinearMap.BilinForm.smul_left, curveClass_pairing_vertices, Matrix.mulVec,
        dotProduct]
      exact Finset.sum_congr rfl (fun i _ => by rw [M_symm R i j, mul_comm])
    rw [hsum, hMu, Pi.neg_apply, add_neg_cancel]
  -- (2) `P̄` lies in the exceptional orthogonal
  have hmem : Pbar ∈ ActualExceptionalNumerical.exceptionalOrthogonal R.π := by
    rw [ActualExceptionalNumerical.mem_exceptionalOrthogonal_iff]
    intro j
    rw [← DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg]
    exact hvertex j
  -- (3) the exceptional orthogonal is one-dimensional and contains `[L] ≠ 0`, so `P̄ = a [L]`
  have hLsq := R.Lsq_pos
  have hLne : R.Lnum ≠ 0 := by
    intro h
    have h0 : R.Lsq = 0 := by
      unfold ResolutionDatum.Lsq
      rw [h]
      simp
    exact absurd h0 (ne_of_gt hLsq)
  have hdim := R.hmin.finrank_exceptionalOrthogonal_eq_one_of_klt R.hklt p hp R.hrank
  have hLO : (⟨R.Lnum, R.Lnum_mem_exceptionalOrthogonal⟩ :
      ActualExceptionalNumerical.exceptionalOrthogonal R.π) ≠ 0 :=
    fun h => hLne (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (_root_.finrank_eq_one_iff_of_nonzero' _ hLO).mp hdim ⟨Pbar, hmem⟩
  have haL : a • R.Lnum = Pbar := congrArg Subtype.val ha
  -- (4) `L · P̄ = L · P` (since `L ⊥ D_i`)
  have hLP : R.S.numericalIntersectionBilinForm R.hreg R.Lnum Pbar = R.Ldeg P := by
    rw [hPbar, LinearMap.BilinForm.add_right, LinearMap.BilinForm.sum_right,
      Lnum_pairing_curveClass R P]
    simp only [LinearMap.BilinForm.smul_right, Lnum_pairing_curveClass R,
      ResolutionDatum.Ldeg_exceptional, mul_zero, Finset.sum_const_zero, add_zero]
  -- (5) `a L² = L · P`
  have ha_eq : a * R.Lsq = R.Ldeg P := by
    unfold ResolutionDatum.Lsq
    rw [← hLP, ← haL, LinearMap.BilinForm.smul_right]
  -- (6) `P̄² = a² L²`
  have hsq1 : R.S.numericalIntersectionBilinForm R.hreg Pbar Pbar = a * a * R.Lsq := by
    unfold ResolutionDatum.Lsq
    rw [← haL, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    ring
  -- (7) `P̄² = P̄ · P = -1 + pᵀ u`
  have hsq2 : R.S.numericalIntersectionBilinForm R.hreg Pbar Pbar =
      -1 + dotProduct (contactVector R P) u := by
    have hPP : R.S.numericalIntersectionBilinForm R.hreg Pbar
        (DisjointNegativeCurvesRank.curveClass R.S R.hreg P) =
        -1 + dotProduct (contactVector R P) u := by
      rw [hPbar, LinearMap.BilinForm.add_left, LinearMap.BilinForm.sum_left,
        curveClass_self_pairing R P, hP.1.selfIntersection]
      simp only [LinearMap.BilinForm.smul_left, dotProduct]
      push_cast
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg),
        curveClass_pairing_contact R P i, mul_comm]
    have hexp : R.S.numericalIntersectionBilinForm R.hreg Pbar Pbar =
        R.S.numericalIntersectionBilinForm R.hreg Pbar
          (DisjointNegativeCurvesRank.curveClass R.S R.hreg P +
            ∑ i : R.Vertices, u i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val) := by
      rw [← hPbar]
    rw [hexp, LinearMap.BilinForm.add_right, LinearMap.BilinForm.sum_right]
    simp only [LinearMap.BilinForm.smul_right, hvertex, mul_zero, Finset.sum_const_zero,
      add_zero]
    exact hPP
  -- (8) compare the two squares
  have hv : R.Lsq ≠ 0 := ne_of_gt hLsq
  have hg : dotProduct (contactVector R P) u = 1 + a * a * R.Lsq := by linarith
  have hkey : a * a * R.Lsq = R.Ldeg P ^ 2 / R.Lsq := by
    rw [eq_div_iff hv]
    calc a * a * R.Lsq * R.Lsq = (a * R.Lsq) * (a * R.Lsq) := by ring
      _ = R.Ldeg P ^ 2 := by rw [ha_eq]; ring
  rw [hg, hkey]

/-- Manuscript Lemma 2.8, the strict inequality in (eq:green): `pᵀ A⁻¹ p > 1`. -/
theorem rankOneProjection_green_gt_one [DecidableEq R.Vertices]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P) :
    1 < dotProduct (contactVector R P) (R.A⁻¹ *ᵥ contactVector R P) := by
  rw [rankOneProjection_green R p hp P hP]
  have hℓ := Ldeg_pos R P hP.2
  have hv := R.Lsq_pos
  have : 0 < R.Ldeg P ^ 2 / R.Lsq := div_pos (pow_pos hℓ 2) hv
  linarith

/-- Manuscript Lemma 2.8, second identity (eq:green-charge): `pᵀ λ = 1 − L·P`. -/
theorem rankOneProjection_charge (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P) :
    dotProduct (contactVector R P) R.lam = 1 - R.Ldeg P := by
  have h := R.Ldeg_eq_neg_Kdeg_sub P
  rw [Kdeg_eq_neg_one_of_isMinusOne R P hP.1] at h
  have hdot : dotProduct (contactVector R P) R.lam =
      ∑ i : R.Vertices, R.lam i *
        (P.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) := by
    simp only [dotProduct, contactVector]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hdot]
  push_cast at h
  linarith

/-- Manuscript Lemma 2.8, the strict inequality in (eq:green-charge): `pᵀ λ < 1`. -/
theorem rankOneProjection_charge_lt_one (P : R.S.PrimeCurve) (hP : R.IsExteriorMinusOne P) :
    dotProduct (contactVector R P) R.lam < 1 := by
  rw [rankOneProjection_charge R P hP]
  linarith [Ldeg_pos R P hP.2]

end KltDP.Manuscript.S02

#print axioms KltDP.Manuscript.S02.rankOneProjection_green
#print axioms KltDP.Manuscript.S02.rankOneProjection_green_gt_one
#print axioms KltDP.Manuscript.S02.rankOneProjection_charge
#print axioms KltDP.Manuscript.S02.rankOneProjection_charge_lt_one
#print axioms KltDP.Manuscript.S02.A_inv_mulVec_q
#print axioms KltDP.Manuscript.S02.Ldeg_pos
