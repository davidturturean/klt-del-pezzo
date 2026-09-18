import KltDP.Manuscript.Datum.AnticanonicalClass
import KltDP.Geometry.ExceptionalQCartierIntersection
import KltDP.Geometry.ActualExceptionalNumericalComplement
import KltDP.Geometry.AmplePullbackNef
import KltDP.Geometry.NullCurveNumericalSpan
import KltDP.Geometry.MinimalResolutionDiscrepancy
import KltDP.Geometry.PrimeCurveCartierVanishingIdeal
import KltDP.Geometry.RegularSurfaceWeilPicard
import KltDP.Geometry.NumericalEquivalence

/-!
# Degrees and numerical identities of the anticanonical pullback `L = π^*(-K_X)`

Manuscript `source/manuscript.tex`, Conventions (lines 302–316): for the resolution
datum `(S, D, L)` of a rank-one klt del Pezzo surface,
`K_S + Σ λ_i D_i = π^*K_X = -L`, with `0 ≤ λ_i < 1`, `A = -(D_i · D_j)`, `q_i = K_S · D_i`.

This module records, for `R : ResolutionDatum k`:

* the discrepancy divisor `Δ = K_S - π^*K_X` is supported on the exceptional curves
  (`Δ_exterior`) and equals `Σ_i (-λ_i) D_i` (`Δ_eq_sum`);
* `L · D_i = 0` (`Ldeg_exceptional`), `L` is nef (`Ldeg_nonneg`), and the manuscript's
  `L · C = -K_S · C - Σ λ_i (D_i · C)` (`Ldeg_eq_neg_Kdeg_sub`);
* the numerical class `[L]` has degree `L · C` on every prime curve
  (`numericalRestrictionDegree_Lnum`), lies in the exceptional orthogonal
  (`Lnum_mem_exceptionalOrthogonal`), has positive square (`Lsq_pos`), and satisfies
  `[L] = -([K_S] + Σ λ_i [D_i])` (`Lnum_eq`), `K_S · L = -L²` (`Knum_pairing_Lnum`),
  `L² = K_S² + q · λ` (`Lsq_eq_Ksq_add_dot`).

Everything is derived from the compiled union; no manuscript theorem is assumed.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Manuscript.ResolutionDatum

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### The discrepancy divisor is supported on the exceptional curves -/

/-- (a) `Δ` vanishes on every exterior prime curve: `Δ = K_S - π^*K_X` is supported on the
contracted primes (`MinimalResolutionDiscrepancy.difference_support_subset_exceptional`). -/
theorem Δ_exterior (C : R.S.PrimeCurve) (hC : ¬ IsExceptionalCurve R.π C) : R.Δ C = 0 := by
  have hsupport := MinimalResolutionDiscrepancy.difference_support_subset_exceptional
    R.π R.hbir R.KS R.KX R.KX_qCartier R.KS_push
  by_contra h
  exact hC (hsupport (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr h)))

/-- (b) `Δ = Σ_i (-λ_i) D_i` as rational Weil divisors (the manuscript's
`K_S + Σ λ_i D_i = π^*K_X`). -/
theorem Δ_eq_sum : R.Δ = ∑ i : R.Vertices, (-R.lam i) • Finsupp.single i.val (1 : ℚ) := by
  classical
  ext C
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hC : IsExceptionalCurve R.π C
  · rw [Finset.sum_eq_single (⟨C, hC⟩ : R.Vertices)]
    · simp [lam]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [R.Δ_exterior C hC]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro h
    exact hC (h ▸ j.property)

/-! ### Auxiliary identifications between the divisor route and the numerical classes -/

/-- The rational Weil divisor of the prime Cartier divisor of `E` is `E` itself. -/
theorem rationalCartierToWeilHom_primeCurveCartier (E : R.S.PrimeCurve) :
    R.S.rationalCartierToWeilHom (R.S.primeCurveCartier R.hreg E) =
      Finsupp.single E (1 : ℚ) := by
  change rationalizeWeilDivisor R.S (R.S.cartierToWeilHom (R.S.primeCurveCartier R.hreg E)) = _
  rw [R.S.cartierToWeilHom_primeCurveCartier R.hreg E, rationalizeWeilDivisor_single, Int.cast_one]

/-- The degree of a single prime curve `E` against `C` is the intersection number `C · E`. -/
theorem degreeLinearMap_single (C E : R.S.PrimeCurve) :
    RationalWeilIntersection.degreeLinearMap R.S R.hreg C (Finsupp.single E (1 : ℚ)) =
      (C.intersectionNumber (R.S.primeCurveCartier R.hreg E) : ℚ) := by
  simp only [RationalWeilIntersection.degreeLinearMap, Finsupp.linearCombination_single, one_smul]

/-- The numerical class of an actual Cartier divisor computed through the divisor route
(`rationalWeilNumericalMap`) is its `cartierClass` (Picard route). -/
theorem rationalWeilNumericalMap_rationalCartier (D : CartierDivisor R.S.toScheme) :
    R.S.rationalWeilNumericalMap R.hreg (R.S.rationalCartierToWeilHom D) =
      NefNullCurveNegativeSquare.cartierClass R.S D := by
  have h : R.S.regularWeilPicardClass R.hreg (R.S.cartierToWeilHom D) =
      cartierPicardClass R.S.toScheme D :=
    R.S.regularWeilClassPicardEquiv_of_cartier R.hreg D
  change R.S.rationalWeilNumericalMap R.hreg (rationalizeWeilDivisor R.S (R.S.cartierToWeilHom D)) = _
  rw [← R.S.picardNumericalMap_regularWeilPicardClass R.hreg, h]
  rfl

/-- The numerical class of the prime curve `E` through the divisor route is `curveClass`. -/
theorem rationalWeilNumericalMap_single (E : R.S.PrimeCurve) :
    R.S.rationalWeilNumericalMap R.hreg (Finsupp.single E (1 : ℚ)) =
      DisjointNegativeCurvesRank.curveClass R.S R.hreg E := by
  rw [← R.rationalCartierToWeilHom_primeCurveCartier E, R.rationalWeilNumericalMap_rationalCartier]
  rfl

/-- The numerical degree of the class of a rational Weil divisor is its rational degree. -/
theorem numericalRestrictionDegree_rationalWeilNumericalMap (C : R.S.PrimeCurve)
    (D : R.S.RationalWeilDivisor) :
    R.S.numericalRestrictionDegree C (R.S.rationalWeilNumericalMap R.hreg D) =
      RationalWeilIntersection.degreeLinearMap R.S R.hreg C D := by
  have key : (R.S.numericalRestrictionDegree C).comp (R.S.rationalWeilNumericalMap R.hreg) =
      RationalWeilIntersection.degreeLinearMap R.S R.hreg C := by
    apply Finsupp.lhom_ext'
    intro E
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [R.degreeLinearMap_single C E, R.rationalWeilNumericalMap_single E,
      ← DisjointNegativeCurvesRank.pairing_curveClass R.S R.hreg,
      DisjointNegativeCurvesRank.curveClass_pairing, R.S.intersectionPairing_primeCurve R.hreg]
  exact LinearMap.congr_fun key D

/-- `L` written with an actual ample Cartier numerator: `L = (1/n) π^*A` for an ample Cartier
divisor `A` on `X` with `A = n (-K_X)` as rational Weil divisors (from `R.KX_qAmple`). -/
theorem exists_ample_numerator :
    ∃ n : ℕ, 0 < n ∧ ∃ A : CartierDivisor R.X.toScheme,
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf R.X.toScheme A) ∧
      R.Lweil = (n : ℚ)⁻¹ •
        R.S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom R.π A) := by
  obtain ⟨n, hn, A, hA, hample⟩ := R.KX_qAmple
  refine ⟨n, hn, A, hample, ?_⟩
  let D : R.X.rationalCartierSubmodule := ⟨rationalizeWeilDivisor R.X R.KX, R.KX_qCartier⟩
  have hA' : R.X.rationalCartierToWeilHom A =
      n • ((-D : R.X.rationalCartierSubmodule) : R.X.RationalWeilDivisor) := by
    rw [Submodule.coe_neg]
    exact hA
  have h := QCartierPullback.pullbackToWeil_eq_of_positive_multiple R.π (-D) n hn A hA'
  rw [map_neg] at h
  exact h

/-! ### Degrees of `L` -/

/-- (c) `L · D_i = 0` for every exceptional curve (a `ℚ`-Cartier pullback has degree zero on
contracted curves). -/
theorem Ldeg_exceptional (i : R.Vertices) : R.Ldeg i.val = 0 := by
  unfold Ldeg Lweil pullbackKX
  rw [map_neg, RationalWeilIntersection.degreeLinearMap_pullback_eq_zero R.hreg R.π
    R.hmin.over_base (rationalizeWeilDivisor R.X R.KX) R.KX_qCartier i.val i.property, neg_zero]

/-- (d) `L` is nef: `L · C ≥ 0` on every prime curve (pullback of an ample divisor). -/
theorem Ldeg_nonneg (C : R.S.PrimeCurve) : 0 ≤ R.Ldeg C := by
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  unfold Ldeg
  rw [hL, map_smul, RationalWeilIntersection.degreeLinearMap_rationalCartier, smul_eq_mul]
  have hnef := AmplePullbackNef.isNef_signedCartier_pullback R.π A hample
  rw [Positivity.isNef_iff_forall_primeCurve] at hnef
  have hC : 0 ≤ C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) := hnef C
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (by exact_mod_cast hC)

/-- (e) `L · C = -K_S · C - Σ_i λ_i (D_i · C)`: the manuscript's `K_S + Σ λ_i D_i = -L`
evaluated on a prime curve `C`. -/
theorem Ldeg_eq_neg_Kdeg_sub (C : R.S.PrimeCurve) :
    R.Ldeg C = -(R.Kdeg C : ℚ) -
      ∑ i : R.Vertices, R.lam i * (C.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) := by
  have h := R.Kdeg_add_Ldeg C
  rw [R.Δ_eq_sum, map_sum] at h
  simp only [map_smul, smul_eq_mul, R.degreeLinearMap_single, neg_mul,
    Finset.sum_neg_distrib] at h
  linarith

/-! ### The numerical class of `L` -/

/-- (f) The numerical degree of `[L]` on `C` is `L · C`. -/
theorem numericalRestrictionDegree_Lnum (C : R.S.PrimeCurve) :
    R.S.numericalRestrictionDegree C R.Lnum = R.Ldeg C :=
  R.numericalRestrictionDegree_rationalWeilNumericalMap C R.Lweil

/-- (g) `[L]` is orthogonal to every exceptional curve. -/
theorem Lnum_mem_exceptionalOrthogonal :
    R.Lnum ∈ ActualExceptionalNumerical.exceptionalOrthogonal R.π := by
  rw [ActualExceptionalNumerical.mem_exceptionalOrthogonal_iff]
  intro i
  rw [R.numericalRestrictionDegree_Lnum, R.Ldeg_exceptional i]

/-- (h) `L² > 0` (positive square of the pullback of an ample divisor under the proper
birational map `π`). -/
theorem Lsq_pos : 0 < R.Lsq := by
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  have hLnum : R.Lnum = (n : ℚ)⁻¹ • NefNullCurveNegativeSquare.cartierClass R.S
      (DominantCartierPullback.pullbackHom R.π A) := by
    unfold Lnum
    rw [hL, map_smul, R.rationalWeilNumericalMap_rationalCartier]
  unfold Lsq
  rw [hLnum, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    NefNullCurveNegativeSquare.cartierClass_pairing]
  have hpos := BirationalAmplePullbackPositiveSquare.intersectionPairing_signedPullback_pos
    R.π R.hbir R.hreg A hample
  have hn' : (0 : ℚ) < (n : ℚ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
  exact mul_pos hn' (mul_pos hn' (by exact_mod_cast hpos))

/-- (i) `[L] = -([K_S] + Σ_i λ_i [D_i])` in `N¹(S)_ℚ`. -/
theorem Lnum_eq :
    R.Lnum = -(R.Knum + ∑ i : R.Vertices,
      R.lam i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val) := by
  have hL : R.Lweil = R.Δ - R.S.rationalCartierToWeilHom R.KS := by
    rw [← R.KS_add_Lweil]
    abel
  unfold Lnum
  rw [hL, map_sub, R.Δ_eq_sum, map_sum, R.rationalWeilNumericalMap_rationalCartier]
  simp only [map_smul, map_neg, R.rationalWeilNumericalMap_single, neg_smul,
    Finset.sum_neg_distrib]
  rw [show R.Knum = NefNullCurveNegativeSquare.cartierClass R.S R.KS from rfl]
  abel

/-- (j) `K_S · L = -L²`. -/
theorem Knum_pairing_Lnum :
    R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Lnum = -R.Lsq := by
  have hK : R.Knum = -R.Lnum - ∑ i : R.Vertices,
      R.lam i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val := by
    rw [R.Lnum_eq]
    abel
  have hzero : ∀ i : R.Vertices, R.S.numericalIntersectionBilinForm R.hreg
      (R.lam i • DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val) R.Lnum = 0 := by
    intro i
    rw [LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg),
      DisjointNegativeCurvesRank.pairing_curveClass, R.numericalRestrictionDegree_Lnum,
      R.Ldeg_exceptional i, mul_zero]
  unfold Lsq
  conv_lhs => rw [hK]
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.neg_left, LinearMap.BilinForm.sum_left,
    Finset.sum_eq_zero (fun i _ => hzero i), sub_zero]

/-- `K_S · D_i = q_i` for every exceptional curve (from (c), (e) and `A λ = q`). -/
theorem Kdeg_exceptional (i : R.Vertices) : (R.Kdeg i.val : ℚ) = R.q i := by
  have h1 := R.Ldeg_eq_neg_Kdeg_sub i.val
  rw [R.Ldeg_exceptional i] at h1
  have h2 := congrFun R.A_mulVec_lam i
  have h3 : (R.A *ᵥ R.lam) i = -∑ j : R.Vertices,
      R.lam j * ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℚ) := by
    rw [show R.A = -R.M from rfl, Matrix.neg_mulVec, Pi.neg_apply, neg_inj]
    simp only [Matrix.mulVec, dotProduct, M, NullCurveIntersectionMatrix.intersectionMatrix]
    apply Finset.sum_congr rfl
    intro j _
    rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg, mul_comm]
  rw [h3] at h2
  linarith

/-- `[K_S] · [D_i] = q_i`. -/
theorem Knum_pairing_curveClass (i : R.Vertices) :
    R.S.numericalIntersectionBilinForm R.hreg R.Knum
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg i.val) = R.q i := by
  rw [← R.Kdeg_exceptional i]
  exact NullCurveNumericalSpan.cartierClass_curveClass R.S R.hreg R.KS i.val

/-- (k) `L² = K_S² + q · λ` (the manuscript's `L² = K_S² + 2 λᵀq - λᵀAλ = K_S² + λᵀq`).
`dotProduct` is the root-namespace dot product (`Matrix.dotProduct` is its deprecated alias). -/
theorem Lsq_eq_Ksq_add_dot : R.Lsq = R.Ksq + dotProduct R.q R.lam := by
  have hj := R.Knum_pairing_Lnum
  rw [R.Lnum_eq, LinearMap.BilinForm.neg_right, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.sum_right] at hj
  simp only [LinearMap.BilinForm.smul_right, R.Knum_pairing_curveClass] at hj
  have hdot : dotProduct R.q R.lam = ∑ i : R.Vertices, R.lam i * R.q i := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hdot]
  change R.Lsq = R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Knum + _
  linarith

end KltDP.Manuscript.ResolutionDatum

#print axioms KltDP.Manuscript.ResolutionDatum.Δ_exterior
#print axioms KltDP.Manuscript.ResolutionDatum.Δ_eq_sum
#print axioms KltDP.Manuscript.ResolutionDatum.Ldeg_exceptional
#print axioms KltDP.Manuscript.ResolutionDatum.Ldeg_nonneg
#print axioms KltDP.Manuscript.ResolutionDatum.Ldeg_eq_neg_Kdeg_sub
#print axioms KltDP.Manuscript.ResolutionDatum.numericalRestrictionDegree_Lnum
#print axioms KltDP.Manuscript.ResolutionDatum.Lnum_mem_exceptionalOrthogonal
#print axioms KltDP.Manuscript.ResolutionDatum.Lsq_pos
#print axioms KltDP.Manuscript.ResolutionDatum.Lnum_eq
#print axioms KltDP.Manuscript.ResolutionDatum.Knum_pairing_Lnum
#print axioms KltDP.Manuscript.ResolutionDatum.Kdeg_exceptional
#print axioms KltDP.Manuscript.ResolutionDatum.Lsq_eq_Ksq_add_dot
