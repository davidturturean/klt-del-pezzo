import KltDP.Manuscript.Datum.AnticanonicalDegrees
import KltDP.Manuscript.S07.AdjointConfiguration
import KltDP.Manuscript.S03.NefThresholdCore
import KltDP.Manuscript.S03.NefThresholdArithmetic
import KltDP.Manuscript.S02.Projection
import KltDP.Manuscript.S02.ExteriorNullCurves
import KltDP.Manuscript.S02.SquareDegree
import KltDP.Geometry.NefSelfIntersectionNonnegative
import KltDP.Geometry.RiemannRochEffectiveMultiple
import KltDP.Geometry.NefIntersectionSectionVanishing
import KltDP.Geometry.AmplePullbackNef
import KltDP.Geometry.BirationalAmplePullbackPositiveSquare
import KltDP.Geometry.SurfaceNumericalFinitenessProved

/-!
# Manuscript Lemma 3.3: the least exterior degree is the nef anticanonical threshold

Source: `source/manuscript.tex`, lines 754–823, label `lem:nef-threshold`.

For the resolution datum `(S, D, L)` of a rank-one klt del Pezzo surface with `ρ(S) > 2`:

* `exists_exteriorMinusOne` (a): exterior `(-1)`-curves exist. `K_S · L = -L² < 0`, so a
  positive multiple of the nef and big pullback `π^*A` of an ample divisor is effective
  (Riemann–Roch, `RiemannRochEffectiveMultiple.exists_positive_effective_multiple`) and has
  negative `K_S`-degree; one of its components `C` has `K_S · C < 0`; Tanaka's contraction
  theorem (`NefThresholdCore`, `exists_minusOneCurve_of_not_nef`) yields a `(-1)`-curve, which
  is exterior because the resolution is minimal.
* `exists_shortestExteriorMinusOne` (b): a shortest exterior `(-1)`-curve exists: `n L` is the
  Cartier divisor `π^*A`, so the degrees `n (L · Q)` are positive integers.
* `thresholdClass_nef` (c): `N = L + ℓ K_S` is nef for `ℓ = L · P`, `P` shortest
  (`NefThresholdCore.nef_of_minusOne_nonneg` applied to the Cartier divisor `π^*A` and `n ℓ`).
* `thresholdClass_not_nef_of_gt` (d): `L + t K_S` is negative on `P` for `t > ℓ`.
* `exterior_degree_bound` (e): `L · C ≥ ℓ (-K_S · C) ≥ ℓ` for every exterior prime curve
  (`eq:least-degree-canonical-bound`).
* `effective_small_degree_supported_on_exceptional` (f): an effective divisor of `L`-degree
  `< ℓ` is supported on the exceptional curves, hence has `L`-degree zero
  (`effective_small_degree_Ldeg_eq_zero`).
* `thresholdClass_square_nonneg` (g): `N² ≥ 0`: `n N` is the class of the actual Cartier divisor
  `π^*A + (P · π^*A) K_S`, which is nef by (c), and a nef Cartier divisor on a regular surface has
  nonnegative square (`NefSelfIntersectionNonnegative.intersection_nonneg_of_isCanonical`).

The identities `N · D_i = ℓ (b_i - 2)` and `N² = (1 - 2ℓ) L² + ℓ² K_S²` are
`KltDP.Manuscript.S03.thresholdClass_degree_exceptional` and `thresholdClass_square`
(`NefThresholdArithmetic`).

All objects are the actual union objects; nothing is assumed beyond the datum and `ρ(S) > 2`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript

universe u

namespace KltDP.Manuscript.S03

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### Every `(-1)`-curve of the minimal resolution is exterior -/

/-- Manuscript line 801: "It is exterior because no component of the minimal exceptional divisor
has square `-1`" (the minimality clause of `IsMinimalResolution`). -/
theorem isExterior_of_isMinusOne (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    ¬ IsExceptionalCurve R.π P :=
  fun hex => R.hmin.no_minusOne_curve P hex hP

theorem isExteriorMinusOne_of_isMinusOne (P : R.S.PrimeCurve) (hP : IsMinusOneCurve R.hreg P) :
    R.IsExteriorMinusOne P :=
  ⟨hP, isExterior_of_isMinusOne R P hP⟩

/-! ### The ample numerator `π^*A = n L` -/

/-- `n (L · C) = C · π^*A` for the ample numerator `A` with `L = (1/n) π^*A`. -/
theorem Ldeg_mul_eq_intersectionNumber (n : ℕ) (A : CartierDivisor R.X.toScheme)
    (hL : R.Lweil = (n : ℚ)⁻¹ •
      R.S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom R.π A))
    (hn : 0 < n) (C : R.S.PrimeCurve) :
    (n : ℚ) * R.Ldeg C = (C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) : ℚ) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold ResolutionDatum.Ldeg
  rw [hL, map_smul, RationalWeilIntersection.degreeLinearMap_rationalCartier, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hn', one_mul]

/-- `[π^*A] = n [L]` in `N¹(S)_ℚ`. -/
theorem cartierClass_pullback_eq (n : ℕ) (A : CartierDivisor R.X.toScheme)
    (hL : R.Lweil = (n : ℚ)⁻¹ •
      R.S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom R.π A))
    (hn : 0 < n) :
    NefNullCurveNegativeSquare.cartierClass R.S (DominantCartierPullback.pullbackHom R.π A) =
      (n : ℚ) • R.Lnum := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold ResolutionDatum.Lnum
  rw [hL, map_smul, R.rationalWeilNumericalMap_rationalCartier, smul_smul, mul_inv_cancel₀ hn',
    one_smul]

/-- `π^*A` is nef: nonnegative degree on every prime curve. -/
theorem intersectionNumber_pullback_nonneg (A : CartierDivisor R.X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf R.X.toScheme A)) (C : R.S.PrimeCurve) :
    0 ≤ C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) := by
  have hnef := AmplePullbackNef.isNef_signedCartier_pullback R.π A hA
  rw [Positivity.isNef_iff_forall_primeCurve] at hnef
  exact hnef C

/-- `π^*A · K_S = n (L · K_S) = -n L² < 0` (manuscript line 803: `K_S · L = -L² < 0`). -/
theorem intersectionPairing_pullback_KS_neg (n : ℕ) (A : CartierDivisor R.X.toScheme)
    (hL : R.Lweil = (n : ℚ)⁻¹ •
      R.S.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom R.π A))
    (hn : 0 < n) :
    R.S.intersectionPairing R.hreg (DominantCartierPullback.pullbackHom R.π A) R.KS < 0 := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h := NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg
    (DominantCartierPullback.pullbackHom R.π A) R.KS
  rw [cartierClass_pullback_eq R n A hL hn, LinearMap.BilinForm.smul_left] at h
  have hLK : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S R.KS) = -R.Lsq := by
    rw [← R.Knum_pairing_Lnum]
    exact (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq R.Lnum R.Knum
  rw [hLK] at h
  have hneg : ((R.S.intersectionPairing R.hreg (DominantCartierPullback.pullbackHom R.π A) R.KS :
      ℤ) : ℚ) < 0 := by
    rw [← h]
    exact mul_neg_of_pos_of_neg hn' (by linarith [R.Lsq_pos])
  exact_mod_cast hneg

/-! ### (a) Exterior `(-1)`-curves exist -/

/-- `K_S` is not nef: some prime curve has `K_S · C < 0`. A positive multiple of `π^*A` (nef, with
positive square) is linearly equivalent to an effective divisor `Z` by Riemann–Roch; since
`π^*A · K_S < 0`, some component of `Z` is `K_S`-negative. -/
theorem exists_KS_negative_curve : ∃ C : R.S.PrimeCurve, C.intersectionNumber R.KS < 0 := by
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  have hDD : 0 < R.S.intersectionPairing R.hreg (DominantCartierPullback.pullbackHom R.π A)
      (DominantCartierPullback.pullbackHom R.π A) :=
    BirationalAmplePullbackPositiveSquare.intersectionPairing_signedPullback_pos R.π R.hbir R.hreg
      A hample
  have hDnef : Positivity.IsNef R.S.structureMorphism
      (cartierDivisorInvertibleSheaf R.S.toScheme (DominantCartierPullback.pullbackHom R.π A)) :=
    AmplePullbackNef.isNef_signedCartier_pullback R.π A hample
  have hDK := intersectionPairing_pullback_KS_neg R n A hL hn
  obtain ⟨m, hm, Z, hZ, hZD⟩ :=
    RiemannRochEffectiveMultiple.exists_positive_effective_multiple R.S R.hreg
      (SmoothCanonicalCartierRepresentative.weilRepresentative R.S)
      (SurfaceRiemannRochSource.constructedCanonical_isCanonical R.S)
      (DominantCartierPullback.pullbackHom R.π A) (DominantCartierPullback.pullbackHom R.π A)
      hDnef hDD hDD
  have hZK : R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm Z) R.KS
      < 0 := by
    rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent R.S R.hreg R.KS hZD,
      RiemannRochEffectiveMultiple.inverse_toWeil,
      RiemannRochEffectiveMultiple.intersection_nsmul_left]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hm) hDK
  have hZmap : R.S.cartierToWeilHom ((R.S.regularCartierWeilEquiv R.hreg).symm Z) = Z :=
    (R.S.regularCartierWeilEquiv R.hreg).apply_symm_apply Z
  rw [R.S.intersectionPairing_eq_weil_sum_right R.hreg, hZmap] at hZK
  by_contra hall
  push_neg at hall
  have hnonneg : 0 ≤ Z.sum fun C a => a * C.intersectionNumber R.KS := by
    unfold Finsupp.sum
    apply Finset.sum_nonneg
    intro C _
    exact mul_nonneg (hZ C) (hall C)
  exact absurd hZK (not_lt.mpr hnonneg)

/-- Manuscript Lemma 3.3 (a), lines 793–805: exterior `(-1)`-curves exist when `ρ(S) > 2`. -/
theorem exists_exteriorMinusOne (hrho : 2 < R.S.picardRank) :
    ∃ P : R.S.PrimeCurve, R.IsExteriorMinusOne P := by
  haveI : FiniteDimensional ℚ R.S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite R.S R.hreg
  obtain ⟨E, hE⟩ := exists_minusOneCurve_of_not_nef R.S R.hreg R.KS R.eKS hrho
    (exists_KS_negative_curve R)
  exact ⟨E, isExteriorMinusOne_of_isMinusOne R E hE⟩

/-! ### (b) A shortest exterior `(-1)`-curve exists -/

/-- Manuscript Lemma 3.3 (b), lines 763–765 and 806–807: "A Cartier multiple of `L` makes the
positive degrees of all exterior `(-1)`-curves discrete, so their minimum `ℓ > 0` exists." -/
theorem exists_shortestExteriorMinusOne (hrho : 2 < R.S.picardRank) :
    ∃ P : R.S.PrimeCurve, R.IsShortestExteriorMinusOne P := by
  classical
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hdeg := Ldeg_mul_eq_intersectionNumber R n A hL hn
  obtain ⟨Q₀, hQ₀⟩ := exists_exteriorMinusOne R hrho
  have hpos : ∀ Q : R.S.PrimeCurve, R.IsExteriorMinusOne Q →
      0 < Q.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) :=
    fun Q hQ => AmplePullbackCurvePositive.intersectionNumber_pos R.π A hample Q hQ.2
  have hex : ∃ m : ℕ, ∃ Q : R.S.PrimeCurve, R.IsExteriorMinusOne Q ∧
      Q.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) = (m : ℤ) :=
    ⟨(Q₀.intersectionNumber (DominantCartierPullback.pullbackHom R.π A)).toNat, Q₀, hQ₀,
      (Int.toNat_of_nonneg (hpos Q₀ hQ₀).le).symm⟩
  obtain ⟨P, hP, hPm⟩ := Nat.find_spec hex
  refine ⟨P, hP, fun Q hQ => ?_⟩
  have hQpos := hpos Q hQ
  have hmin : Nat.find hex ≤ (Q.intersectionNumber (DominantCartierPullback.pullbackHom R.π A)).toNat :=
    Nat.find_min' hex ⟨Q, hQ, (Int.toNat_of_nonneg hQpos.le).symm⟩
  have hPQ : P.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) ≤
      Q.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) := by
    rw [hPm, ← Int.toNat_of_nonneg hQpos.le]
    exact_mod_cast hmin
  have hPQ' : (n : ℚ) * R.Ldeg P ≤ (n : ℚ) * R.Ldeg Q := by
    rw [hdeg P, hdeg Q]
    exact_mod_cast hPQ
  exact le_of_mul_le_mul_left hPQ' hn'

/-! ### (c) `N = L + ℓ K_S` is nef -/

/-- Manuscript Lemma 3.3 (c), lines 808–811: `N = L + ℓ K_S` is nef for the least exterior degree
`ℓ = L · P`. Applied to the Cartier divisor `π^*A = n L` and `n ℓ`: for every `(-1)`-curve `E`
(exterior by minimality) `(π^*A + nℓ K_S) · E = n (L · E - ℓ) ≥ 0`. -/
theorem thresholdClass_nef (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve)
    (hP : R.IsShortestExteriorMinusOne P) :
    ∀ C : R.S.PrimeCurve, 0 ≤ R.S.numericalRestrictionDegree C (thresholdClass R (R.Ldeg P)) := by
  haveI : FiniteDimensional ℚ R.S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite R.S R.hreg
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hdeg := Ldeg_mul_eq_intersectionNumber R n A hL hn
  have hclass := cartierClass_pullback_eq R n A hL hn
  have hnef : ∀ C : R.S.PrimeCurve,
      0 ≤ C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) :=
    intersectionNumber_pullback_nonneg R A hample
  have hℓ : 0 ≤ (n : ℚ) * R.Ldeg P := mul_nonneg hn'.le (R.Ldeg_nonneg P)
  have hE : ∀ E : R.S.PrimeCurve, IsMinusOneCurve R.hreg E →
      0 ≤ R.S.numericalRestrictionDegree E
        (NefNullCurveNegativeSquare.cartierClass R.S (DominantCartierPullback.pullbackHom R.π A) +
          ((n : ℚ) * R.Ldeg P) • NefNullCurveNegativeSquare.cartierClass R.S R.KS) := by
    intro E hE
    have hle : R.Ldeg P ≤ R.Ldeg E := hP.2 E (isExteriorMinusOne_of_isMinusOne R E hE)
    rw [map_add, map_smul, KltDP.Manuscript.S02.numericalRestrictionDegree_cartierClass R.S R.hreg,
      smul_eq_mul]
    have hK : R.S.numericalRestrictionDegree E (NefNullCurveNegativeSquare.cartierClass R.S R.KS) =
        (R.Kdeg E : ℚ) :=
      numericalRestrictionDegree_Knum R E
    rw [hK, KltDP.Manuscript.S02.Kdeg_eq_neg_one_of_isMinusOne R E hE, ← hdeg E]
    have := mul_le_mul_of_nonneg_left hle hn'.le
    push_cast
    linarith
  have hmain := nef_of_minusOne_nonneg R.S R.hreg R.KS R.eKS hrho
    (DominantCartierPullback.pullbackHom R.π A) hnef ((n : ℚ) * R.Ldeg P) hℓ hE
  intro C
  have hC := hmain C
  have heq : NefNullCurveNegativeSquare.cartierClass R.S (DominantCartierPullback.pullbackHom R.π A) +
      ((n : ℚ) * R.Ldeg P) • NefNullCurveNegativeSquare.cartierClass R.S R.KS =
      (n : ℚ) • thresholdClass R (R.Ldeg P) := by
    rw [hclass, thresholdClass, smul_add, smul_smul]
    rfl
  rw [heq, map_smul, smul_eq_mul] at hC
  exact (mul_nonneg_iff_of_pos_left hn').mp hC

/-! ### (d) Sharpness of the threshold -/

/-- Manuscript Lemma 3.3 (d), lines 812–813: for `t > ℓ`, `L + t K_S` is negative on a curve
attaining the minimum (`K_S · P = -1`). -/
theorem thresholdClass_not_nef_of_gt (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
    (t : ℚ) (ht : R.Ldeg P < t) :
    R.S.numericalRestrictionDegree P (thresholdClass R t) < 0 := by
  rw [thresholdClass_degree, KltDP.Manuscript.S02.Kdeg_eq_neg_one_of_isMinusOne R P hP.1.1]
  push_cast
  linarith

/-! ### (e) The degree bound on exterior curves -/

/-- Manuscript Lemma 3.3 (e), `eq:least-degree-canonical-bound` (lines 776–779, 814–818):
`L · C ≥ ℓ (-K_S · C)` and `-K_S · C ≥ 1` for every exterior prime curve `C`. -/
theorem exterior_degree_bound (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve)
    (hP : R.IsShortestExteriorMinusOne P) (C : R.S.PrimeCurve)
    (hC : ¬ IsExceptionalCurve R.π C) :
    R.Ldeg P * (-(R.Kdeg C : ℚ)) ≤ R.Ldeg C ∧ (1 : ℤ) ≤ -R.Kdeg C := by
  have h := thresholdClass_nef R hrho P hP C
  rw [thresholdClass_degree] at h
  have hK := KltDP.Manuscript.S02.Kdeg_neg_of_not_exceptional R C hC
  exact ⟨by linarith, by omega⟩

/-- `L · C ≥ ℓ` for every exterior prime curve `C`. -/
theorem Ldeg_ge_of_not_exceptional (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve)
    (hP : R.IsShortestExteriorMinusOne P) (C : R.S.PrimeCurve)
    (hC : ¬ IsExceptionalCurve R.π C) : R.Ldeg P ≤ R.Ldeg C := by
  obtain ⟨hb, hK⟩ := exterior_degree_bound R hrho P hP C hC
  have hℓ : 0 < R.Ldeg P := KltDP.Manuscript.S02.Ldeg_pos R P hP.1.2
  have hK' : (1 : ℚ) ≤ -(R.Kdeg C : ℚ) := by exact_mod_cast hK
  exact le_trans (le_mul_of_one_le_right hℓ.le hK') hb

/-! ### (f) Effective divisors of small `L`-degree -/

/-- Manuscript Lemma 3.3 (f), lines 780–782 and 818–819: an effective divisor of `L`-degree less
than `ℓ` is supported on the exceptional curves. -/
theorem effective_small_degree_supported_on_exceptional (hrho : 2 < R.S.picardRank)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P) (N : R.S.WeilDivisor)
    (hN : ∀ C, 0 ≤ N C) (hdeg : N.sum (fun C a => (a : ℚ) * R.Ldeg C) < R.Ldeg P) :
    ∀ C : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π C → N C = 0 := by
  intro C hC
  by_contra hne
  have hpos : 0 < N C := lt_of_le_of_ne (hN C) (Ne.symm hne)
  have h1 : (1 : ℚ) ≤ (N C : ℚ) := by exact_mod_cast hpos
  have hLC : R.Ldeg P ≤ R.Ldeg C := Ldeg_ge_of_not_exceptional R hrho P hP C hC
  have hterm : (N C : ℚ) * R.Ldeg C ≤ N.sum (fun C' a => (a : ℚ) * R.Ldeg C') := by
    unfold Finsupp.sum
    exact Finset.single_le_sum (f := fun C' => (N C' : ℚ) * R.Ldeg C')
      (fun C' _ => mul_nonneg (by exact_mod_cast hN C') (R.Ldeg_nonneg C'))
      (Finsupp.mem_support_iff.mpr hne)
  have hmul : R.Ldeg C ≤ (N C : ℚ) * R.Ldeg C := le_mul_of_one_le_left (R.Ldeg_nonneg C) h1
  linarith

/-- Manuscript Lemma 3.3 (f), second clause: such a divisor has `L`-degree zero. -/
theorem effective_small_degree_Ldeg_eq_zero (hrho : 2 < R.S.picardRank)
    (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P) (N : R.S.WeilDivisor)
    (hN : ∀ C, 0 ≤ N C) (hdeg : N.sum (fun C a => (a : ℚ) * R.Ldeg C) < R.Ldeg P) :
    N.sum (fun C a => (a : ℚ) * R.Ldeg C) = 0 := by
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro C _
  by_cases hex : IsExceptionalCurve R.π C
  · change (N C : ℚ) * R.Ldeg C = 0
    rw [show R.Ldeg C = 0 from R.Ldeg_exceptional ⟨C, hex⟩, mul_zero]
  · change (N C : ℚ) * R.Ldeg C = 0
    rw [effective_small_degree_supported_on_exceptional R hrho P hP N hN hdeg C hex]
    simp

/-! ### (g) The threshold class has nonnegative square -/

/-- Manuscript Lemma 3.3 (g), lines 784–786 and 820–822: `N² ≥ 0`. The class `n N` is the class of
the actual Cartier divisor `π^*A + (P · π^*A) K_S`, nef by (c); a nef Cartier divisor on the regular
surface `S` has nonnegative self-intersection. -/
theorem thresholdClass_square_nonneg (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve)
    (hP : R.IsShortestExteriorMinusOne P) :
    0 ≤ R.S.numericalIntersectionBilinForm R.hreg (thresholdClass R (R.Ldeg P))
      (thresholdClass R (R.Ldeg P)) := by
  obtain ⟨n, hn, A, hample, hL⟩ := R.exists_ample_numerator
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hdeg := Ldeg_mul_eq_intersectionNumber R n A hL hn
  have hclass := cartierClass_pullback_eq R n A hL hn
  -- the integer `a = P · π^*A = n ℓ`
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = P.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) :=
    ⟨_, rfl⟩
  -- the Cartier divisor `π^*A + a K_S` has class `n N`
  have hNclass : NefNullCurveNegativeSquare.cartierClass R.S
      (DominantCartierPullback.pullbackHom R.π A + a • R.KS) =
      (n : ℚ) • thresholdClass R (R.Ldeg P) := by
    have h1 : NefNullCurveNegativeSquare.cartierClass R.S
        (DominantCartierPullback.pullbackHom R.π A + a • R.KS) =
        NefNullCurveNegativeSquare.cartierClass R.S (DominantCartierPullback.pullbackHom R.π A) +
          a • NefNullCurveNegativeSquare.cartierClass R.S R.KS := by
      show R.S.picardNumericalMap (cartierPicardHom R.S.toScheme
        (DominantCartierPullback.pullbackHom R.π A + a • R.KS)) = _
      rw [map_add, map_zsmul, map_add, map_zsmul]
      rfl
    rw [h1, hclass, ← Int.cast_smul_eq_zsmul ℚ a, thresholdClass, smul_add, smul_smul, ha,
      ← hdeg P]
    rfl
  -- it is nef by (c)
  have hNnef : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme
      (DominantCartierPullback.pullbackHom R.π A + a • R.KS)) := by
    rw [Positivity.isNef_iff_forall_primeCurve]
    intro C
    rw [← C.intersectionNumber_eq_restrictionDegree]
    have h1 := thresholdClass_nef R hrho P hP C
    have h2 := KltDP.Manuscript.S02.numericalRestrictionDegree_cartierClass R.S R.hreg C
      (DominantCartierPullback.pullbackHom R.π A + a • R.KS)
    rw [hNclass, map_smul, smul_eq_mul] at h2
    have h3 : (0 : ℚ) ≤
        (C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A + a • R.KS) : ℚ) := by
      rw [← h2]
      exact mul_nonneg hn'.le h1
    exact_mod_cast h3
  -- a nef Cartier divisor has nonnegative square
  have hsq : 0 ≤ R.S.intersectionPairing R.hreg
      (DominantCartierPullback.pullbackHom R.π A + a • R.KS)
      (DominantCartierPullback.pullbackHom R.π A + a • R.KS) :=
    NefSelfIntersectionNonnegative.intersection_nonneg_of_isCanonical R.S R.hreg
      (SmoothCanonicalCartierRepresentative.weilRepresentative R.S)
      (SurfaceRiemannRochSource.constructedCanonical_isCanonical R.S) _ hNnef
  have hsq' : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg
      (NefNullCurveNegativeSquare.cartierClass R.S
        (DominantCartierPullback.pullbackHom R.π A + a • R.KS))
      (NefNullCurveNegativeSquare.cartierClass R.S
        (DominantCartierPullback.pullbackHom R.π A + a • R.KS)) := by
    rw [NefNullCurveNegativeSquare.cartierClass_pairing]
    exact_mod_cast hsq
  rw [hNclass, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at hsq'
  exact (mul_nonneg_iff_of_pos_left hn').mp ((mul_nonneg_iff_of_pos_left hn').mp hsq')

end KltDP.Manuscript.S03

#print axioms KltDP.Manuscript.S03.isExterior_of_isMinusOne
#print axioms KltDP.Manuscript.S03.exists_KS_negative_curve
#print axioms KltDP.Manuscript.S03.exists_exteriorMinusOne
#print axioms KltDP.Manuscript.S03.exists_shortestExteriorMinusOne
#print axioms KltDP.Manuscript.S03.thresholdClass_nef
#print axioms KltDP.Manuscript.S03.thresholdClass_not_nef_of_gt
#print axioms KltDP.Manuscript.S03.exterior_degree_bound
#print axioms KltDP.Manuscript.S03.effective_small_degree_supported_on_exceptional
#print axioms KltDP.Manuscript.S03.effective_small_degree_Ldeg_eq_zero
#print axioms KltDP.Manuscript.S03.thresholdClass_square_nonneg
