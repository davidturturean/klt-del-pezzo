import KltDP.Manuscript.S02.ExteriorNullCurves
import KltDP.Manuscript.S02.SquareDegree
import KltDP.Manuscript.S03.NefThresholdArithmetic
import KltDP.Manuscript.S04.DiscrepancyLemmas
import KltDP.Manuscript.S05.PicardIndex
import KltDP.Geometry.SurfaceRiemannRochNef
import KltDP.Geometry.NumericalHodgeConsequences
import KltDP.Geometry.KltResolutionNoetherRelation
import KltDP.Geometry.KltResolutionPicardRank
import KltDP.Geometry.KltResolutionPicardCohomologyInvariants
import KltDP.Geometry.RiemannRochEffectiveMultiple
import KltDP.Geometry.NullCurveNumericalSpan
import KltDP.Geometry.CurveConeExtremal

/-!
# Manuscript Lemma 6.3: the adjacent-contact adjoint

Source: `source/manuscript.tex`, lines 1720–1780, label `lem:adjacent-contact-adjoint`.

The first part of this file is the shared Weil-divisor infrastructure of §6 (numerical and
Picard classes of integral Weil divisors on the resolution surface `S`, degrees against prime
curves, the `L`-degree, the Riemann–Roch effective representative of an adjoint divisor
`K_S + A` for a nef `A` of positive square, and the Hodge-index uniqueness of an effective
`A`-null representative). The second part is Lemma 6.3 itself.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.DisjointNegativeCurvesRank KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Manuscript KltDP.Manuscript.S02 KltDP.Manuscript.S04

universe u

namespace KltDP.Manuscript.S06Adj

variable {k : Type u} [Field k] [IsAlgClosed k] (R : ResolutionDatum k)

/-! ### Numerical classes of integral Weil divisors -/

/-- The numerical class of an integral Weil divisor on `S` (divisor route). -/
def numW : R.S.WeilDivisor →+ R.S.NumericalClassGroup :=
  (R.S.rationalWeilNumericalMap R.hreg).toAddMonoidHom.comp (rationalizeWeilDivisor R.S)

theorem numW_apply (N : R.S.WeilDivisor) :
    numW R N = R.S.rationalWeilNumericalMap R.hreg (rationalizeWeilDivisor R.S N) := rfl

theorem numW_single (C : R.S.PrimeCurve) (a : ℤ) :
    numW R (Finsupp.single C a) = (a : ℚ) • curveClass R.S R.hreg C := by
  rw [numW_apply, rationalizeWeilDivisor_single, ← R.rationalWeilNumericalMap_single C,
    ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem numW_eq_sum (N : R.S.WeilDivisor) :
    numW R N = ∑ C ∈ N.support, (N C : ℚ) • curveClass R.S R.hreg C := by
  conv_lhs => rw [← Finsupp.sum_single N, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl (fun C _ => numW_single R C (N C))

/-- The degree `Q · N` of an integral Weil divisor against a prime curve. -/
def degW (Q : R.S.PrimeCurve) (N : R.S.WeilDivisor) : ℚ :=
  R.S.numericalRestrictionDegree Q (numW R N)

theorem degW_eq_pairing (Q : R.S.PrimeCurve) (N : R.S.WeilDivisor) :
    degW R Q N = R.S.numericalIntersectionBilinForm R.hreg (curveClass R.S R.hreg Q) (numW R N) := by
  rw [degW, LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg),
    pairing_curveClass]

theorem degW_eq_sum (Q : R.S.PrimeCurve) (N : R.S.WeilDivisor) :
    degW R Q N = ∑ C ∈ N.support,
      (N C : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C) : ℚ) := by
  rw [degW, numW_apply, R.numericalRestrictionDegree_rationalWeilNumericalMap,
    RationalWeilIntersection.degreeLinearMap_apply, rationalizeWeilDivisor_componentSupport]
  rfl

theorem degW_single (Q C : R.S.PrimeCurve) (a : ℤ) :
    degW R Q (Finsupp.single C a) =
      (a : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C) : ℚ) := by
  rw [degW, numW_single, map_smul, smul_eq_mul, numericalRestrictionDegree_curveClass]

theorem degW_add (Q : R.S.PrimeCurve) (N N' : R.S.WeilDivisor) :
    degW R Q (N + N') = degW R Q N + degW R Q N' := by
  simp only [degW, map_add]

theorem degW_sub (Q : R.S.PrimeCurve) (N N' : R.S.WeilDivisor) :
    degW R Q (N - N') = degW R Q N - degW R Q N' := by
  simp only [degW, map_sub]

theorem degW_zero (Q : R.S.PrimeCurve) : degW R Q 0 = 0 := by
  simp only [degW, map_zero]

/-- Distinct prime curves have nonnegative intersection number. -/
theorem inter_nonneg (Q C : R.S.PrimeCurve) (h : Q ≠ C) :
    0 ≤ (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C) : ℚ) := by
  have h1 := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg Q C h
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at h1
  exact_mod_cast h1

/-- Distinct disjoint prime curves have intersection number zero. -/
theorem inter_eq_zero_of_disjoint (Q C : R.S.PrimeCurve) (h : Q ≠ C)
    (hd : Disjoint (Q : Set R.S.toScheme) (C : Set R.S.toScheme)) :
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C) : ℚ) = 0 := by
  have h1 := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg Q C h).mpr hd
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at h1
  exact_mod_cast h1

/-- Distinct prime curves with intersection number zero are disjoint. -/
theorem disjoint_of_inter_eq_zero (Q C : R.S.PrimeCurve) (h : Q ≠ C)
    (h0 : (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C) : ℚ) = 0) :
    Disjoint (Q : Set R.S.toScheme) (C : Set R.S.toScheme) := by
  refine (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg Q C h).mp ?_
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]
  exact_mod_cast h0

/-- The degree of an effective divisor against a prime curve not in its support is
nonnegative. -/
theorem degW_nonneg_of_coeff_eq_zero (Q : R.S.PrimeCurve) (N : R.S.WeilDivisor)
    (hN : EffectiveDivisor N) (hQ : N Q = 0) : 0 ≤ degW R Q N := by
  rw [degW_eq_sum]
  refine Finset.sum_nonneg (fun C hC => ?_)
  have hne : Q ≠ C := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hC) hQ
  exact mul_nonneg (by exact_mod_cast hN C) (inter_nonneg R Q C hne)

/-- The pairing of two integral Weil divisors, expanded along the components of the second. -/
theorem pairing_numW_eq_sum (A Z : R.S.WeilDivisor) :
    R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R Z) =
      ∑ C ∈ Z.support, (Z C : ℚ) * degW R C A := by
  conv_lhs => rw [numW_eq_sum R Z]
  rw [LinearMap.BilinForm.sum_right]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [LinearMap.BilinForm.smul_right, degW_eq_pairing]
  congr 1
  exact LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg) _ _

/-! ### The `L`-degree of an integral Weil divisor -/

/-- The `L`-degree `L · N = Σ a_C (L · C)` of an integral Weil divisor `N = Σ a_C C`. -/
def LdegW (N : R.S.WeilDivisor) : ℚ := N.sum fun C a => (a : ℚ) * R.Ldeg C

theorem LdegW_eq_sum (N : R.S.WeilDivisor) :
    LdegW R N = ∑ C ∈ N.support, (N C : ℚ) * R.Ldeg C := rfl

theorem LdegW_eq_pairing (N : R.S.WeilDivisor) :
    LdegW R N = R.S.numericalIntersectionBilinForm R.hreg R.Lnum (numW R N) := by
  rw [LdegW_eq_sum, numW_eq_sum, LinearMap.BilinForm.sum_right]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [LinearMap.BilinForm.smul_right, Lnum_pairing_curveClass]

theorem LdegW_nonneg (N : R.S.WeilDivisor) (hN : EffectiveDivisor N) : 0 ≤ LdegW R N := by
  rw [LdegW_eq_sum]
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (by exact_mod_cast hN C) (R.Ldeg_nonneg C))

/-- A single term of the `L`-degree of an effective divisor is at most the `L`-degree. -/
theorem coeff_mul_Ldeg_le_LdegW (N : R.S.WeilDivisor) (hN : EffectiveDivisor N)
    (Q : R.S.PrimeCurve) : (N Q : ℚ) * R.Ldeg Q ≤ LdegW R N := by
  rw [LdegW_eq_sum]
  by_cases hQ : Q ∈ N.support
  · exact Finset.single_le_sum
      (fun C _ => mul_nonneg (by exact_mod_cast hN C) (R.Ldeg_nonneg C)) hQ
  · rw [Finsupp.not_mem_support_iff.mp hQ, Int.cast_zero, zero_mul]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (by exact_mod_cast hN C) (R.Ldeg_nonneg C))

/-! ### Picard classes of integral Weil divisors -/

theorem picW_single (C : R.S.PrimeCurve) :
    R.S.regularWeilPicardClass R.hreg (Finsupp.single C 1) = R.curvePic C := by
  rw [← R.S.cartierToWeilHom_primeCurveCartier R.hreg C]
  exact R.S.regularWeilClassPicardEquiv_of_cartier R.hreg _

theorem picW_KS :
    R.S.regularWeilPicardClass R.hreg (R.S.cartierToWeilHom R.KS) =
      cartierPicardClass R.S.toScheme R.KS :=
  R.S.regularWeilClassPicardEquiv_of_cartier R.hreg _

theorem picW_eq_of_linearlyEquivalent {N N' : R.S.WeilDivisor} (h : R.S.LinearlyEquivalent N N') :
    R.S.regularWeilPicardClass R.hreg N = R.S.regularWeilPicardClass R.hreg N' :=
  (R.S.regularWeilPicardClass_eq_iff R.hreg N N').mpr h

theorem linearlyEquivalent_of_picW_eq {N N' : R.S.WeilDivisor}
    (h : R.S.regularWeilPicardClass R.hreg N = R.S.regularWeilPicardClass R.hreg N') :
    R.S.LinearlyEquivalent N N' :=
  (R.S.regularWeilPicardClass_eq_iff R.hreg N N').mp h

theorem numW_eq_picardNumericalMap (N : R.S.WeilDivisor) :
    numW R N = R.S.picardNumericalMap (Additive.ofMul (R.S.regularWeilPicardClass R.hreg N)) :=
  (R.S.picardNumericalMap_regularWeilPicardClass R.hreg N).symm

/-- Linearly equivalent integral Weil divisors have the same numerical class. -/
theorem numW_eq_of_linearlyEquivalent {N N' : R.S.WeilDivisor}
    (h : R.S.LinearlyEquivalent N N') : numW R N = numW R N' := by
  rw [numW_eq_picardNumericalMap, numW_eq_picardNumericalMap, picW_eq_of_linearlyEquivalent R h]

theorem linearlyEquivalent_iff_weilClassMap (N N' : R.S.WeilDivisor) :
    R.S.LinearlyEquivalent N N' ↔ R.S.weilClassMap N = R.S.weilClassMap N' :=
  R.S.linearlyEquivalent_iff_weilClassMap_eq N N'

/-! ### The Cartier divisor of an integral Weil divisor and nefness -/

theorem cartierClass_symm (N : R.S.WeilDivisor) :
    NefNullCurveNegativeSquare.cartierClass R.S ((R.S.regularCartierWeilEquiv R.hreg).symm N) =
      numW R N := by
  rw [← R.rationalWeilNumericalMap_rationalCartier, numW_apply]
  congr 1
  change rationalizeWeilDivisor R.S
    (R.S.regularCartierWeilEquiv R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm N)) = _
  rw [AddEquiv.apply_symm_apply]

theorem intersectionPairing_symm_symm (N N' : R.S.WeilDivisor) :
    (R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm N)
      ((R.S.regularCartierWeilEquiv R.hreg).symm N') : ℚ) =
      R.S.numericalIntersectionBilinForm R.hreg (numW R N) (numW R N') := by
  rw [← NefNullCurveNegativeSquare.cartierClass_pairing R.S R.hreg, cartierClass_symm,
    cartierClass_symm]

theorem intersectionNumber_symm_eq_degW (Q : R.S.PrimeCurve) (N : R.S.WeilDivisor) :
    (Q.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm N) : ℚ) = degW R Q N := by
  rw [degW, ← cartierClass_symm, numericalRestrictionDegree_cartierClass R.S R.hreg]

/-- A Weil divisor with nonnegative degree on every prime curve gives a nef Cartier divisor. -/
theorem isNef_symm (N : R.S.WeilDivisor) (h : ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q N) :
    Positivity.IsNef R.S.structureMorphism
      (cartierDivisorInvertibleSheaf R.S.toScheme ((R.S.regularCartierWeilEquiv R.hreg).symm N)) := by
  refine (R.S.isNef_iff_pairing R.hreg _).mpr (fun Q => ?_)
  have hQ := h Q
  rw [← intersectionNumber_symm_eq_degW R Q N] at hQ
  have hQ' : 0 ≤ Q.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm N) := by
    exact_mod_cast hQ
  rw [R.S.intersectionPairing_primeCurve R.hreg]
  exact hQ'

/-! ### The canonical divisor as a Weil divisor and Riemann–Roch -/

theorem symm_KS : (R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS) = R.KS :=
  (R.S.regularCartierWeilEquiv R.hreg).symm_apply_apply R.KS

theorem numW_KS : numW R (R.S.cartierToWeilHom R.KS) = R.Knum := by
  rw [← cartierClass_symm, symm_KS]
  rfl

theorem isCanonical_KS : IsCanonical R.S R.hreg (R.S.cartierToWeilHom R.KS) := by
  unfold IsCanonical divisorModule
  rw [symm_KS]
  exact R.KS_canonical

/-- `p_a(S) = 0`: `χ(O_S) = 1` for the resolution of a rank-one klt del Pezzo surface. -/
theorem arithmeticGenus_eq_zero (p : ℕ) [CharP k p] (hp : 0 < p) : arithmeticGenus R.S = 0 := by
  have h := (R.hmin.picard_and_structure_invariants_of_kltDelPezzo R.hDP R.hrank p hp).2.2.1
  unfold arithmeticGenus
  rw [h]
  norm_num

/-- The Riemann–Roch number of the adjoint divisor `K_S + A`: `χ(K_S + A) = 1 + (K_S + A)·A / 2`. -/
theorem rrNumber_adjoint (p : ℕ) [CharP k p] (hp : 0 < p) (A : R.S.WeilDivisor) :
    rrNumber R.S R.hreg (R.S.cartierToWeilHom R.KS + A) (R.S.cartierToWeilHom R.KS) =
      R.S.numericalIntersectionBilinForm R.hreg (R.Knum + numW R A) (numW R A) / 2 + 1 := by
  unfold rrNumber
  rw [arithmeticGenus_eq_zero R p hp, add_sub_cancel_left, intersectionPairing_symm_symm, map_add,
    numW_KS]
  simp

/-- **Riemann–Roch for adjoint divisors** (manuscript lines 1591–1598 / 1755–1758 / 1848–1851):
for a nef integral Weil divisor `A` with `A² > 0` and `χ(K_S + A) > 0`, the adjoint class
`K_S + A` contains an effective divisor. -/
theorem exists_effective_adjoint (p : ℕ) [CharP k p] (hp : 0 < p) (A : R.S.WeilDivisor)
    (hnef : ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q A)
    (hsq : 0 < R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R A))
    (hrr : 0 < R.S.numericalIntersectionBilinForm R.hreg (R.Knum + numW R A) (numW R A) / 2 + 1) :
    ∃ Z : R.S.WeilDivisor, EffectiveDivisor Z ∧
      R.S.LinearlyEquivalent Z (R.S.cartierToWeilHom R.KS + A) := by
  refine SurfaceRiemannRochNef.exists_effectiveWeil R.S R.hreg (R.S.cartierToWeilHom R.KS + A)
    (R.S.cartierToWeilHom R.KS) ((R.S.regularCartierWeilEquiv R.hreg).symm A) (isCanonical_KS R)
    (isNef_symm R A hnef) ?_ ?_
  · have h1 := intersectionPairing_symm_symm R (R.S.cartierToWeilHom R.KS) A
    have h2 := intersectionPairing_symm_symm R (R.S.cartierToWeilHom R.KS + A) A
    rw [numW_KS] at h1
    rw [map_add (numW R), numW_KS, LinearMap.BilinForm.add_left] at h2
    have h3 : (R.S.intersectionPairing R.hreg
        ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS))
        ((R.S.regularCartierWeilEquiv R.hreg).symm A) : ℚ) <
        (R.S.intersectionPairing R.hreg
        ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS + A))
        ((R.S.regularCartierWeilEquiv R.hreg).symm A) : ℚ) := by
      rw [h1, h2]
      linarith
    exact_mod_cast h3
  · rw [rrNumber_adjoint R p hp A]
    exact hrr

/-! ### Components of an effective divisor null for a nef class -/

/-- If `A` is nef and `A · Z = 0` for an effective `Z`, every component of `Z` is `A`-null. -/
theorem degW_eq_zero_of_component (A Z : R.S.WeilDivisor)
    (hnef : ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q A) (hZ : EffectiveDivisor Z)
    (h0 : R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R Z) = 0)
    (Q : R.S.PrimeCurve) (hQ : Z Q ≠ 0) : degW R Q A = 0 := by
  rw [pairing_numW_eq_sum] at h0
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun C _ => mul_nonneg (by exact_mod_cast hZ C) (hnef C))).mp h0 Q
    (Finsupp.mem_support_iff.mpr hQ)
  have hQ' : (Z Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  exact (mul_eq_zero.mp hterm).resolve_left hQ'

/-! ### Effective numerically trivial divisors vanish -/

/-- The pairing of the class of a Cartier divisor with an integral Weil divisor. -/
theorem pairing_cartierClass_numW (D : CartierDivisor R.S.toScheme) (N : R.S.WeilDivisor) :
    R.S.numericalIntersectionBilinForm R.hreg (NefNullCurveNegativeSquare.cartierClass R.S D)
      (numW R N) = ∑ C ∈ N.support, (N C : ℚ) * (C.intersectionNumber D : ℚ) := by
  rw [numW_eq_sum, LinearMap.BilinForm.sum_right]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  rw [LinearMap.BilinForm.smul_right, NullCurveNumericalSpan.cartierClass_curveClass]

/-- An effective integral Weil divisor with numerical class zero is zero. -/
theorem eq_zero_of_effective_of_numW_eq_zero (N : R.S.WeilDivisor) (hN : EffectiveDivisor N)
    (h : numW R N = 0) : N = 0 := by
  classical
  obtain ⟨Hd, hH⟩ := R.S.exists_isAmple_cartier
  by_contra hne
  have hsupp : N.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  have hpos : 0 < ∑ C ∈ N.support, (N C : ℚ) * (C.intersectionNumber Hd : ℚ) := by
    refine Finset.sum_pos (fun C hC => ?_) hsupp
    have h1 : 0 < N C := lt_of_le_of_ne (hN C) (Ne.symm (Finsupp.mem_support_iff.mp hC))
    have h2 := CurveCone.intersectionNumber_pos_of_isAmple R.S Hd hH C
    exact mul_pos (by exact_mod_cast h1) (by exact_mod_cast h2)
  rw [← pairing_cartierClass_numW, h, map_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### Hodge-index uniqueness of effective null representatives -/

/-- **Hodge uniqueness** (manuscript lines 1763–1766, 1863–1867): two effective integral Weil
divisors with the same numerical class, all of whose components are null for a class `G` of
positive square, coincide. -/
theorem eq_of_effective_of_null (G : R.S.NumericalClassGroup)
    (hG : 0 < R.S.numericalIntersectionBilinForm R.hreg G G)
    (N₁ N₂ : R.S.WeilDivisor) (h₁ : EffectiveDivisor N₁) (h₂ : EffectiveDivisor N₂)
    (hnull₁ : ∀ Q : R.S.PrimeCurve, N₁ Q ≠ 0 → R.S.numericalRestrictionDegree Q G = 0)
    (heq : numW R N₁ = numW R N₂) : N₁ = N₂ := by
  classical
  -- the common part and the two remainders
  set m : R.S.WeilDivisor := N₁ ⊓ N₂ with hm
  set M₁ : R.S.WeilDivisor := N₁ - m with hM₁
  set M₂ : R.S.WeilDivisor := N₂ - m with hM₂
  have hmQ : ∀ Q, m Q = min (N₁ Q) (N₂ Q) := fun Q => by
    rw [hm, Finsupp.inf_apply]
  have hM₁Q : ∀ Q, M₁ Q = N₁ Q - min (N₁ Q) (N₂ Q) := fun Q => by
    rw [hM₁, Finsupp.sub_apply, hmQ]
  have hM₂Q : ∀ Q, M₂ Q = N₂ Q - min (N₁ Q) (N₂ Q) := fun Q => by
    rw [hM₂, Finsupp.sub_apply, hmQ]
  have hM₁eff : EffectiveDivisor M₁ := fun Q => by
    rw [hM₁Q]
    exact sub_nonneg.mpr (min_le_left _ _)
  have hM₂eff : EffectiveDivisor M₂ := fun Q => by
    rw [hM₂Q]
    exact sub_nonneg.mpr (min_le_right _ _)
  have hdisj : ∀ Q, M₁ Q ≠ 0 → M₂ Q = 0 := fun Q hQ => by
    rw [hM₁Q] at hQ
    rw [hM₂Q]
    have : min (N₁ Q) (N₂ Q) = N₂ Q := by
      rcases min_choice (N₁ Q) (N₂ Q) with h | h
      · exact absurd (by rw [h]; ring) hQ
      · exact h
    rw [this, sub_self]
  have hsub₁ : ∀ Q, M₁ Q ≠ 0 → N₁ Q ≠ 0 := fun Q hQ hN => by
    apply hQ
    rw [hM₁Q, hN]
    have := h₂ Q
    rw [min_eq_left this, sub_self]
  have hsub₂ : ∀ Q, M₂ Q ≠ 0 → N₂ Q ≠ 0 := fun Q hQ hN => by
    apply hQ
    rw [hM₂Q, hN]
    have := h₁ Q
    rw [min_eq_right this, sub_self]
  have heqM : numW R M₁ = numW R M₂ := by
    rw [hM₁, hM₂, map_sub, map_sub, heq]
  -- `M₁ · M₂ ≥ 0` since the remainders have no common component
  have hM₁M₂ : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg (numW R M₂) (numW R M₁) := by
    rw [pairing_numW_eq_sum]
    refine Finset.sum_nonneg (fun Q hQ => ?_)
    have hQ' := Finsupp.mem_support_iff.mp hQ
    exact mul_nonneg (by exact_mod_cast hM₁eff Q)
      (degW_nonneg_of_coeff_eq_zero R Q M₂ hM₂eff (hdisj Q hQ'))
  have hsq : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg (numW R M₁) (numW R M₁) := by
    rw [heqM] at hM₁M₂ ⊢
    exact hM₁M₂
  -- `G · M₁ = 0`
  have hperp : R.S.numericalIntersectionBilinForm R.hreg G (numW R M₁) = 0 := by
    rw [numW_eq_sum, LinearMap.BilinForm.sum_right]
    refine Finset.sum_eq_zero (fun Q hQ => ?_)
    rw [LinearMap.BilinForm.smul_right, pairing_curveClass,
      hnull₁ Q (hsub₁ Q (Finsupp.mem_support_iff.mp hQ)), mul_zero]
  have hzero := NumericalHodgeConsequences.eq_zero_of_nonneg_square_of_orthogonal R.S R.hreg G
    (numW R M₁) hG hperp hsq
  have hM₁0 : M₁ = 0 := eq_zero_of_effective_of_numW_eq_zero R M₁ hM₁eff hzero
  have hM₂0 : M₂ = 0 := eq_zero_of_effective_of_numW_eq_zero R M₂ hM₂eff (heqM ▸ hzero)
  have e₁ : N₁ = m := sub_eq_zero.mp hM₁0
  have e₂ : N₂ = m := sub_eq_zero.mp hM₂0
  rw [e₁, e₂]

/-! ### Divisors supported on the exceptional locus -/

/-- `D_i · D_i = -b_i`. -/
theorem M_diag (i : R.Vertices) : R.M i i = -R.w i := by
  simp [ResolutionDatum.w]

/-- Distinct non-adjacent exceptional curves have zero intersection number. -/
theorem M_eq_zero_of_not_adj {i j : R.Vertices} (hne : i ≠ j) (h : ¬ R.graph.Adj i j) :
    R.M i j = 0 := by
  have hne' : i.val ≠ j.val := fun h' => hne (Subtype.ext h')
  have hd := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg i.val j.val hne').mpr (KltDP.Manuscript.S05.disjoint_of_not_adj R hne h)
  change (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg j.val) : ℚ) = 0
  rw [hd, Int.cast_zero]

/-- Adjacent exceptional curves have intersection number one (the exceptional configuration
is a forest of transversally meeting curves). -/
theorem M_eq_one_of_adj {i j : R.Vertices} (h : R.graph.Adj i j) : R.M i j = 1 := by
  have hne : i ≠ j := h.ne
  have hne' : i.val ≠ j.val := fun h' => hne (Subtype.ext h')
  obtain ⟨_, _, _, hpair⟩ := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  have hle := hpair i j hne
  have hnn := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg
    i.val j.val hne'
  have hne0 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) ≠ 0 := by
    intro h0
    have hd := (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
      R.S R.hreg i.val j.val hne').mp h0
    obtain ⟨_, hn⟩ := h
    exact Set.not_disjoint_iff_nonempty_inter.mpr hn hd
  have h1 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) = 1 := by omega
  change (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg j.val) : ℚ) = 1
  rw [h1, Int.cast_one]

/-- The intersection number of two exceptional curves is `M i j`. -/
theorem inter_vertices (i j : R.Vertices) :
    ((i.val).intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℚ) = R.M i j := by
  change _ = (R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
    (R.S.primeCurveCartier R.hreg j.val) : ℚ)
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber]

/-- The numerical class of a divisor supported on the exceptional curves, as a vertex
combination. -/
theorem numW_eq_sum_vertices (Z : R.S.WeilDivisor)
    (hexc : ∀ Q : R.S.PrimeCurve, Z Q ≠ 0 → IsExceptionalCurve R.π Q) :
    numW R Z = ∑ i : R.Vertices, (Z i.val : ℚ) • curveClass R.S R.hreg i.val := by
  classical
  rw [numW_eq_sum]
  have hsupp : Z.support = (Finset.univ.filter fun i : R.Vertices => Z i.val ≠ 0).image
      Subtype.val := by
    ext Q
    simp only [Finsupp.mem_support_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hQ
      exact ⟨⟨Q, hexc Q hQ⟩, hQ, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact hi
  rw [hsupp, Finset.sum_image (fun i _ j _ h => Subtype.ext h), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : Z i.val ≠ 0
  · rw [if_pos hi]
  · rw [if_neg hi]
    push_neg at hi
    rw [hi, Int.cast_zero, zero_smul]

/-- The square of a vertex combination is `-cᵀ A c`. -/
theorem square_sum_vertices (c : R.Vertices → ℚ) :
    R.S.numericalIntersectionBilinForm R.hreg
      (∑ i : R.Vertices, c i • curveClass R.S R.hreg i.val)
      (∑ i : R.Vertices, c i • curveClass R.S R.hreg i.val) = -dotProduct c (R.A *ᵥ c) := by
  have h := NullCurveIntersectionMatrix.quadraticForm_eq R.S R.hreg (fun i : R.Vertices => i.val) c
  rw [← h]
  have hA : R.A = -R.M := rfl
  rw [hA, Matrix.neg_mulVec, dotProduct_neg, neg_neg]
  rfl

/-- **Negative definiteness of the exceptional locus**: an integral Weil divisor supported on
the exceptional curves with nonnegative square is zero. -/
theorem eq_zero_of_exceptional_of_square_nonneg (Z : R.S.WeilDivisor)
    (hexc : ∀ Q : R.S.PrimeCurve, Z Q ≠ 0 → IsExceptionalCurve R.π Q)
    (hsq : 0 ≤ R.S.numericalIntersectionBilinForm R.hreg (numW R Z) (numW R Z)) : Z = 0 := by
  classical
  set c : R.Vertices → ℚ := fun i => (Z i.val : ℚ) with hc
  have hnum : numW R Z = ∑ i : R.Vertices, c i • curveClass R.S R.hreg i.val :=
    numW_eq_sum_vertices R Z hexc
  rw [hnum, square_sum_vertices] at hsq
  have hc0 : c = 0 := by
    by_contra hne
    have hpos := R.A_posDef.2 c hne
    rw [star_trivial] at hpos
    linarith
  ext Q
  by_contra hQ
  have hQ' : Z Q ≠ 0 := by simpa using hQ
  have := congr_fun hc0 ⟨Q, hexc Q hQ'⟩
  simp only [hc, Pi.zero_apply, Int.cast_eq_zero] at this
  exact hQ' this


/-! ### Symmetry of intersection numbers of prime curves -/

theorem inter_comm (Q Q' : R.S.PrimeCurve) :
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg Q') : ℚ) =
      (Q'.intersectionNumber (R.S.primeCurveCartier R.hreg Q) : ℚ) := by
  rw [← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg
    Q Q', ← PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S
    R.hreg Q' Q, R.S.intersectionPairing_symm R.hreg]

/-- `[K_S] · [X] = K_S · X` for every prime curve `X`. -/
theorem Knum_pairing_cc (X : R.S.PrimeCurve) :
    R.S.numericalIntersectionBilinForm R.hreg R.Knum (curveClass R.S R.hreg X) = (R.Kdeg X : ℚ) := by
  rw [pairing_curveClass, KltDP.Manuscript.S03.numericalRestrictionDegree_Knum]

/-- The exterior contact numbers of a non-exceptional prime curve are nonnegative (rational form). -/
theorem contact_cast_nonneg (Q : R.S.PrimeCurve) (hQ : ¬ IsExceptionalCurve R.π Q) (i : R.Vertices) :
    0 ≤ (Q.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℚ) := by
  exact_mod_cast contact_nonneg_of_not_exceptional R Q hQ i

/-! ## Lemma 6.3: the adjacent-contact configuration -/

section Adjacent

variable (P : R.S.PrimeCurve) (C H : R.Vertices)

/-- The divisor `a C + h H + q P` supported on the adjacent-contact configuration. -/
def adjDiv (a h q : ℤ) : R.S.WeilDivisor :=
  Finsupp.single C.val a + Finsupp.single H.val h + Finsupp.single P q

theorem numW_adjDiv (a h q : ℤ) :
    numW R (adjDiv R P C H a h q) = (a : ℚ) • curveClass R.S R.hreg C.val +
      (h : ℚ) • curveClass R.S R.hreg H.val + (q : ℚ) • curveClass R.S R.hreg P := by
  simp only [adjDiv, map_add, numW_single]

theorem degW_adjDiv (a h q : ℤ) (Q : R.S.PrimeCurve) :
    degW R Q (adjDiv R P C H a h q) =
      (a : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) +
      (h : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) +
      (q : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
  simp only [adjDiv, degW_add, degW_single]

theorem square_adjDiv (a h q : ℤ) :
    R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
      (numW R (adjDiv R P C H a h q)) =
      (a : ℚ) * degW R C.val (adjDiv R P C H a h q) + (h : ℚ) * degW R H.val (adjDiv R P C H a h q) +
        (q : ℚ) * degW R P (adjDiv R P C H a h q) := by
  nth_rewrite 1 [numW_adjDiv]
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left, ← degW_eq_pairing,
    ← degW_eq_pairing, ← degW_eq_pairing]

theorem Knum_pairing_adjDiv (hP : R.IsExteriorMinusOne P) (a h q : ℤ) :
    R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R (adjDiv R P C H a h q)) =
      (a : ℚ) * (R.w C - 2) + (h : ℚ) * (R.w H - 2) - q := by
  rw [numW_adjDiv]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, Knum_pairing_cc,
    R.Kdeg_exceptional, Kdeg_eq_neg_one_of_isMinusOne R P hP.1, ResolutionDatum.q]
  push_cast
  ring

theorem Lnum_pairing_adjDiv (a h q : ℤ) :
    R.S.numericalIntersectionBilinForm R.hreg R.Lnum (numW R (adjDiv R P C H a h q)) =
      (q : ℚ) * R.Ldeg P := by
  rw [numW_adjDiv]
  simp only [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, Lnum_pairing_curveClass,
    R.Ldeg_exceptional]
  ring

variable (hP : R.IsExteriorMinusOne P) (hCH : C ≠ H) (hwH : R.w H = 2) (hadj : R.graph.Adj C H)
  (hPC : R.contact P C = 1) (hPH : R.contact P H = 1)

/-! ### The intersection table -/

include hP in
theorem iPP : (P.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = -1 := by
  have h : P.intersectionNumber (R.S.primeCurveCartier R.hreg P) = -1 := hP.1.selfIntersection
  rw [h]
  push_cast
  ring

theorem iCC : ((C.val).intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = -R.w C := by
  rw [inter_vertices, M_diag]

include hwH in
theorem iHH : ((H.val).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = -2 := by
  rw [inter_vertices, M_diag, hwH]

include hadj in
theorem iCH : ((C.val).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 1 := by
  rw [inter_vertices, M_eq_one_of_adj R hadj]

include hadj in
theorem iHC : ((H.val).intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 1 := by
  rw [inter_vertices, M_eq_one_of_adj R hadj.symm]

include hPC in
theorem iPC : (P.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 1 := by
  exact_mod_cast hPC

include hPC in
theorem iCP : ((C.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 1 := by
  rw [inter_comm]
  exact_mod_cast hPC

include hPH in
theorem iPH : (P.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 1 := by
  exact_mod_cast hPH

include hPH in
theorem iHP : ((H.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 1 := by
  rw [inter_comm]
  exact_mod_cast hPH

include hP in
theorem P_ne_C : P ≠ C.val := fun h => hP.2 (h ▸ C.property)

include hP in
theorem P_ne_H : P ≠ H.val := fun h => hP.2 (h ▸ H.property)

include hCH in
theorem C_ne_H : C.val ≠ H.val := fun h => hCH (Subtype.ext h)

/-! ### `b ≤ 4` (manuscript lines 1749–1754) -/

/-- The weight of an exceptional curve is a (cast) integer. -/
theorem w_eq_int_cast (i : R.Vertices) :
    R.w i = ((-(i.val.selfIntersectionNumber R.hreg) : ℤ) : ℚ) := by
  rw [KltDP.Manuscript.S05.w_eq_neg_selfIntersection, Int.cast_neg]

include hP hCH hwH hadj hPC hPH in
/-- Manuscript Lemma 6.3, first claim: `b = -C² ≤ 4`. The discrepancy equations give
`2λ_H ≥ λ_C` and `bλ_C ≥ b - 2 + λ_H`, whose contribution to `Σ λ_i (P·D_i) = 1 - L·P < 1` is at
least `3(b-2)/(2b-1) ≥ 1` for `b ≥ 5`. -/
theorem weight_le_four : R.w C ≤ 4 := by
  classical
  by_contra hlt
  push_neg at hlt
  have h5 : (5 : ℚ) ≤ R.w C := by
    rw [w_eq_int_cast] at hlt ⊢
    have h4 : (4 : ℤ) < -(C.val.selfIntersectionNumber R.hreg) := by exact_mod_cast hlt
    exact_mod_cast (by omega : (5 : ℤ) ≤ -(C.val.selfIntersectionNumber R.hreg))
  have h1 := lam_le_of_adj R hadj
  have h2 := lam_le_of_adj R hadj.symm
  rw [hwH] at h2
  have hch := rankOneProjection_charge_lt_one R P hP
  have hsum : contactVector R P C * R.lam C + contactVector R P H * R.lam H ≤
      dotProduct (contactVector R P) R.lam := by
    unfold dotProduct
    exact Finset.add_le_sum (fun j _ => mul_nonneg (contact_cast_nonneg R P hP.2 j) (R.lam_nonneg j))
      (Finset.mem_univ C) (Finset.mem_univ H) hCH
  have hcC : contactVector R P C = 1 := by
    show (R.contact P C : ℚ) = 1
    rw [hPC, Int.cast_one]
  have hcH : contactVector R P H = 1 := by
    show (R.contact P H : ℚ) = 1
    rw [hPH, Int.cast_one]
  rw [hcC, hcH, one_mul, one_mul] at hsum
  have hlamC := R.lam_nonneg C
  have hlamH := R.lam_nonneg H
  have h3 : R.lam C + R.lam H < 1 := lt_of_le_of_lt hsum hch
  set b := R.w C with hb
  set x := R.lam C with hx
  set y := R.lam H with hy
  have hbpos : 0 < b := by linarith
  have i1 : y * (1 + b) < 2 := by
    have e := mul_lt_mul_of_pos_left h3 hbpos
    nlinarith
  have i2 : b - 2 ≤ y * (2 * b - 1) := by
    have e := mul_le_mul_of_nonneg_left h2 hbpos.le
    nlinarith
  have j1 := mul_lt_mul_of_pos_right i1 (by linarith : (0 : ℚ) < 2 * b - 1)
  have j2 := mul_le_mul_of_nonneg_right i2 (by linarith : (0 : ℚ) ≤ 1 + b)
  have j3 : 0 ≤ b * (b - 5) := mul_nonneg hbpos.le (by linarith)
  nlinarith [j1, j2, j3]

include hP hCH hwH hadj hPC hPH in
theorem weight_cases : R.w C = 2 ∨ R.w C = 3 ∨ R.w C = 4 := by
  have h4 := weight_le_four R P C H hP hCH hwH hadj hPC hPH
  have h2 := R.two_le_w C
  rw [w_eq_int_cast] at h4 h2 ⊢
  have h4' : -(C.val.selfIntersectionNumber R.hreg) ≤ (4 : ℤ) := by exact_mod_cast h4
  have h2' : (2 : ℤ) ≤ -(C.val.selfIntersectionNumber R.hreg) := by exact_mod_cast h2
  rcases (by omega : -(C.val.selfIntersectionNumber R.hreg) = 2 ∨
      -(C.val.selfIntersectionNumber R.hreg) = 3 ∨
      -(C.val.selfIntersectionNumber R.hreg) = 4) with h | h | h
  · left; rw [h]; norm_num
  · right; left; rw [h]; norm_num
  · right; right; rw [h]; norm_num

/-! ### Nefness of the configuration divisors -/

/-- `a C + h H + q P` (with `a, h, q ≥ 0`) is nef as soon as its degrees on `C, H, P` are
nonnegative: every other curve meets the effective divisor nonnegatively. -/
theorem adjDiv_nef (a h q : ℤ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hq : 0 ≤ q)
    (hAC : 0 ≤ degW R C.val (adjDiv R P C H a h q))
    (hAH : 0 ≤ degW R H.val (adjDiv R P C H a h q))
    (hAP : 0 ≤ degW R P (adjDiv R P C H a h q)) :
    ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q (adjDiv R P C H a h q) := by
  intro Q
  by_cases hQC : Q = C.val
  · rw [hQC]; exact hAC
  by_cases hQH : Q = H.val
  · rw [hQH]; exact hAH
  by_cases hQP : Q = P
  · rw [hQP]; exact hAP
  rw [degW_adjDiv]
  have ha' : (0 : ℚ) ≤ a := by exact_mod_cast ha
  have hh' : (0 : ℚ) ≤ h := by exact_mod_cast hh
  have hq' : (0 : ℚ) ≤ q := by exact_mod_cast hq
  exact add_nonneg (add_nonneg (mul_nonneg ha' (inter_nonneg R Q C.val hQC))
    (mul_nonneg hh' (inter_nonneg R Q H.val hQH))) (mul_nonneg hq' (inter_nonneg R Q P hQP))

/-- A curve outside the configuration which is null for `a C + h H + q P` (`a, h, q > 0`) is
disjoint from `C`, `H` and `P`. -/
theorem null_inter_eq_zero (a h q : ℤ) (ha : 0 < a) (hh : 0 < h) (hq : 0 < q)
    (Q : R.S.PrimeCurve) (hQC : Q ≠ C.val) (hQH : Q ≠ H.val) (hQP : Q ≠ P)
    (h0 : degW R Q (adjDiv R P C H a h q) = 0) :
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 0 ∧
    (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
  rw [degW_adjDiv] at h0
  have h1 := inter_nonneg R Q C.val hQC
  have h2 := inter_nonneg R Q H.val hQH
  have h3 := inter_nonneg R Q P hQP
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hh' : (0 : ℚ) < h := by exact_mod_cast hh
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have m1 := mul_nonneg ha'.le h1
  have m2 := mul_nonneg hh'.le h2
  have m3 := mul_nonneg hq'.le h3
  have e1 : (a : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 0 := by
    linarith
  have e2 : (h : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 0 := by
    linarith
  have e3 : (q : ℚ) * (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
    linarith
  exact ⟨(mul_eq_zero.mp e1).resolve_left ha'.ne', (mul_eq_zero.mp e2).resolve_left hh'.ne',
    (mul_eq_zero.mp e3).resolve_left hq'.ne'⟩

/-! ### The Riemann–Roch core (manuscript lines 1755–1762) -/

include hP hCH in
/-- The effective adjoint representative `Z ∼ K_S + A`, `A = a C + h H + q P`, its remainder `N`
outside the configuration, and the three coefficient equations obtained by intersecting with
`C`, `H`, `P`. -/
theorem adjointCore (p : ℕ) [CharP k p] (hp : 0 < p) (a h q : ℤ) (ha : 0 < a) (hh : 0 < h)
    (hq : 0 < q)
    (hAC : 0 ≤ degW R C.val (adjDiv R P C H a h q))
    (hAH : 0 ≤ degW R H.val (adjDiv R P C H a h q))
    (hAP : 0 ≤ degW R P (adjDiv R P C H a h q))
    (hsq : 0 < R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
      (numW R (adjDiv R P C H a h q)))
    (hKA : R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R (adjDiv R P C H a h q)) +
      R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
        (numW R (adjDiv R P C H a h q)) = 0) :
    ∃ Z N : R.S.WeilDivisor, EffectiveDivisor Z ∧ EffectiveDivisor N ∧
      R.S.LinearlyEquivalent Z (R.S.cartierToWeilHom R.KS + adjDiv R P C H a h q) ∧
      Z = N + Finsupp.single C.val (Z C.val) + Finsupp.single H.val (Z H.val) +
        Finsupp.single P (Z P) ∧
      N C.val = 0 ∧ N H.val = 0 ∧ N P = 0 ∧
      (∀ Q : R.S.PrimeCurve, N Q ≠ 0 → degW R Q (adjDiv R P C H a h q) = 0) ∧
      (∀ Q : R.S.PrimeCurve, N Q ≠ 0 →
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 0 ∧
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 0 ∧
        (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0) ∧
      (R.w C - 2) + degW R C.val (adjDiv R P C H a h q) =
        -(R.w C) * (Z C.val : ℚ) + (Z H.val : ℚ) *
          ((C.val).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) +
          (Z P : ℚ) * ((C.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) ∧
      (R.w H - 2) + degW R H.val (adjDiv R P C H a h q) =
        (Z C.val : ℚ) * ((H.val).intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) -
          R.w H * (Z H.val : ℚ) +
          (Z P : ℚ) * ((H.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) ∧
      -1 + degW R P (adjDiv R P C H a h q) =
        (Z C.val : ℚ) * (P.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) +
          (Z H.val : ℚ) * (P.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) -
          (Z P : ℚ) := by
  classical
  have hnef := adjDiv_nef R P C H a h q ha.le hh.le hq.le hAC hAH hAP
  have hrr : 0 < R.S.numericalIntersectionBilinForm R.hreg (R.Knum + numW R (adjDiv R P C H a h q))
      (numW R (adjDiv R P C H a h q)) / 2 + 1 := by
    rw [LinearMap.BilinForm.add_left, hKA]
    norm_num
  obtain ⟨Z, hZ, hlin⟩ := exists_effective_adjoint R p hp (adjDiv R P C H a h q) hnef hsq hrr
  have hnumZ : numW R Z = R.Knum + numW R (adjDiv R P C H a h q) := by
    rw [numW_eq_of_linearlyEquivalent R hlin, map_add, numW_KS]
  have hAZ : R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
      (numW R Z) = 0 := by
    rw [hnumZ, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg) _ R.Knum,
      hKA]
  have hZnull : ∀ Q : R.S.PrimeCurve, Z Q ≠ 0 → degW R Q (adjDiv R P C H a h q) = 0 :=
    degW_eq_zero_of_component R (adjDiv R P C H a h q) Z hnef hZ hAZ
  have hPC' := P_ne_C R P C hP
  have hPH' := P_ne_H R P H hP
  have hCH' := C_ne_H R C H hCH
  -- the remainder
  set N : R.S.WeilDivisor := Z - Finsupp.single C.val (Z C.val) - Finsupp.single H.val (Z H.val) -
    Finsupp.single P (Z P) with hNdef
  have hNapply : ∀ Q, N Q = Z Q - (if C.val = Q then Z C.val else 0) -
      (if H.val = Q then Z H.val else 0) - (if P = Q then Z P else 0) := by
    intro Q
    simp only [hNdef, Finsupp.sub_apply, Finsupp.single_apply]
  have hNC : N C.val = 0 := by
    rw [hNapply]
    simp [Ne.symm hCH', hPC']
  have hNH : N H.val = 0 := by
    rw [hNapply]
    simp [hCH', hPH']
  have hNP : N P = 0 := by
    rw [hNapply]
    simp [Ne.symm hPC', Ne.symm hPH']
  have hNother : ∀ Q, Q ≠ C.val → Q ≠ H.val → Q ≠ P → N Q = Z Q := by
    intro Q hQC hQH hQP
    rw [hNapply]
    simp [Ne.symm hQC, Ne.symm hQH, Ne.symm hQP]
  have hNeff : EffectiveDivisor N := by
    intro Q
    by_cases hQC : Q = C.val
    · rw [hQC, hNC]
    by_cases hQH : Q = H.val
    · rw [hQH, hNH]
    by_cases hQP : Q = P
    · rw [hQP, hNP]
    rw [hNother Q hQC hQH hQP]
    exact hZ Q
  have hZdecomp : Z = N + Finsupp.single C.val (Z C.val) + Finsupp.single H.val (Z H.val) +
      Finsupp.single P (Z P) := by
    rw [hNdef]
    abel
  have hNne : ∀ Q, N Q ≠ 0 → Q ≠ C.val ∧ Q ≠ H.val ∧ Q ≠ P ∧ Z Q ≠ 0 := by
    intro Q hQ
    have hQC : Q ≠ C.val := fun h => hQ (h ▸ hNC)
    have hQH : Q ≠ H.val := fun h => hQ (h ▸ hNH)
    have hQP : Q ≠ P := fun h => hQ (h ▸ hNP)
    refine ⟨hQC, hQH, hQP, ?_⟩
    rwa [hNother Q hQC hQH hQP] at hQ
  have hNnull : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 → degW R Q (adjDiv R P C H a h q) = 0 :=
    fun Q hQ => hZnull Q (hNne Q hQ).2.2.2
  have hNdisj : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 →
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0 := by
    intro Q hQ
    obtain ⟨hQC, hQH, hQP, _⟩ := hNne Q hQ
    exact null_inter_eq_zero R P C H a h q ha hh hq Q hQC hQH hQP (hNnull Q hQ)
  -- the degrees of `Z` on the configuration
  have hdegZ : ∀ X : R.S.PrimeCurve, degW R X Z = (R.Kdeg X : ℚ) + degW R X (adjDiv R P C H a h q) := by
    intro X
    unfold degW
    rw [hnumZ, map_add, KltDP.Manuscript.S03.numericalRestrictionDegree_Knum]
  have hdegN : ∀ X : R.S.PrimeCurve, (X = C.val ∨ X = H.val ∨ X = P) → degW R X N = 0 := by
    intro X hX
    rw [degW_eq_sum]
    refine Finset.sum_eq_zero (fun Q hQ => ?_)
    obtain ⟨h1, h2, h3⟩ := hNdisj Q (Finsupp.mem_support_iff.mp hQ)
    rw [inter_comm R X Q]
    rcases hX with rfl | rfl | rfl
    · rw [h1, mul_zero]
    · rw [h2, mul_zero]
    · rw [h3, mul_zero]
  have hdegZ' : ∀ X : R.S.PrimeCurve, degW R X Z = degW R X N +
      (Z C.val : ℚ) * (X.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) +
      (Z H.val : ℚ) * (X.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) +
      (Z P : ℚ) * (X.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
    intro X
    nth_rewrite 1 [hZdecomp]
    rw [degW_add, degW_add, degW_add, degW_single, degW_single, degW_single]
  refine ⟨Z, N, hZ, hNeff, hlin, hZdecomp, hNC, hNH, hNP, hNnull, hNdisj, ?_, ?_, ?_⟩
  · have e1 := hdegZ C.val
    rw [hdegZ' C.val, hdegN C.val (Or.inl rfl), R.Kdeg_exceptional, iCC] at e1
    simp only [ResolutionDatum.q] at e1
    linarith
  · have e1 := hdegZ H.val
    rw [hdegZ' H.val, hdegN H.val (Or.inr (Or.inl rfl)), R.Kdeg_exceptional, inter_vertices R H H,
      M_diag] at e1
    simp only [ResolutionDatum.q] at e1
    linarith
  · have e1 := hdegZ P
    rw [hdegZ' P, hdegN P (Or.inr (Or.inr rfl)), Kdeg_eq_neg_one_of_isMinusOne R P hP.1, iPP R P hP]
      at e1
    push_cast at e1
    linarith

/-! ### The conclusions about the remainder -/

/-- The numerical data of a configuration divisor `A` (manuscript table, lines 1735–1741):
`A` is nef, `A² = 1`, `K_S · A = -1`, with the displayed degrees on `C`, `H`, `P`. -/
structure AdjointDivisorData (A : R.S.WeilDivisor) (dC dH dP : ℚ) : Prop where
  nef : ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q A
  square : R.S.numericalIntersectionBilinForm R.hreg (numW R A) (numW R A) = 1
  Kdeg : R.S.numericalIntersectionBilinForm R.hreg R.Knum (numW R A) = -1
  degC : degW R C.val A = dC
  degH : degW R H.val A = dH
  degP : degW R P A = dP

/-- The conclusions of Lemma 6.3 about the remainder `N` of the adjoint divisor `K_S + A`,
`K_S + A ∼ Z + N` (manuscript lines 1742–1748 and 1763–1770). -/
structure AdjointRemainder (A Z N : R.S.WeilDivisor) : Prop where
  effective : EffectiveDivisor N
  adjoint : R.S.LinearlyEquivalent (R.S.cartierToWeilHom R.KS + A) (Z + N)
  class_eq : R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1)
  coeff_C : N C.val = 0
  coeff_H : N H.val = 0
  coeff_P : N P = 0
  null : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 → degW R Q A = 0
  disjoint : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 →
    Disjoint (Q : Set R.S.toScheme) (C.val : Set R.S.toScheme) ∧
    Disjoint (Q : Set R.S.toScheme) (H.val : Set R.S.toScheme) ∧
    Disjoint (Q : Set R.S.toScheme) (P : Set R.S.toScheme)
  Ldeg_eq : LdegW R N = R.Ldeg P - R.Lsq
  exterior_mem : ∀ Q : R.S.PrimeCurve, ¬ IsExceptionalCurve R.π Q → Q ≠ P → degW R Q A = 0 →
    0 < N Q
  exterior_bound : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 → ¬ IsExceptionalCurve R.π Q →
    0 < R.Ldeg Q ∧ R.Ldeg Q ≤ R.Ldeg P - R.Lsq
  unique : ∀ N' : R.S.WeilDivisor, EffectiveDivisor N' → R.S.LinearlyEquivalent N' N → N' = N

include hP hCH in
/-- Assembling the remainder conclusions from the core data. -/
theorem adjointRemainder_mk (a h q : ℤ) (ha : 0 < a) (hh : 0 < h) (hq : 0 < q)
    (hnef : ∀ Q : R.S.PrimeCurve, 0 ≤ degW R Q (adjDiv R P C H a h q))
    (hsq : 0 < R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
      (numW R (adjDiv R P C H a h q)))
    (Z N : R.S.WeilDivisor) (hNeff : EffectiveDivisor N)
    (hadjoint : R.S.LinearlyEquivalent (R.S.cartierToWeilHom R.KS + adjDiv R P C H a h q) (Z + N))
    (hclass : R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1))
    (hNC : N C.val = 0) (hNH : N H.val = 0) (hNP : N P = 0)
    (hnull : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 → degW R Q (adjDiv R P C H a h q) = 0)
    (hdisj : ∀ Q : R.S.PrimeCurve, N Q ≠ 0 →
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) = 0 ∧
      (Q.intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) = 0) :
    AdjointRemainder R P C H (adjDiv R P C H a h q) Z N := by
  classical
  have hPC' := P_ne_C R P C hP
  have hPH' := P_ne_H R P H hP
  have hCH' := C_ne_H R C H hCH
  have hnumN : numW R N = R.Knum + curveClass R.S R.hreg C.val + curveClass R.S R.hreg H.val +
      curveClass R.S R.hreg P := by
    rw [numW_eq_of_linearlyEquivalent R hclass, map_add, numW_KS, numW_adjDiv]
    simp only [Int.cast_one, one_smul, add_assoc]
  have hNne : ∀ Q, N Q ≠ 0 → Q ≠ C.val ∧ Q ≠ H.val ∧ Q ≠ P := fun Q hQ =>
    ⟨fun h => hQ (h ▸ hNC), fun h => hQ (h ▸ hNH), fun h => hQ (h ▸ hNP)⟩
  -- `N · A = 0`
  have hAN : R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
      (numW R N) = 0 := by
    rw [pairing_numW_eq_sum]
    exact Finset.sum_eq_zero (fun Q hQ => by
      rw [hnull Q (Finsupp.mem_support_iff.mp hQ), mul_zero])
  refine ⟨hNeff, hadjoint, hclass, hNC, hNH, hNP, hnull, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨h1, h2, h3⟩ := hdisj Q hQ
    obtain ⟨hQC, hQH, hQP⟩ := hNne Q hQ
    exact ⟨disjoint_of_inter_eq_zero R Q C.val hQC h1, disjoint_of_inter_eq_zero R Q H.val hQH h2,
      disjoint_of_inter_eq_zero R Q P hQP h3⟩
  · rw [LdegW_eq_pairing, hnumN]
    simp only [LinearMap.BilinForm.add_right, R.Knum_pairing_Lnum, Lnum_pairing_curveClass,
      R.Ldeg_exceptional]
    have hsymm : R.S.numericalIntersectionBilinForm R.hreg R.Lnum R.Knum =
        R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Lnum :=
      LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg) _ _
    rw [hsymm, R.Knum_pairing_Lnum]
    ring
  · intro Q hQext hQP h0
    have hQC : Q ≠ C.val := fun h => hQext (h ▸ C.property)
    have hQH : Q ≠ H.val := fun h => hQext (h ▸ H.property)
    obtain ⟨h1, h2, h3⟩ := null_inter_eq_zero R P C H a h q ha hh hq Q hQC hQH hQP h0
    -- `Q` is a `(-1)`-curve (Lemma 2.9)
    have hminus := exteriorNullCurve_isMinusOne R (numW R (adjDiv R P C H a h q)) hnef hsq Q hQext h0
    -- `N · Q = K_S · Q = -1`
    have hdeg : degW R Q N = -1 := by
      rw [degW, hnumN, map_add, map_add, map_add,
        KltDP.Manuscript.S03.numericalRestrictionDegree_Knum, hminus.2,
        numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass,
        numericalRestrictionDegree_curveClass, h1, h2, h3]
      push_cast
      ring
    by_contra hle
    push_neg at hle
    have hQ0 : N Q = 0 := le_antisymm hle (hNeff Q)
    have := degW_nonneg_of_coeff_eq_zero R Q N hNeff hQ0
    linarith
  · intro Q hQ hQext
    have hpos := Ldeg_pos R Q hQext
    have h1 : (1 : ℚ) ≤ (N Q : ℚ) := by
      have : 0 < N Q := lt_of_le_of_ne (hNeff Q) (Ne.symm hQ)
      exact_mod_cast this
    have h2 := coeff_mul_Ldeg_le_LdegW R N hNeff Q
    have hL : LdegW R N = R.Ldeg P - R.Lsq := by
      rw [LdegW_eq_pairing, hnumN]
      simp only [LinearMap.BilinForm.add_right, Lnum_pairing_curveClass, R.Ldeg_exceptional]
      have hsymm : R.S.numericalIntersectionBilinForm R.hreg R.Lnum R.Knum =
          R.S.numericalIntersectionBilinForm R.hreg R.Knum R.Lnum :=
        LinearMap.BilinForm.IsSymm.eq (R.S.numericalIntersectionBilinForm_isSymm R.hreg) _ _
      rw [hsymm, R.Knum_pairing_Lnum]
      ring
    refine ⟨hpos, ?_⟩
    rw [← hL]
    calc R.Ldeg Q = 1 * R.Ldeg Q := (one_mul _).symm
      _ ≤ (N Q : ℚ) * R.Ldeg Q := mul_le_mul_of_nonneg_right h1 hpos.le
      _ ≤ LdegW R N := h2
  · intro N' hN' hlin'
    have heq : numW R N' = numW R N := numW_eq_of_linearlyEquivalent R hlin'
    have hAN' : R.S.numericalIntersectionBilinForm R.hreg (numW R (adjDiv R P C H a h q))
        (numW R N') = 0 := by
      rw [heq, hAN]
    have hnull' := degW_eq_zero_of_component R (adjDiv R P C H a h q) N' hnef hN' hAN'
    exact eq_of_effective_of_null R (numW R (adjDiv R P C H a h q)) hsq N' N hN' hNeff
      (fun Q hQ => hnull' Q hQ) heq

/-! ### The three cases `b = 2, 3, 4` -/

include hP hwH hadj hPC hPH in
theorem adjointDivisorData_two (hb : R.w C = 2) :
    AdjointDivisorData R P C H (adjDiv R P C H 1 1 1) 0 0 1 := by
  have dC : degW R C.val (adjDiv R P C H 1 1 1) = 0 := by
    rw [degW_adjDiv, iCC, iCH R C H hadj, iCP R P C hPC, hb]; norm_num
  have dH : degW R H.val (adjDiv R P C H 1 1 1) = 0 := by
    rw [degW_adjDiv, iHC R C H hadj, iHH R H hwH, iHP R P H hPH]; norm_num
  have dP : degW R P (adjDiv R P C H 1 1 1) = 1 := by
    rw [degW_adjDiv, iPC R P C hPC, iPH R P H hPH, iPP R P hP]; norm_num
  refine ⟨adjDiv_nef R P C H 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by rw [dC]; try norm_num)
    (by rw [dH]; try norm_num) (by rw [dP]; try norm_num), ?_, ?_, dC, dH, dP⟩
  · rw [square_adjDiv, dC, dH, dP]; norm_num
  · rw [Knum_pairing_adjDiv R P C H hP, hb, hwH]; norm_num

include hP hwH hadj hPC hPH in
theorem adjointDivisorData_three (hb : R.w C = 3) :
    AdjointDivisorData R P C H (adjDiv R P C H 1 1 2) 0 1 0 := by
  have dC : degW R C.val (adjDiv R P C H 1 1 2) = 0 := by
    rw [degW_adjDiv, iCC, iCH R C H hadj, iCP R P C hPC, hb]; norm_num
  have dH : degW R H.val (adjDiv R P C H 1 1 2) = 1 := by
    rw [degW_adjDiv, iHC R C H hadj, iHH R H hwH, iHP R P H hPH]; norm_num
  have dP : degW R P (adjDiv R P C H 1 1 2) = 0 := by
    rw [degW_adjDiv, iPC R P C hPC, iPH R P H hPH, iPP R P hP]; norm_num
  refine ⟨adjDiv_nef R P C H 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by rw [dC]; try norm_num)
    (by rw [dH]; try norm_num) (by rw [dP]; try norm_num), ?_, ?_, dC, dH, dP⟩
  · rw [square_adjDiv, dC, dH, dP]; norm_num
  · rw [Knum_pairing_adjDiv R P C H hP, hb, hwH]; norm_num

include hP hwH hadj hPC hPH in
theorem adjointDivisorData_four (hb : R.w C = 4) :
    AdjointDivisorData R P C H (adjDiv R P C H 1 2 3) 1 0 0 := by
  have dC : degW R C.val (adjDiv R P C H 1 2 3) = 1 := by
    rw [degW_adjDiv, iCC, iCH R C H hadj, iCP R P C hPC, hb]; norm_num
  have dH : degW R H.val (adjDiv R P C H 1 2 3) = 0 := by
    rw [degW_adjDiv, iHC R C H hadj, iHH R H hwH, iHP R P H hPH]; norm_num
  have dP : degW R P (adjDiv R P C H 1 2 3) = 0 := by
    rw [degW_adjDiv, iPC R P C hPC, iPH R P H hPH, iPP R P hP]; norm_num
  refine ⟨adjDiv_nef R P C H 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by rw [dC]; try norm_num)
    (by rw [dH]; try norm_num) (by rw [dP]; try norm_num), ?_, ?_, dC, dH, dP⟩
  · rw [square_adjDiv, dC, dH, dP]; norm_num
  · rw [Knum_pairing_adjDiv R P C H hP, hb, hwH]; norm_num

/-- Linear equivalence of Weil divisors transported along an equality of class maps. -/
theorem linearlyEquivalent_of_sub {Z N X D : R.S.WeilDivisor} (hZ : Z = N + X)
    (hlin : R.S.LinearlyEquivalent Z D) : R.S.LinearlyEquivalent N (D - X) := by
  rw [linearlyEquivalent_iff_weilClassMap] at hlin ⊢
  rw [map_sub, ← hlin, hZ, map_add, add_sub_cancel_right]

include hP hCH hwH hadj hPC hPH in
/-- Case `b = 2`: `A_2 = C + H + P`, `Z_2 = 0`. -/
theorem adjointRemainder_two (p : ℕ) [CharP k p] (hp : 0 < p) (hb : R.w C = 2) :
    ∃ N : R.S.WeilDivisor, AdjointRemainder R P C H (adjDiv R P C H 1 1 1) 0 N := by
  obtain ⟨hnef, hsq, hK, dC, dH, dP⟩ := adjointDivisorData_two R P C H hP hwH hadj hPC hPH hb
  obtain ⟨Z, N, hZ, hNeff, hlin, hZdecomp, hNC, hNH, hNP, hnull, hdisj, e1, e2, e3⟩ :=
    adjointCore R P C H hP hCH p hp 1 1 1 (by norm_num) (by norm_num) (by norm_num)
      (by rw [dC]; try norm_num) (by rw [dH]; try norm_num) (by rw [dP]; try norm_num) (by rw [hsq]; norm_num) (by rw [hK, hsq]; norm_num)
  rw [dC, iCH R C H hadj, iCP R P C hPC, hb] at e1
  rw [dH, iHC R C H hadj, iHP R P H hPH, hwH] at e2
  rw [dP, iPC R P C hPC, iPH R P H hPH] at e3
  have hz : Z C.val = 0 ∧ Z H.val = 0 ∧ Z P = 0 := by
    have hZC := hZ C.val
    have hZH := hZ H.val
    have hZP := hZ P
    have f1 : (2 : ℚ) * (Z C.val : ℚ) = (Z H.val : ℚ) + (Z P : ℚ) := by linarith
    have f2 : (2 : ℚ) * (Z H.val : ℚ) = (Z C.val : ℚ) + (Z P : ℚ) := by linarith
    have f3 : (Z P : ℚ) = (Z C.val : ℚ) + (Z H.val : ℚ) := by linarith
    have g1 : 2 * Z C.val = Z H.val + Z P := by exact_mod_cast f1
    have g2 : 2 * Z H.val = Z C.val + Z P := by exact_mod_cast f2
    have g3 : Z P = Z C.val + Z H.val := by exact_mod_cast f3
    omega
  obtain ⟨z1, z2, z3⟩ := hz
  rw [z1, z2, z3, Finsupp.single_zero, Finsupp.single_zero, Finsupp.single_zero, add_zero, add_zero,
    add_zero] at hZdecomp
  subst hZdecomp
  refine ⟨Z, adjointRemainder_mk R P C H hP hCH 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) hnef (by rw [hsq]; norm_num) 0 Z hNeff ?_ hlin hNC hNH hNP hnull hdisj⟩
  rw [zero_add]
  exact R.S.linearlyEquivalent_symm hlin

include hP hCH hwH hadj hPC hPH in
/-- Case `b = 3`: `A_3 = C + H + 2P`, `Z_3 = P`. -/
theorem adjointRemainder_three (p : ℕ) [CharP k p] (hp : 0 < p) (hb : R.w C = 3) :
    ∃ N : R.S.WeilDivisor,
      AdjointRemainder R P C H (adjDiv R P C H 1 1 2) (Finsupp.single P 1) N := by
  obtain ⟨hnef, hsq, hK, dC, dH, dP⟩ := adjointDivisorData_three R P C H hP hwH hadj hPC hPH hb
  obtain ⟨Z, N, hZ, hNeff, hlin, hZdecomp, hNC, hNH, hNP, hnull, hdisj, e1, e2, e3⟩ :=
    adjointCore R P C H hP hCH p hp 1 1 2 (by norm_num) (by norm_num) (by norm_num)
      (by rw [dC]; try norm_num) (by rw [dH]; try norm_num) (by rw [dP]; try norm_num) (by rw [hsq]; norm_num) (by rw [hK, hsq]; norm_num)
  rw [dC, iCH R C H hadj, iCP R P C hPC, hb] at e1
  rw [dH, iHC R C H hadj, iHP R P H hPH, hwH] at e2
  rw [dP, iPC R P C hPC, iPH R P H hPH] at e3
  have hz : Z C.val = 0 ∧ Z H.val = 0 ∧ Z P = 1 := by
    have hZC := hZ C.val
    have hZH := hZ H.val
    have hZP := hZ P
    have f1 : (1 : ℚ) + 3 * (Z C.val : ℚ) = (Z H.val : ℚ) + (Z P : ℚ) := by linarith
    have f2 : (1 : ℚ) + 2 * (Z H.val : ℚ) = (Z C.val : ℚ) + (Z P : ℚ) := by linarith
    have f3 : (Z P : ℚ) = (Z C.val : ℚ) + (Z H.val : ℚ) + 1 := by linarith
    have g1 : 1 + 3 * Z C.val = Z H.val + Z P := by exact_mod_cast f1
    have g2 : 1 + 2 * Z H.val = Z C.val + Z P := by exact_mod_cast f2
    have g3 : Z P = Z C.val + Z H.val + 1 := by exact_mod_cast f3
    omega
  obtain ⟨z1, z2, z3⟩ := hz
  rw [z1, z2, z3, Finsupp.single_zero, Finsupp.single_zero, add_zero, add_zero] at hZdecomp
  have hclass : R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1) := by
    have h := linearlyEquivalent_of_sub R hZdecomp hlin
    have hsub : R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 2 - Finsupp.single P 1 =
        R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1 := by
      simp only [adjDiv]
      rw [show (2 : ℤ) = 1 + 1 by norm_num, Finsupp.single_add]
      abel
    rwa [hsub] at h
  refine ⟨N, adjointRemainder_mk R P C H hP hCH 1 1 2 (by norm_num) (by norm_num)
    (by norm_num) hnef (by rw [hsq]; norm_num) (Finsupp.single P 1) N hNeff ?_ hclass hNC hNH hNP
    hnull hdisj⟩
  rw [add_comm (Finsupp.single P 1) N, ← hZdecomp]
  exact R.S.linearlyEquivalent_symm hlin

include hP hCH hwH hadj hPC hPH in
/-- Case `b = 4`: `A_4 = C + 2H + 3P`, `Z_4 = H + 2P`. -/
theorem adjointRemainder_four (p : ℕ) [CharP k p] (hp : 0 < p) (hb : R.w C = 4) :
    ∃ N : R.S.WeilDivisor,
      AdjointRemainder R P C H (adjDiv R P C H 1 2 3)
        (Finsupp.single H.val 1 + Finsupp.single P 2) N := by
  obtain ⟨hnef, hsq, hK, dC, dH, dP⟩ := adjointDivisorData_four R P C H hP hwH hadj hPC hPH hb
  obtain ⟨Z, N, hZ, hNeff, hlin, hZdecomp, hNC, hNH, hNP, hnull, hdisj, e1, e2, e3⟩ :=
    adjointCore R P C H hP hCH p hp 1 2 3 (by norm_num) (by norm_num) (by norm_num)
      (by rw [dC]; try norm_num) (by rw [dH]; try norm_num) (by rw [dP]; try norm_num) (by rw [hsq]; norm_num) (by rw [hK, hsq]; norm_num)
  rw [dC, iCH R C H hadj, iCP R P C hPC, hb] at e1
  rw [dH, iHC R C H hadj, iHP R P H hPH, hwH] at e2
  rw [dP, iPC R P C hPC, iPH R P H hPH] at e3
  have hz : Z C.val = 0 ∧ Z H.val = 1 ∧ Z P = 2 := by
    have hZC := hZ C.val
    have hZH := hZ H.val
    have hZP := hZ P
    have f1 : (3 : ℚ) + 4 * (Z C.val : ℚ) = (Z H.val : ℚ) + (Z P : ℚ) := by linarith
    have f2 : (2 : ℚ) * (Z H.val : ℚ) = (Z C.val : ℚ) + (Z P : ℚ) := by linarith
    have f3 : (Z P : ℚ) = (Z C.val : ℚ) + (Z H.val : ℚ) + 1 := by linarith
    have g1 : 3 + 4 * Z C.val = Z H.val + Z P := by exact_mod_cast f1
    have g2 : 2 * Z H.val = Z C.val + Z P := by exact_mod_cast f2
    have g3 : Z P = Z C.val + Z H.val + 1 := by exact_mod_cast f3
    omega
  obtain ⟨z1, z2, z3⟩ := hz
  rw [z1, z2, z3, Finsupp.single_zero, add_zero] at hZdecomp
  have hZ' : Z = N + (Finsupp.single H.val 1 + Finsupp.single P 2) := by
    rw [hZdecomp, add_assoc]
  have hclass : R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1) := by
    have h := linearlyEquivalent_of_sub R hZ' hlin
    have hsub : R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 2 3 -
        (Finsupp.single H.val 1 + Finsupp.single P 2) =
        R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1 := by
      have e1 : Finsupp.single H.val (2 : ℤ) = Finsupp.single H.val 1 + Finsupp.single H.val 1 := by
        rw [← Finsupp.single_add]; norm_num
      have e2 : Finsupp.single P (3 : ℤ) = Finsupp.single P 1 + Finsupp.single P 2 := by
        rw [← Finsupp.single_add]; norm_num
      simp only [adjDiv]
      rw [e1, e2]
      abel
    rwa [hsub] at h
  refine ⟨N, adjointRemainder_mk R P C H hP hCH 1 2 3 (by norm_num) (by norm_num)
    (by norm_num) hnef (by rw [hsq]; norm_num) (Finsupp.single H.val 1 + Finsupp.single P 2) N
    hNeff ?_ hclass hNC hNH hNP hnull hdisj⟩
  rw [add_comm _ N, ← hZ']
  exact R.S.linearlyEquivalent_symm hlin

/-! ### The extra clauses -/

/-- Manuscript lines 1747–1748: `N ≠ 0` if a further weight-two exceptional curve `T ≠ C, H`
meets `P`, since `N · T = C·T + H·T + P·T > 0`. -/
theorem remainder_ne_zero_of_contact (N : R.S.WeilDivisor)
    (hclass : R.S.LinearlyEquivalent N (R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1))
    (T : R.Vertices) (hTC : T ≠ C) (hTH : T ≠ H) (hwT : R.w T = 2) (hPT : 0 < R.contact P T) :
    N ≠ 0 := by
  intro hN0
  have hnumN : numW R N = R.Knum + curveClass R.S R.hreg C.val + curveClass R.S R.hreg H.val +
      curveClass R.S R.hreg P := by
    rw [numW_eq_of_linearlyEquivalent R hclass, map_add, numW_KS, numW_adjDiv]
    simp only [Int.cast_one, one_smul, add_assoc]
  have hdeg : degW R T.val N = (R.w T - 2) +
      ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) +
      ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) +
      ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
    rw [degW, hnumN, map_add, map_add, map_add,
      KltDP.Manuscript.S03.numericalRestrictionDegree_Knum, R.Kdeg_exceptional,
      numericalRestrictionDegree_curveClass, numericalRestrictionDegree_curveClass,
      numericalRestrictionDegree_curveClass]
    rfl
  have h1 : 0 ≤ ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg C.val) : ℚ) :=
    inter_nonneg R T.val C.val (fun h => hTC (Subtype.ext h))
  have h2 : 0 ≤ ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℚ) :=
    inter_nonneg R T.val H.val (fun h => hTH (Subtype.ext h))
  have h3 : 0 < ((T.val).intersectionNumber (R.S.primeCurveCartier R.hreg P) : ℚ) := by
    rw [inter_comm]
    exact_mod_cast hPT
  rw [hN0, degW_zero] at hdeg
  rw [hwT] at hdeg
  linarith

include hP hCH hwH hadj hPC hPH in
/-- Manuscript lines 1774–1777: if `b = 2` and `N = 0`, then `-K_S ∼ C + H + P`, `K_S² = 1`,
`#Irr(D) = 8`, and the edge `CH` leaves at most seven connected components, so `#Sing(X) ≤ 7`. -/
theorem singularPoints_le_seven_of_remainder_zero (p : ℕ) [CharP k p] (hp : 0 < p)
    (hb : R.w C = 2)
    (hclass : R.S.LinearlyEquivalent 0 (R.S.cartierToWeilHom R.KS + adjDiv R P C H 1 1 1)) :
    R.X.singularPoints.card ≤ 7 := by
  classical
  -- `K_S ≡ -(C + H + P)`
  have hK : R.Knum = -(curveClass R.S R.hreg C.val + curveClass R.S R.hreg H.val +
      curveClass R.S R.hreg P) := by
    have h := numW_eq_of_linearlyEquivalent R hclass
    rw [map_zero, map_add, numW_KS, numW_adjDiv] at h
    simp only [Int.cast_one, one_smul] at h
    have h' : R.Knum + (curveClass R.S R.hreg C.val + curveClass R.S R.hreg H.val +
        curveClass R.S R.hreg P) = 0 := by
      rw [← add_assoc, ← add_assoc]
      exact h.symm
    exact eq_neg_of_add_eq_zero_left h'
  -- `K_S² = 1`
  have hcc : ∀ X Y : R.S.PrimeCurve, R.S.numericalIntersectionBilinForm R.hreg
      (curveClass R.S R.hreg X) (curveClass R.S R.hreg Y) =
      (X.intersectionNumber (R.S.primeCurveCartier R.hreg Y) : ℚ) :=
    fun X Y => curveClass_pairing_eq_intersectionNumber R X Y
  have hKsq : R.Ksq = 1 := by
    unfold ResolutionDatum.Ksq
    rw [hK]
    simp only [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hcc]
    rw [iCC, iHH R H hwH, iPP R P hP, iCH R C H hadj, iHC R C H hadj, iCP R P C hPC,
      iPC R P C hPC, iHP R P H hPH, iPH R P H hPH, hb]
    norm_num
  -- Noether: `ρ(S) = 9`, hence eight exceptional curves
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
  -- the components of the exceptional forest
  obtain ⟨hfin, hcount, -, -⟩ := R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt
  letI := hfin
  letI : Fintype (ActualExceptionalIncidence.graph R.π).ConnectedComponent := Fintype.ofFinite _
  rw [hcount, Nat.card_eq_fintype_card]
  have hsurj : Function.Surjective
      (fun v : R.Vertices => (ActualExceptionalIncidence.graph R.π).connectedComponentMk v) :=
    fun c => SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c
  have hninj : ¬ Function.Injective
      (fun v : R.Vertices => (ActualExceptionalIncidence.graph R.π).connectedComponentMk v) := by
    intro hinj
    exact hCH (hinj (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj))
  have hlt := Fintype.card_lt_of_surjective_not_injective _ hsurj hninj
  omega

/-! ### Lemma 6.3 -/

include hP hCH hwH hadj hPC hPH in
/-- **Manuscript Lemma 6.3 (`lem:adjacent-contact-adjoint`, lines 1720–1780).** Let `P` be an
exterior `(-1)`-curve and `C ≠ H` exceptional curves with `H² = -2`, `C · H = 1` (adjacency) and
`P · C = P · H = 1`. Then `b = -C² ≤ 4`, and for `b = 2, 3, 4` the divisors
`A_2 = C + H + P`, `A_3 = C + H + 2P`, `A_4 = C + 2H + 3P` are nef with `A_b² = -K_S · A_b = 1`
and the displayed degree table, and there is a (unique) effective `N` with
`K_S + A_b ∼ Z_b + N` (`Z_2 = 0`, `Z_3 = P`, `Z_4 = H + 2P`), `N ∼ K_S + C + H + P`,
`Supp N ∩ (C ∪ H ∪ P) = ∅`, `N` `A_b`-null, `L · N = L · P - L²`, every exterior `A_b`-null curve
outside the support occurring in `N`, and every exterior component `Q` of `N` satisfying
`0 < L · Q ≤ L · P - L² < L · P`. -/
theorem adjacentContactAdjoint (p : ℕ) [CharP k p] (hp : 0 < p) :
    R.w C ≤ 4 ∧
    ((R.w C = 2 ∧ AdjointDivisorData R P C H (adjDiv R P C H 1 1 1) 0 0 1 ∧
        ∃ N : R.S.WeilDivisor, AdjointRemainder R P C H (adjDiv R P C H 1 1 1) 0 N) ∨
     (R.w C = 3 ∧ AdjointDivisorData R P C H (adjDiv R P C H 1 1 2) 0 1 0 ∧
        ∃ N : R.S.WeilDivisor,
          AdjointRemainder R P C H (adjDiv R P C H 1 1 2) (Finsupp.single P 1) N) ∨
     (R.w C = 4 ∧ AdjointDivisorData R P C H (adjDiv R P C H 1 2 3) 1 0 0 ∧
        ∃ N : R.S.WeilDivisor,
          AdjointRemainder R P C H (adjDiv R P C H 1 2 3)
            (Finsupp.single H.val 1 + Finsupp.single P 2) N)) := by
  refine ⟨weight_le_four R P C H hP hCH hwH hadj hPC hPH, ?_⟩
  rcases weight_cases R P C H hP hCH hwH hadj hPC hPH with hb | hb | hb
  · exact Or.inl ⟨hb, adjointDivisorData_two R P C H hP hwH hadj hPC hPH hb,
      adjointRemainder_two R P C H hP hCH hwH hadj hPC hPH p hp hb⟩
  · exact Or.inr (Or.inl ⟨hb, adjointDivisorData_three R P C H hP hwH hadj hPC hPH hb,
      adjointRemainder_three R P C H hP hCH hwH hadj hPC hPH p hp hb⟩)
  · exact Or.inr (Or.inr ⟨hb, adjointDivisorData_four R P C H hP hwH hadj hPC hPH hb,
      adjointRemainder_four R P C H hP hCH hwH hadj hPC hPH p hp hb⟩)

/-- The strict inequality `L · P - L² < L · P` of the degree bound. -/
theorem Ldeg_sub_Lsq_lt (P : R.S.PrimeCurve) : R.Ldeg P - R.Lsq < R.Ldeg P := by
  linarith [R.Lsq_pos]

/-- The Picard-group form of `N ∼ K_S + C + H + P`. -/
theorem AdjointRemainder.pic_eq {A Z N : R.S.WeilDivisor} (hN : AdjointRemainder R P C H A Z N) :
    R.S.regularWeilPicardClass R.hreg N =
      cartierPicardClass R.S.toScheme R.KS * R.curvePic C.val * R.curvePic H.val * R.curvePic P := by
  rw [picW_eq_of_linearlyEquivalent R hN.class_eq]
  simp only [adjDiv, R.S.regularWeilPicardClass_add, picW_KS, picW_single, mul_assoc]

end Adjacent

end KltDP.Manuscript.S06Adj

namespace KltDP.Manuscript.S06

/-! Re-exports of the headline results of `KltDP.Manuscript.S06Adj` into the manuscript's §6
namespace (the module lives in the sibling namespace `S06Adj` to avoid clashes with the
square-one modules of the same section). -/

alias adjacentContactAdjoint := KltDP.Manuscript.S06Adj.adjacentContactAdjoint
alias remainder_ne_zero_of_contact := KltDP.Manuscript.S06Adj.remainder_ne_zero_of_contact
alias singularPoints_le_seven_of_remainder_zero := KltDP.Manuscript.S06Adj.singularPoints_le_seven_of_remainder_zero

end KltDP.Manuscript.S06

#print axioms KltDP.Manuscript.S06Adj.adjacentContactAdjoint
#print axioms KltDP.Manuscript.S06Adj.remainder_ne_zero_of_contact
#print axioms KltDP.Manuscript.S06Adj.singularPoints_le_seven_of_remainder_zero
#print axioms KltDP.Manuscript.S06Adj.exists_effective_adjoint
#print axioms KltDP.Manuscript.S06Adj.eq_of_effective_of_null
