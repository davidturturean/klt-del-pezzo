import KltDP.Manuscript.S07.FiberDegreeEquality
import KltDP.Geometry.SurfaceRiemannRochProved
import KltDP.Geometry.NefIntersectionSectionVanishing

/-!
# Manuscript Lemma 7.4: a bisection adjoint is zero or one exterior curve

Source: `source/manuscript.tex`, lines 2198–2233, `lem:bisection-adjoint`.

Setting as in Lemma 7.3 (`FiberDegreeEquality.lean`): the ruling `g` with nef fibre class `F`
(`F² = 0`, `K_S · F = -2`), the shortest exterior `(-1)`-curve `P` with `ℓ = L · P`, and
`L · F = 2ℓ`. Let `H ⊂ D` be a *bisection*: an exceptional curve with `F · H = 2`, of weight
`b = w_H` (`H² = -b`).

* `exists_adjoint`: there is an effective Weil divisor `N ∼ K_S + F + H` (Riemann–Roch on `S`:
  `χ(K_S + A) = 1` for `A = F + H`, and `h⁰(-A) = 0` because `(-A) · F = -2 < 0` with `F` nef;
  union: `SurfaceRiemannRochProved.exists_effectiveWeil`,
  `NefIntersectionSectionVanishing.sections_subsingleton`).
* `bisectionAdjoint`: for such `N`, exactly one of: `N = 0`, or `N = R` for an exterior vertical
  `(-1)`-curve `R` disjoint from `H`. In the first case `K_S² = 4 - b` and `H` is the only
  horizontal exceptional curve; in the second `K_S² = 3 - b`, and if another horizontal
  exceptional curve `T` exists then `T` has weight two, `T · H = 0`, `T · R = F · T`, and the fibre
  multiplicity of `R` is one.

The proof follows the manuscript: `N` is vertical (`N · F = 0`), its `L`-degree is
`2ℓ - L² < 2ℓ` while every exterior curve has `L`-degree `≥ ℓ` (Lemma 3.3 (e)), so `N` has at
most one exterior component, with coefficient one; an exterior component in an irreducible fibre
would have `L`-degree `2ℓ`. The remaining part of `N` is an effective divisor supported on
exceptional curves with nonnegative intersection against each of its components, hence zero by
negative definiteness of the exceptional intersection matrix (`exceptional_effective_eq_zero`,
from `ResolutionDatum.A_posDef`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Finset Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S03

universe u

namespace KltDP.Manuscript.S07

variable {k : Type u} [Field k] [IsAlgClosed k] {R : ResolutionDatum k}
  (p : ℕ) [CharP k p] (hp : 0 < p)
  (F : CartierDivisor R.S.toScheme)
  (hF : Positivity.IsNef R.S.structureMorphism (cartierDivisorInvertibleSheaf R.S.toScheme F))
  (hFF : R.S.intersectionPairing R.hreg F F = 0)
  (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)

/-! ### Preliminaries -/

/-- `L · D = Σ_C a_C (L · C)` for every Cartier divisor `D = Σ a_C C` (via the ample numerator
`π^*A = n L`). -/
theorem Lnum_pairing_cartier (D : CartierDivisor R.S.toScheme) :
    R.S.numericalIntersectionBilinForm R.hreg R.Lnum (NefNullCurveNegativeSquare.cartierClass R.S D)
      = (R.S.cartierToWeilHom D).sum fun C a => (a : ℚ) * R.Ldeg C := by
  obtain ⟨n, hn, A, -, hLw⟩ := R.exists_ample_numerator
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hclass := cartierClass_pullback_eq R n A hLw hn
  have hdeg := Ldeg_mul_eq_intersectionNumber R n A hLw hn
  have hpair : (n : ℚ) * R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S D)
      = (((R.S.cartierToWeilHom D).sum fun C a =>
          a * C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) : ℤ) : ℚ) := by
    rw [← LinearMap.BilinForm.smul_left, ← hclass,
      NefNullCurveNegativeSquare.cartierClass_pairing,
      R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_eq_weil_sum_right R.hreg]
  have hsum : (n : ℚ) * ((R.S.cartierToWeilHom D).sum fun C a => (a : ℚ) * R.Ldeg C)
      = (((R.S.cartierToWeilHom D).sum fun C a =>
          a * C.intersectionNumber (DominantCartierPullback.pullbackHom R.π A) : ℤ) : ℚ) := by
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← hdeg C]
    ring
  exact mul_left_cancel₀ hn'.ne' (hpair.trans hsum.symm)

/-- The prime Cartier divisor of `C` is the Cartier divisor of the Weil divisor `C`. -/
theorem primeCurveCartier_eq_symm_single (C : R.S.PrimeCurve) :
    R.S.primeCurveCartier R.hreg C =
      (R.S.regularCartierWeilEquiv R.hreg).symm (Finsupp.single C 1) := by
  apply (R.S.regularCartierWeilEquiv R.hreg).injective
  rw [AddEquiv.apply_symm_apply, R.S.regularCartierWeilEquiv_apply,
    R.S.cartierToWeilHom_primeCurveCartier R.hreg]

/-- The Weil divisor of the Cartier divisor of a Weil divisor. -/
theorem cartierToWeilHom_symm (Z : R.S.WeilDivisor) :
    R.S.cartierToWeilHom ((R.S.regularCartierWeilEquiv R.hreg).symm Z) = Z :=
  (R.S.regularCartierWeilEquiv R.hreg).apply_symm_apply Z

/-- A sum over the exceptional vertices of a divisor supported on exceptional curves is the sum over
its support. -/
theorem sum_vertices_eq_sum_support (Z : R.S.WeilDivisor)
    (hexc : ∀ C, Z C ≠ 0 → IsExceptionalCurve R.π C) (C : R.S.PrimeCurve) :
    ∑ j : R.Vertices, (Z j.val : ℚ) *
        ((C.intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℤ) : ℚ) =
      ∑ C' ∈ Z.support, (Z C' : ℚ) *
        ((C.intersectionNumber (R.S.primeCurveCartier R.hreg C') : ℤ) : ℚ) := by
  classical
  have h1 : ∑ j ∈ (Finset.univ : Finset R.Vertices).filter (fun j => j.val ∈ Z.support),
      (Z j.val : ℚ) * ((C.intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℤ) : ℚ) =
      ∑ j : R.Vertices, (Z j.val : ℚ) *
        ((C.intersectionNumber (R.S.primeCurveCartier R.hreg j.val) : ℤ) : ℚ) := by
    apply Finset.sum_filter_of_ne
    intro j _ hne
    refine Classical.byContradiction fun h => ?_
    apply hne
    rw [Finsupp.not_mem_support_iff.mp h, Int.cast_zero, zero_mul]
  rw [← h1]
  refine Finset.sum_bij (fun (j : R.Vertices) _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro j _ j' _ h
    exact Subtype.ext h
  · intro C' hC'
    exact ⟨⟨C', hexc C' (Finsupp.mem_support_iff.mp hC')⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'⟩, rfl⟩
  · intro j _
    rfl

/-- **Negative definiteness of the exceptional lattice** (manuscript lines 2219–2226): an effective
divisor `Z` supported on exceptional curves with `Z · C ≥ 0` for every component `C` of `Z` is
zero. (`z^T M z = Σ_C z_C (Z · C) ≥ 0` while `M = -A` is negative definite.) -/
theorem exceptional_effective_eq_zero (Z : R.S.WeilDivisor) (hZ : EffectiveDivisor Z)
    (hexc : ∀ C, Z C ≠ 0 → IsExceptionalCurve R.π C)
    (hnn : ∀ C, Z C ≠ 0 →
      0 ≤ C.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm Z)) :
    Z = 0 := by
  classical
  obtain ⟨Zc, hZc_def⟩ : ∃ Zc, Zc = (R.S.regularCartierWeilEquiv R.hreg).symm Z := ⟨_, rfl⟩
  have hZc : R.S.cartierToWeilHom Zc = Z := by
    rw [hZc_def]
    exact (R.S.regularCartierWeilEquiv R.hreg).apply_symm_apply Z
  obtain ⟨z, hz⟩ : ∃ z : R.Vertices → ℚ, z = fun i => (Z i.val : ℚ) := ⟨_, rfl⟩
  -- `(M z)_i = D_i · Z`
  have hMz : ∀ i : R.Vertices, (R.M *ᵥ z) i = (i.val.intersectionNumber Zc : ℚ) := by
    intro i
    have h := R.S.intersectionNumber_eq_weil_sum R.hreg i.val Zc
    rw [hZc] at h
    have h' : ((i.val.intersectionNumber Zc : ℤ) : ℚ) = ∑ C' ∈ Z.support, (Z C' : ℚ) *
        ((i.val.intersectionNumber (R.S.primeCurveCartier R.hreg C') : ℤ) : ℚ) := by
      rw [h]
      unfold Finsupp.sum
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun C' _ => by rw [Int.cast_mul]; rfl
    rw [h', ← sum_vertices_eq_sum_support Z hexc i.val]
    simp only [Matrix.mulVec, dotProduct, hz]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    exact congrArg (fun n : ℤ => (n : ℚ))
      (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg
        i.val j.val)
  -- `z ⬝ (M z) ≥ 0`
  have hdot : 0 ≤ dotProduct z (R.M *ᵥ z) := by
    apply Finset.sum_nonneg
    intro i _
    rw [hMz i, hz]
    by_cases h0 : Z i.val = 0
    · simp [h0]
    · have h1 : (0 : ℚ) ≤ (Z i.val : ℚ) := by exact_mod_cast hZ i.val
      have h2 : (0 : ℚ) ≤ (i.val.intersectionNumber Zc : ℚ) := by
        rw [hZc_def]; exact_mod_cast hnn i.val h0
      exact mul_nonneg h1 h2
  -- hence `z = 0` by positive definiteness of `A = -M`
  have hz0 : z = 0 := by
    refine Classical.byContradiction fun hne => ?_
    have hpos : 0 < dotProduct z (R.A *ᵥ z) := by
      simpa only [star_trivial] using R.A_posDef.2 z hne
    have hA : R.A *ᵥ z = -(R.M *ᵥ z) := by
      show (-R.M) *ᵥ z = _
      rw [Matrix.neg_mulVec]
    rw [hA, dotProduct_neg] at hpos
    linarith
  -- hence `Z = 0`
  ext C
  by_cases h0 : Z C = 0
  · rw [h0]; rfl
  · have := congrFun hz0 ⟨C, hexc C h0⟩
    rw [hz] at this
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    exact absurd this h0

/-! ### The adjoint divisor `N ∼ K_S + F + H` -/

/-- The adjoint Cartier divisor `K_S + F + H`. -/
def adjointCartier (H : R.S.PrimeCurve) : CartierDivisor R.S.toScheme :=
  R.KS + F + R.S.primeCurveCartier R.hreg H

include p hp hF hFF hKF in
/-- **Manuscript Lemma 7.4, existence** (lines 2214–2217): for a bisection `H` (`F · H = 2`) there is
an effective divisor `N ∼ K_S + F + H`. Riemann–Roch with `A = F + H`: `(K_S + A) · A = 0`, so
`χ(K_S + A) = χ(O_S) = 1`; and `h⁰(-A) = 0` since `(-A) · F = -2 < 0` with `F` nef. -/
theorem exists_adjoint (H : R.Vertices) (hHF : H.val.intersectionNumber F = 2) :
    ∃ Z : R.S.WeilDivisor, EffectiveDivisor Z ∧
      R.S.LinearlyEquivalent Z (R.S.cartierToWeilHom (adjointCartier F H.val)) := by
  have hsymmK : (R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS) = R.KS :=
    (R.S.regularCartierWeilEquiv R.hreg).symm_apply_apply R.KS
  have hsymmD : (R.S.regularCartierWeilEquiv R.hreg).symm
      (R.S.cartierToWeilHom (adjointCartier F H.val)) = adjointCartier F H.val :=
    (R.S.regularCartierWeilEquiv R.hreg).symm_apply_apply _
  have hsymmKD : (R.S.regularCartierWeilEquiv R.hreg).symm
      (R.S.cartierToWeilHom R.KS - R.S.cartierToWeilHom (adjointCartier F H.val))
      = -(F + R.S.primeCurveCartier R.hreg H.val) := by
    rw [map_sub, hsymmK, hsymmD]
    simp only [adjointCartier]
    abel
  have hsymmDK : (R.S.regularCartierWeilEquiv R.hreg).symm
      (R.S.cartierToWeilHom (adjointCartier F H.val) - R.S.cartierToWeilHom R.KS)
      = F + R.S.primeCurveCartier R.hreg H.val := by
    rw [map_sub, hsymmK, hsymmD]
    simp only [adjointCartier]
    abel
  -- the canonical divisor
  have hK : SurfaceRiemannRochSource.IsCanonical R.S R.hreg (R.S.cartierToWeilHom R.KS) := by
    change Nonempty (cartierDivisorModule R.S.toScheme
      ((R.S.regularCartierWeilEquiv R.hreg).symm (R.S.cartierToWeilHom R.KS)) ≅ _)
    rw [hsymmK]
    exact ⟨R.eKS⟩
  -- `h⁰(-A) = 0`
  have hHcF : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg H.val) F = 2 := by
    rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_primeCurve R.hreg]
    exact hHF
  have hneg : R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm
      (R.S.cartierToWeilHom R.KS - R.S.cartierToWeilHom (adjointCartier F H.val))) F < 0 := by
    rw [hsymmKD, R.S.intersectionPairing_neg_left R.hreg, R.S.intersectionPairing_add_left R.hreg,
      hFF, hHcF]
    norm_num
  have hvanish := NefIntersectionSectionVanishing.sections_subsingleton R.S R.hreg
    (R.S.cartierToWeilHom R.KS - R.S.cartierToWeilHom (adjointCartier F H.val)) F hF hneg
  -- `χ(K_S + A) = 1`
  have hKH : ((H.val.intersectionNumber R.KS : ℤ) : ℚ) = R.w H - 2 := R.Kdeg_exceptional H
  have hHH : ((H.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℤ) : ℚ) = -R.w H :=
    selfIntersection_eq_neg_w H
  have hchi := (R.hmin.picard_and_structure_invariants_of_kltDelPezzo R.hDP R.hrank p hp).2.2.1
  have hpair : R.S.intersectionPairing R.hreg (adjointCartier F H.val)
      (F + R.S.primeCurveCartier R.hreg H.val) = 0 := by
    have h : (R.S.intersectionPairing R.hreg (adjointCartier F H.val)
        (F + R.S.primeCurveCartier R.hreg H.val) : ℚ) = 0 := by
      simp only [adjointCartier]
      rw [R.S.intersectionPairing_add_right R.hreg, R.S.intersectionPairing_add_left R.hreg,
        R.S.intersectionPairing_add_left R.hreg, R.S.intersectionPairing_add_left R.hreg,
        R.S.intersectionPairing_add_left R.hreg, hKF, hFF, hHcF,
        R.S.intersectionPairing_primeCurve R.hreg R.KS, R.S.intersectionPairing_primeCurve R.hreg F,
        R.S.intersectionPairing_primeCurve R.hreg, hHF]
      push_cast
      rw [hKH, hHH]
      ring
    exact_mod_cast h
  have hpos : 0 < SurfaceRiemannRochSource.rrNumber R.S R.hreg
      (R.S.cartierToWeilHom (adjointCartier F H.val)) (R.S.cartierToWeilHom R.KS) := by
    unfold SurfaceRiemannRochSource.rrNumber SurfaceRiemannRochSource.arithmeticGenus
    rw [hchi, hsymmD, hsymmDK, hpair]
    norm_num
  exact SurfaceRiemannRochProved.exists_effectiveWeil R.S R.hreg _ _ hK hvanish hpos

/-! ### Intersection numbers of the adjoint divisor -/

section Adjoint

variable (H : R.Vertices) (Z : R.S.WeilDivisor)
  (hZD : R.S.LinearlyEquivalent Z (R.S.cartierToWeilHom (adjointCartier F H.val)))

include hZD in
/-- `N` and `K_S + F + H` have the same Picard class. -/
theorem adjoint_class_eq :
    cartierPicardClass R.S.toScheme ((R.S.regularCartierWeilEquiv R.hreg).symm Z) =
      cartierPicardClass R.S.toScheme (adjointCartier F H.val) := by
  have hp1 := (R.S.regularWeilPicardClass_eq_iff R.hreg Z _).mpr hZD
  have h1 := R.S.regularWeilClassPicardEquiv_representative R.hreg Z
  have h2 := R.S.regularWeilClassPicardEquiv_representative R.hreg
    (R.S.cartierToWeilHom (adjointCartier F H.val))
  have h3 : (R.S.regularCartierWeilEquiv R.hreg).symm
      (R.S.cartierToWeilHom (adjointCartier F H.val)) = adjointCartier F H.val :=
    (R.S.regularCartierWeilEquiv R.hreg).symm_apply_apply _
  rw [h3] at h2
  exact h1.symm.trans (hp1.trans h2)

include hZD in
/-- `N · C = K_S · C + F · C + H · C` for every prime curve `C`. -/
theorem adjoint_intersectionNumber (C : R.S.PrimeCurve) :
    C.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm Z) =
      C.intersectionNumber R.KS + C.intersectionNumber F +
        C.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) := by
  rw [C.intersectionNumber_eq_of_cartierPicardClass_eq _ _ (adjoint_class_eq F H Z hZD)]
  simp only [adjointCartier]
  rw [C.intersectionNumber_add, C.intersectionNumber_add]

/-- `N · C = Σ_{C'} z_{C'} (C · C')`. -/
theorem adjoint_weil_sum (C : R.S.PrimeCurve) :
    C.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm Z) =
      Z.sum fun C' a => a * C.intersectionNumber (R.S.primeCurveCartier R.hreg C') := by
  have h := R.S.intersectionNumber_eq_weil_sum R.hreg C ((R.S.regularCartierWeilEquiv R.hreg).symm Z)
  rw [cartierToWeilHom_symm] at h
  exact h

include hZD in
/-- `K_S · N = K_S · (K_S + F + H)`. -/
theorem adjoint_KS_pairing :
    R.S.intersectionPairing R.hreg R.KS ((R.S.regularCartierWeilEquiv R.hreg).symm Z) =
      R.S.intersectionPairing R.hreg R.KS R.KS + R.S.intersectionPairing R.hreg R.KS F +
        R.S.intersectionPairing R.hreg R.KS (R.S.primeCurveCartier R.hreg H.val) := by
  rw [R.S.intersectionPairing_eq_of_class_eq_right R.hreg R.KS _ _ (adjoint_class_eq F H Z hZD)]
  simp only [adjointCartier]
  rw [R.S.intersectionPairing_add_right R.hreg, R.S.intersectionPairing_add_right R.hreg]

include hF hFF hKF hZD in
/-- `N` is vertical (`N · F = 0`, so every component of `N` has `F · C = 0`). -/
theorem adjoint_vertical (hHF : H.val.intersectionNumber F = 2) (hZ : EffectiveDivisor Z)
    (C : R.S.PrimeCurve) (hC : Z C ≠ 0) : C.intersectionNumber F = 0 := by
  classical
  have hZF : R.S.intersectionPairing R.hreg ((R.S.regularCartierWeilEquiv R.hreg).symm Z) F = 0 := by
    rw [R.S.intersectionPairing_symm R.hreg,
      R.S.intersectionPairing_eq_of_class_eq_right R.hreg F _ _ (adjoint_class_eq F H Z hZD)]
    simp only [adjointCartier]
    rw [R.S.intersectionPairing_add_right R.hreg, R.S.intersectionPairing_add_right R.hreg,
      R.S.intersectionPairing_symm R.hreg F R.KS, hKF, hFF, R.S.intersectionPairing_primeCurve R.hreg,
      hHF]
    norm_num
  rw [R.S.intersectionPairing_eq_weil_sum_right R.hreg, cartierToWeilHom_symm] at hZF
  unfold Finsupp.sum at hZF
  have hnn : ∀ C' ∈ Z.support, 0 ≤ Z C' * C'.intersectionNumber F := fun C' _ =>
    mul_nonneg (hZ C') (intersectionNumber_nonneg R F hF C')
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hZF C (Finsupp.mem_support_iff.mpr hC)
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hC
  · exact h

variable (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
  (hL : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
    (NefNullCurveNegativeSquare.cartierClass R.S F) = 2 * R.Ldeg P)

include hZD hL in
/-- `L · N = 2ℓ - L²` (manuscript line 2218). -/
theorem adjoint_Ldeg_sum :
    (Z.sum fun C a => (a : ℚ) * R.Ldeg C) = 2 * R.Ldeg P - R.Lsq := by
  have h1 := Lnum_pairing_cartier ((R.S.regularCartierWeilEquiv R.hreg).symm Z)
  rw [cartierToWeilHom_symm] at h1
  rw [← h1]
  have hcls : NefNullCurveNegativeSquare.cartierClass R.S ((R.S.regularCartierWeilEquiv R.hreg).symm Z)
      = NefNullCurveNegativeSquare.cartierClass R.S (adjointCartier F H.val) := by
    show R.S.picardNumericalMap (Additive.ofMul (cartierPicardClass R.S.toScheme _)) =
      R.S.picardNumericalMap (Additive.ofMul (cartierPicardClass R.S.toScheme _))
    rw [adjoint_class_eq F H Z hZD]
  rw [hcls]
  have hsplit : NefNullCurveNegativeSquare.cartierClass R.S (adjointCartier F H.val) =
      NefNullCurveNegativeSquare.cartierClass R.S R.KS + NefNullCurveNegativeSquare.cartierClass R.S F +
        NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg H.val) := by
    show R.S.picardNumericalMap (cartierPicardHom R.S.toScheme (R.KS + F + _)) = _
    rw [map_add, map_add, map_add, map_add]
    rfl
  rw [hsplit, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, hL]
  have hK : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S R.KS) = -R.Lsq := by
    rw [← R.Knum_pairing_Lnum]
    exact (R.S.numericalIntersectionBilinForm_isSymm R.hreg).eq R.Lnum R.Knum
  have hH : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (NefNullCurveNegativeSquare.cartierClass R.S (R.S.primeCurveCartier R.hreg H.val)) = 0 := by
    change R.S.numericalIntersectionBilinForm R.hreg R.Lnum
      (DisjointNegativeCurvesRank.curveClass R.S R.hreg H.val) = 0
    rw [KltDP.Manuscript.S02.Lnum_pairing_curveClass, R.Ldeg_exceptional H]
  rw [hK, hH]
  ring

include hZD hrho hP hL in
/-- **At most one exterior component** (manuscript lines 2218–2220): the exterior components of
`N` have total multiplicity `< 2` (each has `L`-degree `≥ ℓ` while `L · N = 2ℓ - L² < 2ℓ`), so
either `N` is supported on exceptional curves, or `N` has exactly one exterior component, with
multiplicity one. -/
theorem adjoint_exterior_dichotomy (hZ : EffectiveDivisor Z) :
    (∀ C, Z C ≠ 0 → IsExceptionalCurve R.π C) ∨
      ∃ R' : R.S.PrimeCurve, Z R' = 1 ∧ ¬ IsExceptionalCurve R.π R' ∧
        ∀ C, Z C ≠ 0 → ¬ IsExceptionalCurve R.π C → C = R' := by
  classical
  have hℓ : 0 < R.Ldeg P := KltDP.Manuscript.S02.Ldeg_pos R P hP.1.2
  have hv := R.Lsq_pos
  have hsum := adjoint_Ldeg_sum F H Z hZD P hL
  obtain ⟨Zext, hZext⟩ : ∃ Zext : Finset R.S.PrimeCurve,
      Zext = Z.support.filter fun C => ¬ IsExceptionalCurve R.π C := ⟨_, rfl⟩
  have hmemZ : ∀ C, C ∈ Zext ↔ Z C ≠ 0 ∧ ¬ IsExceptionalCurve R.π C := fun C => by
    rw [hZext, Finset.mem_filter, Finsupp.mem_support_iff]
  have hsplit := Finset.sum_filter_add_sum_filter_not Z.support
    (fun C => ¬ IsExceptionalCurve R.π C) (fun C => (Z C : ℚ) * R.Ldeg C)
  simp only [not_not] at hsplit
  have hexc0 : ∑ C ∈ Z.support.filter (fun C => IsExceptionalCurve R.π C), (Z C : ℚ) * R.Ldeg C = 0 :=
    Finset.sum_eq_zero fun C hC => by
      rw [R.Ldeg_exceptional ⟨C, (Finset.mem_filter.mp hC).2⟩, mul_zero]
  unfold Finsupp.sum at hsum
  rw [← hsplit, hexc0, add_zero, ← hZext] at hsum
  have hone : ∀ C ∈ Zext, (1 : ℚ) ≤ (Z C : ℚ) := fun C hC => by
    have h1 : 0 < Z C := lt_of_le_of_ne (hZ C) (Ne.symm ((hmemZ C).mp hC).1)
    exact_mod_cast h1
  have hge : ∀ C ∈ Zext, R.Ldeg P ≤ R.Ldeg C := fun C hC =>
    Ldeg_ge_of_not_exceptional R hrho P hP C ((hmemZ C).mp hC).2
  have hlow : (∑ C ∈ Zext, (Z C : ℚ)) * R.Ldeg P ≤ ∑ C ∈ Zext, (Z C : ℚ) * R.Ldeg C := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun C hC =>
      mul_le_mul_of_nonneg_left (hge C hC) (by linarith [hone C hC])
  have hlt : ∑ C ∈ Zext, (Z C : ℚ) < 2 := by
    have : (∑ C ∈ Zext, (Z C : ℚ)) * R.Ldeg P < 2 * R.Ldeg P := by linarith
    exact lt_of_mul_lt_mul_right this hℓ.le
  have hcard : (Zext.card : ℚ) ≤ ∑ C ∈ Zext, (Z C : ℚ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun C hC => by simpa using hone C hC
  have hcard' : Zext.card ≤ 1 := by
    have h2 : (Zext.card : ℚ) < 2 := lt_of_le_of_lt hcard hlt
    have h3 : Zext.card < 2 := by exact_mod_cast h2
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard' with h0 | h1
  · left
    rw [Finset.card_eq_zero] at h0
    intro C hC
    refine Classical.byContradiction fun hex => ?_
    have : C ∈ Zext := (hmemZ C).mpr ⟨hC, hex⟩
    rw [h0] at this
    exact Finset.not_mem_empty C this
  · right
    obtain ⟨R', hR'⟩ := Finset.card_eq_one.mp h1
    have hmem : R' ∈ Zext := by rw [hR']; exact Finset.mem_singleton_self R'
    obtain ⟨hsupp, hex⟩ := (hmemZ R').mp hmem
    rw [hR', Finset.sum_singleton] at hlt
    have h1' := hone R' hmem
    refine ⟨R', ?_, hex, fun C hC hCex => ?_⟩
    · have hlt' : Z R' < 2 := by exact_mod_cast hlt
      have hge' : (1 : ℤ) ≤ Z R' := by exact_mod_cast h1'
      omega
    · have : C ∈ Zext := (hmemZ C).mpr ⟨hC, hCex⟩
      rw [hR', Finset.mem_singleton] at this
      exact this

end Adjoint

/-! ### Manuscript Lemma 7.4 -/

section Main

variable (hrho : 2 < R.S.picardRank) (P : R.S.PrimeCurve) (hP : R.IsShortestExteriorMinusOne P)
  (hL : R.S.numericalIntersectionBilinForm R.hreg R.Lnum
    (NefNullCurveNegativeSquare.cartierClass R.S F) = 2 * R.Ldeg P)

include p hp hF hFF hKF hg e hrho hP hL in
/-- **Manuscript Lemma 7.4** (`lem:bisection-adjoint`, lines 2198–2233). Let `H ⊂ D` be a
bisection (`F · H = 2`) of weight `b = w_H`. There is an effective divisor `N ∼ K_S + F + H`, and
exactly one of the following holds:

* `N = 0`; then `K_S² = 4 - b` and `H` is the only horizontal exceptional curve;
* `N = R` for an exterior vertical `(-1)`-curve `R` disjoint from `H`; then `K_S² = 3 - b`, and
  every other horizontal exceptional curve `T` satisfies `T² = -2` (`w_T = 2`), `T · H = 0`,
  `T · R = F · T`, and the fibre multiplicity of `R` is one. -/
theorem bisectionAdjoint [IsProper g] [Surjective g] (H : R.Vertices)
    (hHF : H.val.intersectionNumber F = 2) :
    ∃ Z : R.S.WeilDivisor, EffectiveDivisor Z ∧
      R.S.LinearlyEquivalent Z (R.S.cartierToWeilHom (adjointCartier F H.val)) ∧
      ((Z = 0 ∧ (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) = 4 - R.w H ∧
          ∀ T : R.Vertices, T ≠ H → T.val.intersectionNumber F = 0) ∨
        ∃ R' : R.S.PrimeCurve, Z = Finsupp.single R' 1 ∧ ¬ IsExceptionalCurve R.π R' ∧
          IsMinusOneCurve R.hreg R' ∧ R'.intersectionNumber F = 0 ∧
          Disjoint (R' : Set R.S.toScheme) (H.val : Set R.S.toScheme) ∧
          (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) = 3 - R.w H ∧
          ∀ T : R.Vertices, T ≠ H → T.val.intersectionNumber F ≠ 0 →
            R.w T = 2 ∧ T.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 0 ∧
            T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') = T.val.intersectionNumber F ∧
            ∀ (t : projectiveSpace k 1) (E : CartierDivisor R.S.toScheme),
              IsFiberDivisor F g t E → InFiber g t R' → R.S.cartierToWeilHom E R' = 1) := by
  classical
  obtain ⟨Z, hZ, hZD⟩ := exists_adjoint p hp F hF hFF hKF H hHF
  refine ⟨Z, hZ, hZD, ?_⟩
  -- the general facts about `N`
  have hCZ := adjoint_intersectionNumber F H Z hZD
  have hsum := adjoint_weil_sum Z
  have hvert := adjoint_vertical F hF hFF hKF H Z hZD hHF hZ
  have hKZ := adjoint_KS_pairing F H Z hZD
  have hKH : ((H.val.intersectionNumber R.KS : ℤ) : ℚ) = R.w H - 2 := R.Kdeg_exceptional H
  have hHH : ((H.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℤ) : ℚ) = -R.w H :=
    selfIntersection_eq_neg_w H
  have hKSH : (R.S.intersectionPairing R.hreg R.KS (R.S.primeCurveCartier R.hreg H.val) : ℚ)
      = R.w H - 2 := by
    rw [R.S.intersectionPairing_primeCurve R.hreg]; exact hKH
  -- components of `N` are distinct from `H` (they are vertical)
  have hneH : ∀ C, Z C ≠ 0 → C ≠ H.val := fun C hC heq => by
    have := hvert C hC
    rw [heq, hHF] at this
    exact absurd this (by norm_num)
  -- a horizontal exceptional curve `T ≠ H`
  have hTpos : ∀ T : R.Vertices, T.val.intersectionNumber F ≠ 0 → 0 < T.val.intersectionNumber F :=
    fun T hT => lt_of_le_of_ne (intersectionNumber_nonneg R F hF T.val) (Ne.symm hT)
  rcases adjoint_exterior_dichotomy F H Z hZD hrho P hP hL hZ with hexc | ⟨R', hZR', hR'ex, huniq⟩
  · -- **Case `N = 0`**
    left
    have hZ0 : Z = 0 := by
      apply exceptional_effective_eq_zero Z hZ hexc
      intro C hC
      rw [hCZ C, hvert C hC, add_zero]
      have h1 : 0 ≤ C.intersectionNumber R.KS := Kdeg_exceptional_nonneg ⟨C, hexc C hC⟩
      have h2 : 0 ≤ C.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) := inter_nonneg (hneH C hC)
      omega
    have hZc0 : (R.S.regularCartierWeilEquiv R.hreg).symm Z = 0 := by rw [hZ0, map_zero]
    refine ⟨hZ0, ?_, ?_⟩
    · rw [hZc0, R.S.intersectionPairing_zero_right R.hreg] at hKZ
      have h := congrArg (Int.cast (R := ℚ)) hKZ
      push_cast at h
      rw [hKSH] at h
      have hKF' : ((R.S.intersectionPairing R.hreg R.KS F : ℤ) : ℚ) = -2 := by exact_mod_cast hKF
      linarith
    · intro T hTH
      refine Classical.byContradiction fun hTF => ?_
      have h1 := hCZ T.val
      rw [hZc0, T.val.intersectionNumber_zero] at h1
      have h2 := hTpos T hTF
      have h3 : 0 ≤ T.val.intersectionNumber R.KS := Kdeg_exceptional_nonneg T
      have h4 : 0 ≤ T.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) :=
        inter_nonneg (fun h => hTH (Subtype.ext h))
      omega
  · -- **Case `N = R + Z'`**
    right
    have hR'supp : Z R' ≠ 0 := by rw [hZR']; exact one_ne_zero
    have hR'F : R'.intersectionNumber F = 0 := hvert R' hR'supp
    -- the fibre of `R`
    obtain ⟨t, ht, hR't⟩ := exists_vertical_of_intersectionNumber_eq_zero R F g hg e R' hR'F
    obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t ht
    -- it is reducible: an irreducible fibre component has `L`-degree `2ℓ`
    have hLR' : R.Ldeg R' ≤ 2 * R.Ldeg P - R.Lsq := by
      have h := adjoint_Ldeg_sum F H Z hZD P hL
      unfold Finsupp.sum at h
      rw [← h]
      have hterm : (Z R' : ℚ) * R.Ldeg R' = R.Ldeg R' := by rw [hZR']; simp
      rw [← hterm]
      exact Finset.single_le_sum (f := fun C => (Z C : ℚ) * R.Ldeg C)
        (fun C _ => mul_nonneg (by exact_mod_cast hZ C) (R.Ldeg_nonneg C))
        (Finsupp.mem_support_iff.mpr hR'supp)
    have hred : ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C' := by
      refine Classical.byContradiction fun hnot => ?_
      push_neg at hnot
      have hirr : ∀ C', InFiber g t C' → C' = R' := fun C' hC' => hnot C' R' hC' hR't
      have hweil := (irreducibleFiber_component R F hFF hKF g hE R' hR't hirr).1
      have h := Lnum_pairing_fiberDivisor F g hE
      rw [hL, hweil, Finsupp.sum_single_index (by simp)] at h
      have hv := R.Lsq_pos
      have : R.Ldeg R' = 2 * R.Ldeg P := by
        have h' : 2 * R.Ldeg P = ((1 : ℤ) : ℚ) * R.Ldeg R' := h
        simpa using h'.symm
      linarith
    have hconn := fiber_isConnected R p hp F hFF hKF g hg e t
    obtain ⟨hR'm1, hKR'⟩ := exterior_component_isMinusOne p hp F hFF hKF g hg e hE hred R' hR't hR'ex
    have hR'sq := hR'm1.selfIntersection
    -- `N` is disjoint from `H`: `N · H = 0` with nonnegative terms
    have hNH : H.val.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm Z) = 0 := by
      rw [hCZ H.val, hHF]
      have h : H.val.intersectionNumber R.KS +
          H.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = -2 := by
        have h' : ((H.val.intersectionNumber R.KS : ℤ) : ℚ) +
            ((H.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) : ℤ) : ℚ) = -2 := by
          rw [hKH, hHH]; ring
        exact_mod_cast h'
      omega
    have hHC : ∀ C, Z C ≠ 0 → H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
      intro C hC
      rw [hsum H.val] at hNH
      unfold Finsupp.sum at hNH
      have hnn : ∀ C' ∈ Z.support, 0 ≤ Z C' * H.val.intersectionNumber (R.S.primeCurveCartier R.hreg C') :=
        fun C' hC' => mul_nonneg (hZ C')
          (inter_nonneg (Ne.symm (hneH C' (Finsupp.mem_support_iff.mp hC'))))
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hNH C (Finsupp.mem_support_iff.mpr hC)
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hC
      · exact h
    have hR'H : R'.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 0 := by
      rw [inter_symm]; exact hHC R' hR'supp
    have hdisj : Disjoint (R' : Set R.S.toScheme) (H.val : Set R.S.toScheme) := by
      have hne : R' ≠ H.val := hneH R' hR'supp
      have h := PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
        R.S R.hreg R' H.val hne
      rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber] at h
      exact h.mp hR'H
    -- `N · R = -1`, so the other components of `N` are disjoint from `R`
    have hNR : R'.intersectionNumber ((R.S.regularCartierWeilEquiv R.hreg).symm Z) = -1 := by
      rw [hCZ R', hR'F, hR'H]
      change R.Kdeg R' + 0 + 0 = -1
      rw [hKR']; norm_num
    have hR'C : ∀ C, Z C ≠ 0 → C ≠ R' → R'.intersectionNumber (R.S.primeCurveCartier R.hreg C) = 0 := by
      intro C hC hCR'
      rw [hsum R'] at hNR
      unfold Finsupp.sum at hNR
      have hmem : R' ∈ Z.support := Finsupp.mem_support_iff.mpr hR'supp
      rw [← Finset.add_sum_erase _ _ hmem] at hNR
      dsimp only at hNR
      rw [hZR', one_mul] at hNR
      change R'.selfIntersectionNumber R.hreg + _ = -1 at hNR
      rw [hR'sq] at hNR
      have hrest : ∑ C' ∈ Z.support.erase R', Z C' * R'.intersectionNumber (R.S.primeCurveCartier R.hreg C') = 0 := by
        linarith
      have hnn : ∀ C' ∈ Z.support.erase R', 0 ≤ Z C' * R'.intersectionNumber (R.S.primeCurveCartier R.hreg C') :=
        fun C' hC' => mul_nonneg (hZ C') (inter_nonneg (Ne.symm (Finset.mem_erase.mp hC').1))
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hrest C
        (Finset.mem_erase.mpr ⟨hCR', Finsupp.mem_support_iff.mpr hC⟩)
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hC
      · exact h
    -- the exceptional part `Z' = N - R` is zero
    have hexcC : ∀ C, Z C ≠ 0 → C ≠ R' → IsExceptionalCurve R.π C := fun C hC hCR' =>
      Classical.byContradiction fun hex => hCR' (huniq C hC hex)
    have hZ' : Z - Finsupp.single R' 1 = 0 := by
      apply exceptional_effective_eq_zero (Z - Finsupp.single R' 1)
      · intro C
        rw [Finsupp.sub_apply, Finsupp.single_apply]
        split_ifs with h
        · rw [← h, hZR']; norm_num
        · rw [sub_zero]; exact hZ C
      · intro C hC
        rw [Finsupp.sub_apply, Finsupp.single_apply] at hC
        split_ifs at hC with h
        · rw [← h, hZR'] at hC; exact absurd (sub_self _) hC
        · rw [sub_zero] at hC
          exact hexcC C hC (Ne.symm h)
      · intro C hC
        rw [Finsupp.sub_apply, Finsupp.single_apply] at hC
        split_ifs at hC with h
        · rw [← h, hZR'] at hC; exact absurd (sub_self _) hC
        · rw [sub_zero] at hC
          have hCR' : C ≠ R' := Ne.symm h
          rw [map_sub, ← primeCurveCartier_eq_symm_single, sub_eq_add_neg,
            C.intersectionNumber_add, C.intersectionNumber_neg, hCZ C, hvert C hC,
            inter_symm C R', hR'C C hC hCR', inter_symm C H.val, hHC C hC]
          have := Kdeg_exceptional_nonneg ⟨C, hexcC C hC hCR'⟩
          change 0 ≤ C.intersectionNumber R.KS at this
          omega
    have hZeq : Z = Finsupp.single R' 1 := sub_eq_zero.mp hZ'
    -- `K_S · N = K_S · R = -1`
    have hKZR : R.S.intersectionPairing R.hreg R.KS ((R.S.regularCartierWeilEquiv R.hreg).symm Z) = -1 := by
      rw [R.S.intersectionPairing_symm R.hreg, R.S.intersectionPairing_eq_weil_sum_right R.hreg,
        cartierToWeilHom_symm, hZeq, Finsupp.sum_single_index (by simp), one_mul]
      exact hKR'
    have hKsq : (R.S.intersectionPairing R.hreg R.KS R.KS : ℚ) = 3 - R.w H := by
      rw [hKZR] at hKZ
      have h := congrArg (Int.cast (R := ℚ)) hKZ
      push_cast at h
      rw [hKSH] at h
      have hKF' : ((R.S.intersectionPairing R.hreg R.KS F : ℤ) : ℚ) = -2 := by exact_mod_cast hKF
      linarith
    refine ⟨R', hZeq, hR'ex, hR'm1, hR'F, hdisj, hKsq, ?_⟩
    -- another horizontal exceptional curve `T`
    intro T hTH hTF
    have hTF' := hTpos T hTF
    have hTR : T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') =
        T.val.intersectionNumber R.KS + T.val.intersectionNumber F +
          T.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) := by
      rw [← hCZ T.val, hsum T.val, hZeq, Finsupp.sum_single_index (by simp), one_mul]
    have hk : 0 ≤ T.val.intersectionNumber R.KS := Kdeg_exceptional_nonneg T
    have hh : 0 ≤ T.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) :=
      inter_nonneg (fun h => hTH (Subtype.ext h))
    -- the fibre equation: `F · T ≥ μ_R (R · T)` for every fibre divisor of the fibre of `R`
    have hfib : ∀ (t' : projectiveSpace k 1) (E' : CartierDivisor R.S.toScheme),
        IsFiberDivisor F g t' E' → InFiber g t' R' →
        R.S.cartierToWeilHom E' R' * T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') ≤
          T.val.intersectionNumber F := by
      intro t' E' hE' hR't'
      have h := fiber_intersection_eq R F g hE' T.val
      unfold Finsupp.sum at h
      have hmem : R' ∈ (R.S.cartierToWeilHom E').support :=
        (inFiber_iff_mem_support R F g hE' R').mp hR't'
      rw [← Finset.add_sum_erase _ _ hmem] at h
      dsimp only at h
      have hnn : ∀ C ∈ (R.S.cartierToWeilHom E').support.erase R', 0 ≤
          R.S.cartierToWeilHom E' C * T.val.intersectionNumber (R.S.primeCurveCartier R.hreg C) := by
        intro C hC
        have hCin : InFiber g t' C := inFiber_of_coeff_ne_zero R F g hE' C
          (Finsupp.mem_support_iff.mp (Finset.mem_erase.mp hC).2)
        have hCT : T.val ≠ C := fun heq => by
          have := intersectionNumber_eq_zero_of_vertical R F g hg e C t' hCin
          rw [← heq] at this
          exact hTF this
        exact mul_nonneg (hE'.effective C) (inter_nonneg hCT)
      have := Finset.sum_nonneg hnn
      linarith
    have hμ1 := coeff_pos_of_inFiber R F g hE R' hR't
    have hfibE := hfib t E hE hR't
    have hTR'nn : 0 ≤ T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') :=
      inter_nonneg (fun heq => by
        have := hvert R' hR'supp
        rw [← heq] at this
        exact hTF this)
    -- `T · R ≥ F · T ≥ μ_R (T · R) ≥ T · R`
    have hμa : T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') ≤
        R.S.cartierToWeilHom E R' * T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') := by
      nlinarith
    have hk0 : T.val.intersectionNumber R.KS = 0 := by omega
    have hh0 : T.val.intersectionNumber (R.S.primeCurveCartier R.hreg H.val) = 0 := by omega
    have hTRF : T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') =
        T.val.intersectionNumber F := by omega
    refine ⟨(w_eq_two_of_Kdeg_eq_zero T hk0).1, hh0, hTRF, ?_⟩
    intro t' E' hE' hR't'
    have hμ1' := coeff_pos_of_inFiber R F g hE' R' hR't'
    have hfibE' := hfib t' E' hE' hR't'
    have hpos : 0 < T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') := by omega
    have h1 : (R.S.cartierToWeilHom E' R' - 1) *
        T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') ≤ 0 := by
      nlinarith
    have h2 : 0 ≤ (R.S.cartierToWeilHom E' R' - 1) *
        T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') :=
      mul_nonneg (by omega) hpos.le
    have h3 : (R.S.cartierToWeilHom E' R' - 1) *
        T.val.intersectionNumber (R.S.primeCurveCartier R.hreg R') = 0 := le_antisymm h1 h2
    rcases mul_eq_zero.mp h3 with h | h
    · omega
    · omega

end Main

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.exceptional_effective_eq_zero
#print axioms KltDP.Manuscript.S07.exists_adjoint
#print axioms KltDP.Manuscript.S07.adjoint_exterior_dichotomy
#print axioms KltDP.Manuscript.S07.bisectionAdjoint
