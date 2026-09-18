import KltDP.Geometry.AmplePullbackNef
import KltDP.Geometry.AmplePullbackCurvePositive
import KltDP.Geometry.AmpleSelfIntersectionPositive
import KltDP.Geometry.BirationalCartierPullbackPushforward
import KltDP.Geometry.NormalCartierWeilInjective
import KltDP.Geometry.DominantCartierPullbackEffective

/-!
# Positive square of an actual ample pullback under a proper birational map

A nonzero effective ample-power representative has a positive original Weil
coefficient on the normal target. The proved birational prime correspondence
preserves that coefficient on an actual noncontracted source prime. Its
pullback degree is strictly positive; nefness makes all other terms of the
original effective Weil-sum pairing nonnegative. The resulting positive
mixed pairing and the original Picard power give positive self-intersection.

The target need only be normal. Regularity is required on the source for
its original intersection pairing. No Hodge, Riemann--Roch, projection-formula
square equality, positive-square witness, or exceptional negativity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalAmplePullbackPositiveSquare

open BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The original source prime above a target prime is not contracted:
its actual whole image is that target curve, which is not a point. -/
theorem abovePrimeCurve_not_exceptional (C : X.PrimeCurve) :
    ¬ IsExceptionalCurve π (abovePrimeCurve π hbir C) := by
  rintro ⟨y, hy⟩
  rw [abovePrimeCurve_image π hbir C] at hy
  have hη : C.genericPoint = y := by
    have hmem := C.genericPoint_mem
    change C.genericPoint ∈ (C : Set X.toScheme) at hmem
    rwa [hy] at hmem
  have hclosed : IsClosed ({y} : Set X.toScheme) := by
    rw [← hy]
    exact C.isClosed
  exact C.not_isClosed_singleton_genericPoint (hη.symm ▸ hclosed)

variable [IsAlgClosed k]
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hbir in
/-- An original ample target line sheaf has positive square after the
original proper birational pullback, even when the target is singular. -/
theorem selfIntersection_pos (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) :
    0 < S.selfIntersection hregular (pullbackInvertibleSheaf π L) := by
  classical
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  let A := pullbackInvertibleSheaf π L
  have hnef : ∀ C : S.PrimeCurve, 0 ≤ C.restrictionDegree A :=
    (Positivity.isNef_iff_forall_primeCurve S A).mp
      (AmplePullbackNef.isNef_pullback_of_isAmple S π L hL)
  obtain ⟨n, hn, M, hM, E, hE, ⟨e⟩, hEne, hEff⟩ :=
    AmpleSelfIntersectionPositive.exists_nonzero_effectiveCartier_power_of_isAmple X L hL
  have hWne : X.cartierToWeilHom E ≠ 0 :=
    fun hz => hEne ((X.cartierToWeilHom_eq_zero_iff E).mp hz)
  obtain ⟨C, hC⟩ := Finsupp.support_nonempty_iff.mpr hWne
  have hCpos : 0 < X.cartierToWeilHom E C :=
    lt_of_le_of_ne (hEff C) (Finsupp.mem_support_iff.mp hC).symm
  let B := abovePrimeCurve π hbir C
  let P := DominantCartierPullback.pullbackHom π E
  have hBpos : 0 < S.cartierToWeilHom P B := by
    rw [BirationalWeilPushforward.cartier_pullback_coefficient π hbir E C]
    exact hCpos
  have hBdegree : 0 < B.restrictionDegree A :=
    AmplePullbackCurvePositive.restrictionDegree_pos π L hL B
      (abovePrimeCurve_not_exceptional π hbir C)
  have hEffP : NormalProjectiveSurface.EffectiveDivisor (S.cartierToWeilHom P) :=
    DominantCartierPullback.pullbackHom_effective_of_regularEquations π E hE
  have hp : 0 < S.picardPairing hregular (cartierPicardClass S.toScheme P) A.toPic := by
    rw [AmpleSelfIntersectionPositive.picardPairing_cartierClass_eq_weil_sum]
    unfold Finsupp.sum
    apply Finset.sum_pos'
    · intro Q _
      exact mul_nonneg (hEffP Q) (hnef Q)
    · exact ⟨B, Finsupp.mem_support_iff.mpr (ne_of_gt hBpos), mul_pos hBpos hBdegree⟩
  have eP : cartierDivisorModule S.toScheme P ≅ (pullbackInvertibleSheaf π M).obj :=
    (DominantCartierPullback.modulePullbackIso π E).symm ≪≫ (schemeModulePullback π).mapIso e
  have hclass : cartierPicardClass S.toScheme P = A.toPic ^ n := by
    calc
      cartierPicardClass S.toScheme P = (pullbackInvertibleSheaf π M).toPic :=
        SchemeKernelIdealIsoTransport.toPic_eq_of_iso
          (cartierDivisorInvertibleSheaf S.toScheme P) (pullbackInvertibleSheaf π M) eP
      _ = A.toPic ^ n := by
        rw [← schemePicardPullbackHom_toPic, hM, map_pow, schemePicardPullbackHom_toPic]
  rw [hclass, AmpleSelfIntersectionPositive.picardPairing_pow_left] at hp
  exact (mul_pos_iff_of_pos_left (Nat.cast_pos.mpr hn : (0 : ℤ) < n)).mp hp

include hbir in
/-- The positive square belongs to the literal signed Cartier pullback
used by the original exceptional-curve Hodge consumer. -/
theorem intersectionPairing_signedPullback_pos [GenericPointPreserving π]
    (D : CartierDivisor X.toScheme)
    (hD : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D)) :
    0 < S.intersectionPairing hregular
      (DominantCartierPullback.pullbackHom π D) (DominantCartierPullback.pullbackHom π D) := by
  have hp := selfIntersection_pos π hbir hregular
    (cartierDivisorInvertibleSheaf X.toScheme D) hD
  have hclass := SchemeKernelIdealIsoTransport.toPic_eq_of_iso
    (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme D))
    (cartierDivisorInvertibleSheaf S.toScheme (DominantCartierPullback.pullbackHom π D))
    (DominantCartierPullback.modulePullbackIso π D)
  change 0 < S.picardPairing hregular
    (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme D)).toPic
    (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme D)).toPic at hp
  rw [hclass] at hp
  change 0 < S.picardPairing hregular
    (cartierPicardClass S.toScheme (DominantCartierPullback.pullbackHom π D))
    (cartierPicardClass S.toScheme (DominantCartierPullback.pullbackHom π D)) at hp
  rw [S.picardPairing_class] at hp
  exact hp

end KltDP.Geometry.BirationalAmplePullbackPositiveSquare

#print axioms KltDP.Geometry.BirationalAmplePullbackPositiveSquare.selfIntersection_pos
#print axioms KltDP.Geometry.BirationalAmplePullbackPositiveSquare.intersectionPairing_signedPullback_pos
