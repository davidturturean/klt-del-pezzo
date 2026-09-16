import KltDP.Geometry.AmpleCurveRestrictionPositive
import KltDP.Geometry.PrimeCurveExistence
import KltDP.Geometry.SectionEffectiveWeil
import KltDP.Geometry.PrimeCurveClassPairing
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import KltDP.Geometry.EulerPairingUnconditional
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Positive self-intersection from Serre ampleness on a regular surface

On the original normal projective surface, the proved point-separating
construction produces a positive tensor power with an actual effective
Cartier representative. Its proper intersection with an actual prime curve
contains a point, so the Cartier divisor is nonzero. Its original finite
Cartier-to-Weil image has nonnegative coefficients.

For the existing intersection pairing, the surface is additionally regular
over an algebraically closed field. The accepted Cartier--Weil equivalence
then makes this Weil image nonzero. The mixed pairing formula is a finite
sum of its nonnegative coefficients times the original sheaf's strictly
positive restriction degrees. Thus the pairing of the positive power with
the original sheaf is positive, and the accepted bilinearity proves that
the original sheaf itself has positive self-intersection.

No section, nontrivial divisor, finite-support condition or positive-square
condition is supplied to the final consumer. Ampleness remains an explicit
hypothesis. The original four-term Euler pairing is positive as well. General normal-surface pairing
and Euler additivity are outside the regular-surface interface used here;
this module does not claim that extension or construct an IsAmple witness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.AmpleSelfIntersectionPositive

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- A positive power of the original ample sheaf has an actual nonzero
effective Cartier representative. Effectivity is also proved for its
original finite Weil image. No regularity of the surface is needed here. -/
theorem exists_nonzero_effectiveCartier_power_of_isAmple
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) :
    ∃ n : ℕ, 0 < n ∧ ∃ M : InvertibleSheaf X.toScheme,
      M.toPic = L.toPic ^ n ∧ ∃ E : CartierDivisor X.toScheme,
        ∃ hE : HasRegularCartierEquations X.toScheme E,
          Nonempty (cartierDivisorModule X.toScheme E ≅ M.obj) ∧
            E ≠ 0 ∧ EffectiveDivisor (X.cartierToWeilHom E) := by
  letI : IsLocallyNoetherian X.toScheme := NormalProjectiveSurface.isLocallyNoetherian X
  obtain ⟨C⟩ := X.primeCurve_nonempty
  obtain ⟨x, hxC, hxclosed, hne⟩ :=
    AmpleCurveRestrictionPositive.exists_closed_point_ne_generic X C
  obtain ⟨n, hn, M, hM, E, hE, e, _, _, hxE, hηE⟩ :=
    AmplePointSeparatingCartier.exists_positive_power_point_separating_effectiveCartier
      L hL x C.genericPoint hxclosed hne
  have hpos : 0 < C.restrictionDegree M :=
    AmpleCurveRestrictionPositive.restrictionDegree_pos_of_effectiveIso_of_mem
      X C M E hE hηE e x hxC hxE
  have heq : C.intersectionNumber E = C.restrictionDegree M :=
    (C.intersectionNumber_eq_restrictionDegree E).trans (C.restrictionDegree_eq_of_iso e)
  refine ⟨n, hn, M, hM, E, hE, ⟨e⟩, ?_,
    X.effective_cartierToWeilHom_of_regularEquations E hE⟩
  intro hz
  rw [← heq, hz, C.intersectionNumber_zero] at hpos
  exact (lt_irrefl (0 : ℤ)) hpos

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular in
/-- Nontriviality of the actual Cartier divisor is retained by its original
Weil image, through the accepted regular-surface equivalence. -/
theorem cartierToWeil_ne_zero_of_ne_zero (E : CartierDivisor X.toScheme) (hE : E ≠ 0) :
    X.cartierToWeilHom E ≠ 0 := by
  intro hz
  apply hE
  apply (X.regularCartierWeilEquiv hregular).injective
  change X.cartierToWeilHom E = X.cartierToWeilHom 0
  rw [hz, map_zero]

/-- The mixed formula pairs the original effective representative with the
restriction degrees of the original invertible sheaf. -/
theorem picardPairing_cartierClass_eq_weil_sum
    (E : CartierDivisor X.toScheme) (L : InvertibleSheaf X.toScheme) :
    X.picardPairing hregular (cartierPicardClass X.toScheme E) L.toPic =
      (X.cartierToWeilHom E).sum fun C a => a * C.restrictionDegree L := by
  obtain ⟨D, hD⟩ := cartierPicardClass_surjective X.toScheme L.toPic
  rw [← hD, X.picardPairing_class hregular E D,
    X.intersectionPairing_eq_weil_sum_right hregular E D]
  refine Finsupp.sum_congr fun C _ => ?_
  rw [C.intersectionNumber_eq_picardRestrictionDegree D, hD,
    C.picardRestrictionDegree_toPic L]

/-- An original nonzero effective Cartier divisor pairs positively with an
ample sheaf: every nonzero coefficient and every curve degree is positive. -/
theorem picardPairing_cartierClass_pos_of_isAmple
    (E : CartierDivisor X.toScheme) (hE : E ≠ 0)
    (hEff : EffectiveDivisor (X.cartierToWeilHom E))
    (L : InvertibleSheaf X.toScheme) (hL : AmpleSerre.IsAmple L) :
    0 < X.picardPairing hregular (cartierPicardClass X.toScheme E) L.toPic := by
  classical
  have hW : X.cartierToWeilHom E ≠ 0 :=
    cartierToWeil_ne_zero_of_ne_zero X hregular E hE
  rw [picardPairing_cartierClass_eq_weil_sum X hregular E L]
  unfold Finsupp.sum
  apply Finset.sum_pos
  · intro C hC
    have hcoeff : 0 < (X.cartierToWeilHom E) C := by
      have hnonneg := hEff C
      have hne := Finsupp.mem_support_iff.mp hC
      omega
    exact mul_pos hcoeff
      (AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X L hL C)
  · exact Finsupp.support_nonempty_iff.mpr hW

/-- The existing additive Picard pairing computes tensor powers of the
same original sheaf class. -/
theorem picardPairing_pow_left (p q : X.toScheme.Pic) (n : ℕ) :
    X.picardPairing hregular (p ^ n) q =
      (n : ℤ) * X.picardPairing hregular p q := by
  change PrimeCurveClassPairing.pairing X hregular
      (Additive.ofMul (p ^ n)) (Additive.ofMul q) =
    (n : ℤ) * PrimeCurveClassPairing.pairing X hregular
      (Additive.ofMul p) (Additive.ofMul q)
  rw [ofMul_pow, PrimeCurveClassPairing.pairing_nsmul_left]

/-- Serre ampleness implies positive self-intersection of the original
invertible sheaf on the actual regular projective surface. -/
theorem selfIntersection_pos_of_isAmple (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) : 0 < X.selfIntersection hregular L := by
  obtain ⟨n, hn, M, hM, E, _, ⟨e⟩, hE, hEff⟩ :=
    exists_nonzero_effectiveCartier_power_of_isAmple X L hL
  have hp := picardPairing_cartierClass_pos_of_isAmple X hregular E hE hEff L hL
  have hclass : cartierPicardClass X.toScheme E = L.toPic ^ n :=
    (SchemeKernelIdealIsoTransport.toPic_eq_of_iso
      (cartierDivisorInvertibleSheaf X.toScheme E) M e).trans hM
  rw [hclass, picardPairing_pow_left X hregular L.toPic L.toPic n] at hp
  have hn' : (0 : ℤ) < (n : ℤ) := Nat.cast_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hn').mp hp

include hregular in
/-- The original four-term Euler pairing of the same ample sheaf class is
positive, using the proved regular-surface comparison. -/
theorem picardEulerPairing_self_pos_of_isAmple (L : InvertibleSheaf X.toScheme)
    (hL : AmpleSerre.IsAmple L) : 0 < X.picardEulerPairing L.toPic L.toPic := by
  rw [← X.selfIntersection_eq_picardEulerPairing_of_regular hregular L]
  exact selfIntersection_pos_of_isAmple X hregular L hL

end Regular

end KltDP.Geometry.AmpleSelfIntersectionPositive
