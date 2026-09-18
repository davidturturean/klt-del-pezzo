import KltDP.Geometry.EffectiveWeilCommonPart
import KltDP.Geometry.EffectiveWeilPrimeSupport
import KltDP.Geometry.ProjectiveAmpleCartierWitness

/-! Strict ample degree detects nonzero effective original Weil divisors.
It also proves that distinct linearly equivalent original members have
a nonzero residual after their coefficientwise common part is removed. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry
open scoped BigOperators
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Strict degree belongs to the original Cartier inverse of the
original effective Weil divisor. -/
theorem effectiveWeil_ample_pairing_pos (D : X.WeilDivisor)
    (hD : EffectiveDivisor D) (hne : D ≠ 0) (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A)) :
    0 < X.intersectionPairing hX ((X.regularCartierWeilEquiv hX).symm D) A := by
  classical
  have hmap : X.cartierToWeilHom ((X.regularCartierWeilEquiv hX).symm D) = D :=
    (X.regularCartierWeilEquiv hX).apply_symm_apply D
  rw [X.intersectionPairing_eq_weil_sum_right hX, hmap]
  change 0 < ∑ C ∈ D.support, D C * C.intersectionNumber A
  apply Finset.sum_pos
  · intro C hC
    have hcoeff : 0 < D C := lt_of_le_of_ne (hD C) (Finsupp.mem_support_iff.mp hC).symm
    apply mul_pos hcoeff
    rw [C.intersectionNumber_eq_restrictionDegree A]
    exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme A) hA C
  · exact Finsupp.support_nonempty_iff.mpr hne

/-- An effective original divisor of zero ample degree is literally zero. -/
theorem effectiveWeil_eq_zero_of_ample_pairing_zero (D : X.WeilDivisor)
    (hD : EffectiveDivisor D) (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (hzero : X.intersectionPairing hX ((X.regularCartierWeilEquiv hX).symm D) A = 0) :
    D = 0 := by
  by_contra hne
  have hpos := X.effectiveWeil_ample_pairing_pos hX D hD hne A hA
  omega

include hX in
/-- No nonzero effective original Weil divisor is principal. -/
theorem effectiveWeil_eq_zero_of_linearlyEquivalent_zero (D : X.WeilDivisor)
    (hD : EffectiveDivisor D) (hlinear : X.LinearlyEquivalent D 0) : D = 0 := by
  obtain ⟨A, hA⟩ := X.exists_isAmple_cartier
  apply X.effectiveWeil_eq_zero_of_ample_pairing_zero hX D hD A hA
  rw [NefIntersectionSectionVanishing.intersection_eq_of_linearlyEquivalent X hX A hlinear,
    map_zero, X.intersectionPairing_zero_left hX]

include hX in
/-- Distinct original members have a genuinely nonzero left residual;
this does not assume that the residual linear system moves. -/
theorem commonWeilPart_left_ne_zero (D E : X.WeilDivisor)
    (hDE : X.LinearlyEquivalent D E) (hne : D ≠ E) : D - (D ⊓ E) ≠ 0 := by
  intro hz
  have hlinear := X.linearlyEquivalent_sub_common hDE (D ⊓ E)
  rw [hz] at hlinear
  have hz' := X.effectiveWeil_eq_zero_of_linearlyEquivalent_zero hX (E - (D ⊓ E))
    (X.commonWeilPart_right_effective D E) (X.linearlyEquivalent_symm hlinear)
  exact hne ((sub_eq_zero.mp hz).trans (sub_eq_zero.mp hz').symm)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_left_ne_zero
#print axioms KltDP.Geometry.NormalProjectiveSurface.commonWeilPart_left_ne_zero
