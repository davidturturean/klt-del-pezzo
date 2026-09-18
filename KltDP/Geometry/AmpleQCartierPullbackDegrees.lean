import KltDP.Geometry.AmplePullbackCurvePositive
import KltDP.Geometry.RationalWeilIntersection

/-!
# Positive integral numerators of the original pullback degrees

The original ample pullback is positive on every original noncontracted
prime. Its actual module isomorphism identifies that degree with the signed
Cartier pullback. The existing Q-Cartier numerator formula then computes the
original rational Weil degree, including its positive common denominator.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.AmplePullbackCurvePositive

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] [GenericPointPreserving π]

/-- The original signed Cartier pullback has positive integral degree on
each original prime which the actual morphism does not contract. -/
theorem intersectionNumber_pos
    (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    0 < C.intersectionNumber (DominantCartierPullback.pullbackHom π A) := by
  rw [C.intersectionNumber_eq_restrictionDegree]
  exact (restrictionDegree_pos π (cartierDivisorInvertibleSheaf X.toScheme A) hA C hC).trans_eq
    (C.restrictionDegree_eq_of_iso (DominantCartierPullback.modulePullbackIso π A))

end KltDP.Geometry.AmplePullbackCurvePositive

namespace KltDP.Geometry.RationalWeilIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]

/-- The existing rational degree of the original Q-Cartier pullback is
the integral degree of its actual signed numerator divided by its denominator. -/
theorem degreeLinearMap_pullback_eq_integer_div
    (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • D) (C : S.PrimeCurve) :
    degreeLinearMap S hS C (QCartierPullback.pullback π D hD) =
      (C.intersectionNumber (DominantCartierPullback.pullbackHom π A) : ℚ) / (n : ℚ) := by
  change degreeLinearMap S hS C (QCartierPullback.pullbackToWeil π ⟨D, hD⟩) = _
  rw [QCartierPullback.pullbackToWeil_eq_of_positive_multiple π ⟨D, hD⟩ n hn A hA,
    map_smul, degreeLinearMap_rationalCartier, smul_eq_mul]
  exact (div_eq_inv_mul _ _).symm

/-- Every actual exterior prime has positive original rational pullback degree. -/
theorem degreeLinearMap_pullback_pos_of_ample_numerator [IsProper π]
    (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • D)
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    0 < degreeLinearMap S hS C (QCartierPullback.pullback π D hD) := by
  rw [degreeLinearMap_pullback_eq_integer_div hS π D hD n hn A hA C]
  apply div_pos
  · exact_mod_cast AmplePullbackCurvePositive.intersectionNumber_pos π A hample C hC
  · exact_mod_cast hn

/-- The common Cartier denominator gives the actual uniform bound 1/n
on every original exterior prime, without a nef-threshold hypothesis. -/
theorem one_div_le_degreeLinearMap_pullback [IsProper π]
    (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • D)
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    1 / (n : ℚ) ≤ degreeLinearMap S hS C (QCartierPullback.pullback π D hD) := by
  have hnum : (1 : ℤ) ≤ C.intersectionNumber (DominantCartierPullback.pullbackHom π A) := by
    have hpos := AmplePullbackCurvePositive.intersectionNumber_pos π A hample C hC
    omega
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [degreeLinearMap_pullback_eq_integer_div hS π D hD n hn A hA C]
  simp only [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hnq))
  exact_mod_cast hnum

/-- Multiplication by the actual denominator yields a natural number,
obtained from the positive original integral Cartier degree. -/
theorem degreeLinearMap_pullback_scaled_integral [IsProper π]
    (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (n : ℕ) (hn : 0 < n) (A : CartierDivisor X.toScheme)
    (hA : X.rationalCartierToWeilHom A = n • D)
    (hample : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (C : S.PrimeCurve) (hC : ¬ IsExceptionalCurve π C) :
    ∃ m : ℕ, (m : ℚ) = (n : ℚ) *
      degreeLinearMap S hS C (QCartierPullback.pullback π D hD) := by
  let d := C.intersectionNumber (DominantCartierPullback.pullbackHom π A)
  have hd : 0 ≤ d := le_of_lt
    (AmplePullbackCurvePositive.intersectionNumber_pos π A hample C hC)
  have hcast : (d.toNat : ℚ) = (d : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hd
  refine ⟨d.toNat, ?_⟩
  rw [hcast, degreeLinearMap_pullback_eq_integer_div hS π D hD n hn A hA C]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp only [d]
  field_simp [hnq]

end KltDP.Geometry.RationalWeilIntersection

#check @KltDP.Geometry.AmplePullbackCurvePositive.intersectionNumber_pos
#check @KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_pullback_scaled_integral
#print axioms KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_pullback_pos_of_ample_numerator
#print axioms KltDP.Geometry.RationalWeilIntersection.one_div_le_degreeLinearMap_pullback
#print axioms KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_pullback_scaled_integral
