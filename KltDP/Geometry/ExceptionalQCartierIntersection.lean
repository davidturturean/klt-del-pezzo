import KltDP.Geometry.RationalWeilIntersection
import KltDP.Geometry.ActualExceptionalPullback

/-!
# Original Q-Cartier pullbacks have degree zero on contracted primes

An actual positive Cartier numerator computes the existing rational pullback.
The original signed pullback has degree zero, so the actual rational degree
vanishes independently of the numerator chosen. Subtraction gives the
original canonical difference's degree, without a discrepancy premise.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.RationalWeilIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)

include hπ

/-- Zero degree of the actual Q-Cartier pullback on an actual contracted prime. -/
theorem degreeLinearMap_pullback_eq_zero
    (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) :
    degreeLinearMap S hregular C (QCartierPullback.pullback π D hD) = 0 := by
  obtain ⟨n, hn, A, hA⟩ := (X.qCartier_iff_exists_positive_multiple D).mp hD
  change degreeLinearMap S hregular C
    (QCartierPullback.pullbackToWeil π ⟨D, hD⟩) = 0
  rw [QCartierPullback.pullbackToWeil_eq_of_positive_multiple π ⟨D, hD⟩ n hn A hA,
    map_smul, degreeLinearMap_rationalCartier,
    hC.intersectionNumber_pullback_eq_zero π hπ C A, Int.cast_zero, smul_zero]

/-- The original signed canonical difference has the source Cartier degree
on every actual contracted prime. No support or coefficient identity is supplied. -/
theorem degreeLinearMap_difference
    (KS : CartierDivisor S.toScheme) (D : X.RationalWeilDivisor) (hD : X.QCartier D)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) :
    degreeLinearMap S hregular C
      (S.rationalCartierToWeilHom KS - QCartierPullback.pullback π D hD) =
      (C.intersectionNumber KS : ℚ) := by
  rw [map_sub, degreeLinearMap_rationalCartier,
    degreeLinearMap_pullback_eq_zero hregular π hπ D hD C hC, sub_zero]

end KltDP.Geometry.RationalWeilIntersection

#check @KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_difference
#print axioms KltDP.Geometry.RationalWeilIntersection.degreeLinearMap_difference
