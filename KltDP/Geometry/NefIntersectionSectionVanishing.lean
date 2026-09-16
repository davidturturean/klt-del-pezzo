import KltDP.Geometry.IntersectionPairingSymmetry
import KltDP.Geometry.SectionEffectiveWeil
import KltDP.Geometry.SurfaceEulerSections
import KltDP.Geometry.AmpleNefUnconditional

/-!
# Negative nef intersection forces actual section vanishing

The proof uses the original finite prime decomposition, nonnegative degrees
of an actual nef line bundle, and the original section-to-effective-Weil
producer. Linear equivalence preserves the existing intersection pairing.
No Riemann--Roch or duality input is used in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology
open scoped BigOperators

universe u

namespace KltDP.Geometry.NefIntersectionSectionVanishing

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- An actual effective integral Weil divisor has nonnegative intersection
with the original Cartier divisor whose line bundle is nef. -/
theorem intersection_nonneg (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (Z : X.WeilDivisor) (hZ : EffectiveDivisor Z) :
    0 ≤ intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm Z) A := by
  have hZmap : X.cartierToWeilHom ((X.regularCartierWeilEquiv hregular).symm Z) = Z :=
    (X.regularCartierWeilEquiv hregular).apply_symm_apply Z
  rw [X.intersectionPairing_eq_weil_sum_right hregular, hZmap]
  change 0 ≤ ∑ C ∈ Z.support, Z C * C.intersectionNumber A
  apply Finset.sum_nonneg
  intro C _
  apply mul_nonneg (hZ C)
  rw [← X.intersectionPairing_primeCurve hregular A C]
  exact (X.isNef_iff_pairing hregular A).mp hA C

/-- The original rational-function linear-equivalence relation preserves
intersection with the original Cartier test divisor. -/
theorem intersection_eq_of_linearlyEquivalent (A : CartierDivisor X.toScheme)
    {D E : X.WeilDivisor} (hDE : X.LinearlyEquivalent D E) :
    intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm D) A =
      intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm E) A := by
  have hp := (X.regularWeilPicardClass_eq_iff hregular D E).mpr hDE
  have hclass :
      cartierPicardClass X.toScheme ((X.regularCartierWeilEquiv hregular).symm D) =
        cartierPicardClass X.toScheme ((X.regularCartierWeilEquiv hregular).symm E) :=
    (X.regularWeilClassPicardEquiv_representative hregular D).symm.trans
      (hp.trans (X.regularWeilClassPicardEquiv_representative hregular E))
  exact X.intersectionPairing_eq_of_class_eq_left hregular
    (X.primeCurveIntersectionSymmetric hregular) _ _ A hclass

/-- Negative intersection against an actual nef Cartier class kills every
original section of O(D). The contradiction uses the section's actual
effective Weil representative and the same principal-divisor relation. -/
theorem sections_subsingleton (D : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hnegative : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm D) A < 0) :
    Subsingleton (sections (cartierDivisorModule X.toScheme
      ((X.regularCartierWeilEquiv hregular).symm D))) := by
  have hzero : ∀ s : sections (cartierDivisorModule X.toScheme
      ((X.regularCartierWeilEquiv hregular).symm D)), s = 0 := by
    intro s
    by_contra hs
    obtain ⟨Z, hZ, hZD⟩ := X.exists_effectiveWeil_of_nonzero_section hregular D s hs
    have hnonnegative := intersection_nonneg X hregular A hA Z hZ
    rw [intersection_eq_of_linearlyEquivalent X hregular A hZD] at hnonnegative
    exact (not_le_of_gt hnegative) hnonnegative
  exact ⟨fun s t => (hzero s).trans (hzero t).symm⟩

/-- The same actual section vanishing for the existing Serre ampleness
predicate, using the already proved ample-implies-nef theorem. -/
theorem sections_subsingleton_of_isAmple
    (D : X.WeilDivisor) (A : CartierDivisor X.toScheme)
    (hA : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A))
    (hnegative : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm D) A < 0) :
    Subsingleton (sections (cartierDivisorModule X.toScheme
      ((X.regularCartierWeilEquiv hregular).symm D))) :=
  sections_subsingleton X hregular D A
    (AmpleNefUnconditional.isNef_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme A) hA) hnegative

end KltDP.Geometry.NefIntersectionSectionVanishing
