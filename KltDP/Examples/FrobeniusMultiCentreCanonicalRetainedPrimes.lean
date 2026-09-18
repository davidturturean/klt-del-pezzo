import KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPairing
import KltDP.Examples.FrobeniusMultiCentreRetainedPrimeCurves
import KltDP.Geometry.SmoothCanonicalCartierPicard

/-!
# Actual canonical and anticanonical degrees on the original retained primes

The original prime-curve inclusion and its original kernel line identify
restriction degree with the already computed geometric pairing. The canonical
Cartier divisor below is the existing representative of the actual atlas
canonical line. Its class is proved from that representative's sheaf isomorphism,
not defined by a desired numerical formula. Both degrees vanish on the seven
original characteristic-two retained prime curves at three distinct centres.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPrimes

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRetainedGram
open FrobeniusMultiCentreRetainedCurves FrobeniusMultiCentreRetainedCurveGeometry
open FrobeniusMultiCentreRetainedPrimeCurves FrobeniusMultiCentreCanonicalOpenComparison
open FrobeniusMultiCentreCanonicalRetainedPairing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Restriction to the original retained prime is its original geometric pairing. -/
theorem retainedPrimeCurve_degree_eq_pairing (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n)
    (x : Additive (multiSurface 2 n a).Pic) :
    (multiSurfaceSurface 2 n a ha hproj).picardRestrictionDegreeHom
        (retainedPrimeCurve n a ha hproj r) x =
      multiPairing 2 n a ha hproj x (retainedClass n a ha r) := by
  letI := retainedCurve_isIntegral n a ha r
  have h := pairing_kernelLine_left (multiSurfaceSurface 2 n a ha hproj)
    (multiSurfaceSurface_regularPoints 2 n a ha hproj) (retainedPrimeCurve n a ha hproj r)
    (retainedInclusion n a r) (coe_retainedPrimeCurve n a ha hproj r)
    (retainedKernelLine n a ha r) (retainedKernelLine_obj n a ha r) x
  change multiPairing 2 n a ha hproj (-Additive.ofMul (retainedKernelLine n a ha r).toPic)
    x = _ at h
  rw [← retainedClass_eq_kernel n a ha r] at h
  exact h.symm.trans (multiPairing_symm 2 n a ha hproj _ _)

/-- The actual canonical line has the computed restriction degree on each original prime. -/
theorem retainedPrimeCurve_canonicalDegree (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (multiSurfaceSurface 2 n a ha hproj).picardRestrictionDegreeHom
        (retainedPrimeCurve n a ha hproj r) (multiCanonicalClass 2 n a ha) =
      FrobeniusCharacteristicTwo.retainedWeight n r - 2 := by
  rw [retainedPrimeCurve_degree_eq_pairing, canonical_retained_pairing]

/-- The actual anticanonical line has the opposite restriction degree. -/
theorem retainedPrimeCurve_anticanonicalDegree (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (multiSurfaceSurface 2 n a ha hproj).picardRestrictionDegreeHom
        (retainedPrimeCurve n a ha hproj r) (-multiCanonicalClass 2 n a ha) =
      2 - FrobeniusCharacteristicTwo.retainedWeight n r := by
  rw [retainedPrimeCurve_degree_eq_pairing, anticanonical_retained_pairing]

/-- The existing Cartier representative of the actual smooth canonical line. -/
def canonicalDivisor (n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    @CartierDivisor (multiSurface 2 n a) (multiSurface_isIntegral 2 n a ha) := by
  letI := multiSurface_isIntegral 2 n a ha
  letI := multiStructure_smoothTwo 2 n a ha
  exact SmoothCanonicalCartierRepresentative.cartierRepresentative (multiStructure 2 n a)

/-- Its class is the original atlas canonical class, by the original representative isomorphism. -/
theorem canonicalDivisor_class (n : ℕ) (a : Fin n → k) (ha : Function.Injective a) :
    @cartierPicardHom (multiSurface 2 n a) (multiSurface_isIntegral 2 n a ha)
        (canonicalDivisor n a ha) =
      multiCanonicalClass 2 n a ha := by
  letI := multiSurface_isIntegral 2 n a ha
  letI := multiStructure_smoothTwo 2 n a ha
  exact SmoothCanonicalCartierPicard.cartierPicardHom_representative (multiStructure 2 n a)

/-- The intrinsic canonical Cartier intersection with each original retained prime. -/
theorem retainedPrimeCurve_canonicalIntersection (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeCurve n a ha hproj r).intersectionNumber (canonicalDivisor n a ha) =
      FrobeniusCharacteristicTwo.retainedWeight n r - 2 := by
  rw [← PrimeCurve.picardRestrictionDegreeHom_cartierPicardHom]
  change (multiSurfaceSurface 2 n a ha hproj).picardRestrictionDegreeHom
    (retainedPrimeCurve n a ha hproj r)
    (@cartierPicardHom (multiSurface 2 n a) (multiSurface_isIntegral 2 n a ha)
      (canonicalDivisor n a ha)) = _
  rw [canonicalDivisor_class n a ha]
  exact retainedPrimeCurve_canonicalDegree n a ha hproj r

/-- The intrinsic anticanonical Cartier intersection with each original retained prime. -/
theorem retainedPrimeCurve_anticanonicalIntersection (n : ℕ) (a : Fin n → k)
    (ha : Function.Injective a) (hproj : IsProjectiveOverField (multiStructure 2 n a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeCurve n a ha hproj r).intersectionNumber (-canonicalDivisor n a ha) =
      2 - FrobeniusCharacteristicTwo.retainedWeight n r := by
  rw [(retainedPrimeCurve n a ha hproj r).intersectionNumber_neg,
    retainedPrimeCurve_canonicalIntersection]
  omega

/-- All seven original retained prime curves have zero canonical Cartier intersection. -/
theorem sevenPrimeCurve_canonicalIntersection (a : Fin 3 → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure 2 3 a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    (retainedPrimeCurve 3 a ha hproj r).intersectionNumber (canonicalDivisor 3 a ha) = 0 := by
  rw [retainedPrimeCurve_canonicalIntersection]
  rcases r with r | r <;> norm_num [FrobeniusCharacteristicTwo.retainedWeight]

/-- The original anticanonical Cartier divisor is orthogonal to all seven original retained primes. -/
theorem sevenPrimeCurve_anticanonicalIntersection (a : Fin 3 → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure 2 3 a))
    (r : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    (retainedPrimeCurve 3 a ha hproj r).intersectionNumber (-canonicalDivisor 3 a ha) = 0 := by
  rw [retainedPrimeCurve_anticanonicalIntersection]
  rcases r with r | r <;> norm_num [FrobeniusCharacteristicTwo.retainedWeight]

end KltDP.Examples.FrobeniusMultiCentreCanonicalRetainedPrimes
