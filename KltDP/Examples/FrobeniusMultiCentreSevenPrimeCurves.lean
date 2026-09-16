import KltDP.Examples.FrobeniusMultiCentreRetainedPrimeCurves

/-!
# Seven original disjoint smooth rational curves of square minus two

At three characteristic-two clusters the retained family has seven labels.
The previously constructed original prime curves are distinct, their supports
are disjoint, their original field maps are smooth, and their actual scheme
isomorphisms to the projective line respect those maps. The intrinsic Cartier
intersection matrix specializes to minus twice the identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreSevenPrimeCurves

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRetainedCurves
  FrobeniusMultiCentreRetainedPrimeCurves

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  (a : Fin 3 → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure 2 3 a))

/-- Distinct original retained prime curves have disjoint actual supports. -/
theorem sevenPrimeCurve_disjoint (r s : FrobeniusCharacteristicTwo.RetainedLabel 3)
    (hrs : r ≠ s) :
    Disjoint (retainedPrimeCurve 3 a ha hproj r : Set (multiSurfaceSurface 2 3 a ha hproj).toScheme)
      (retainedPrimeCurve 3 a ha hproj s : Set (multiSurfaceSurface 2 3 a ha hproj).toScheme) := by
  simpa only [coe_retainedPrimeCurve] using retainedInclusion_disjoint 3 a ha r s hrs

/-- Every entry of the intrinsic seven-prime-curve Cartier intersection matrix. -/
theorem sevenPrimeCurve_intersectionNumber (r s : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    (retainedPrimeCurve 3 a ha hproj r).intersectionNumber
      ((multiSurfaceSurface 2 3 a ha hproj).primeCurveCartier
        (multiSurfaceSurface_regularPoints 2 3 a ha hproj) (retainedPrimeCurve 3 a ha hproj s)) =
      if r = s then -2 else 0 := by
  rw [retainedPrimeCurve_intersectionNumber]
  have hw : FrobeniusCharacteristicTwo.retainedWeight 3 r = 2 := by
    rcases r with r | r <;> norm_num [FrobeniusCharacteristicTwo.retainedWeight]
  rw [hw]

/-- Each original retained prime curve has intrinsic self-intersection minus two. -/
theorem sevenPrimeCurve_selfIntersectionNumber (r : FrobeniusCharacteristicTwo.RetainedLabel 3) :
    (retainedPrimeCurve 3 a ha hproj r).selfIntersectionNumber
      (multiSurfaceSurface_regularPoints 2 3 a ha hproj) = -2 := by
  change (retainedPrimeCurve 3 a ha hproj r).intersectionNumber
    ((multiSurfaceSurface 2 3 a ha hproj).primeCurveCartier
      (multiSurfaceSurface_regularPoints 2 3 a ha hproj) (retainedPrimeCurve 3 a ha hproj r)) = -2
  simpa only [ite_true] using sevenPrimeCurve_intersectionNumber a ha hproj r r

/-- The original surface carries exactly this seven-element family of distinct disjoint
smooth rational curves of square minus two. This is a statement on the smooth surface. -/
theorem sevenPrimeCurve_configuration :
    Fintype.card (FrobeniusCharacteristicTwo.RetainedLabel 3) = 7 ∧
    Function.Injective (retainedPrimeCurve 3 a ha hproj) ∧
    (∀ r s : FrobeniusCharacteristicTwo.RetainedLabel 3, r ≠ s →
      Disjoint (retainedPrimeCurve 3 a ha hproj r : Set (multiSurfaceSurface 2 3 a ha hproj).toScheme)
        (retainedPrimeCurve 3 a ha hproj s : Set (multiSurfaceSurface 2 3 a ha hproj).toScheme)) ∧
    (∀ r : FrobeniusCharacteristicTwo.RetainedLabel 3,
      IsSmooth (retainedPrimeCurve 3 a ha hproj r).toSpec ∧
      (∃ e : (retainedPrimeCurve 3 a ha hproj r).toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = (retainedPrimeCurve 3 a ha hproj r).toSpec) ∧
      (retainedPrimeCurve 3 a ha hproj r).selfIntersectionNumber
        (multiSurfaceSurface_regularPoints 2 3 a ha hproj) = -2) := by
  refine ⟨?_, retainedPrimeCurve_injective 3 a ha hproj,
    sevenPrimeCurve_disjoint a ha hproj, ?_⟩
  · simpa using FrobeniusCharacteristicTwo.retainedLabel_card 3
  · intro r
    exact ⟨retainedPrimeCurve_isSmooth 3 a ha hproj r,
      ⟨retainedPrimeIsoProjectiveLine 3 a ha hproj r,
        retainedPrimeIsoProjectiveLine_hom_structure 3 a ha hproj r⟩,
      sevenPrimeCurve_selfIntersectionNumber a ha hproj r⟩

end KltDP.Examples.FrobeniusMultiCentreSevenPrimeCurves
