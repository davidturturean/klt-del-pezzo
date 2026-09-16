import KltDP.Examples.FrobeniusMultiCentreRetainedCurveGeometry
import KltDP.Geometry.PrimeCurveOfClosedImmersion
import KltDP.Geometry.PrimeCurveInclusionLift

/-!
# The original retained curves in the surface's prime-curve theory

The prime curves below are the ranges of the original closed immersions, with
dimension one proved by the actual projective-line isomorphisms. The canonical
prime-curve scheme is identified with the original curve over the original
field. Its Cartier class and all restriction degrees are the classes and
matrix already computed on the original multi-centre surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRetainedPrimeCurves

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveOfClosedImmersion KltDP.Geometry.PrimeCurveTransversalPoint
  KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRetainedGram
  FrobeniusMultiCentreRetainedCurves FrobeniusMultiCentreRetainedCurveGeometry
  FrobeniusStrictTransformSmoothCurves

variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure 2 n a))

/-- The actual retained closed immersions define prime curves of the original surface. -/
def retainedPrimeCurve (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (multiSurfaceSurface 2 n a ha hproj).PrimeCurve :=
  primeCurveOfIsoProjectiveLine (multiSurfaceSurface 2 n a ha hproj)
    (retainedInclusion n a r) (retainedCurveIsoProjectiveLine n a ha r)

@[simp] theorem coe_retainedPrimeCurve (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeCurve n a ha hproj r : Set (multiSurfaceSurface 2 n a ha hproj).toScheme) =
      Set.range (retainedInclusion n a r).base := rfl

/-- The labels represent distinct actual prime curves. -/
theorem retainedPrimeCurve_injective : Function.Injective (retainedPrimeCurve n a ha hproj) := by
  intro r s hrs
  by_contra hne
  obtain ⟨x⟩ := retainedCurve_nonempty n a ha r
  have hr : (retainedInclusion n a r).base x ∈ Set.range (retainedInclusion n a r).base :=
    ⟨x, rfl⟩
  have hs : (retainedInclusion n a r).base x ∈ Set.range (retainedInclusion n a s).base := by
    rw [← coe_retainedPrimeCurve n a ha hproj s, ← hrs, coe_retainedPrimeCurve]
    exact hr
  exact Set.disjoint_left.mp (retainedInclusion_disjoint n a ha r s hne) hr hs

/-- The canonical prime-curve scheme is the original embedded curve. -/
def retainedPrimeIsoCurve (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeCurve n a ha hproj r).toScheme ≅ retainedCurve n a r := by
  letI := retainedCurve_isIntegral n a ha r
  exact (asIso (PrimeCurveInclusionLift.lift (retainedPrimeCurve n a ha hproj r)
    (retainedInclusion n a r) (coe_retainedPrimeCurve n a ha hproj r))).symm

theorem retainedPrimeIsoCurve_hom_inclusion (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeIsoCurve n a ha hproj r).hom ≫ retainedInclusion n a r =
      (retainedPrimeCurve n a ha hproj r).inclusion := by
  letI := retainedCurve_isIntegral n a ha r
  exact (PrimeCurveInclusionLift.inclusion_eq_inv_lift (retainedPrimeCurve n a ha hproj r)
    (retainedInclusion n a r) (coe_retainedPrimeCurve n a ha hproj r)).symm

/-- Each original retained prime-curve scheme is a projective line. -/
def retainedPrimeIsoProjectiveLine (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeCurve n a ha hproj r).toScheme ≅ projectiveSpace k 1 :=
  retainedPrimeIsoCurve n a ha hproj r ≪≫ retainedCurveIsoProjectiveLine n a ha r

theorem retainedPrimeIsoProjectiveLine_hom_structure
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeIsoProjectiveLine n a ha hproj r).hom ≫ projectiveSpaceToSpec k 1 =
      (retainedPrimeCurve n a ha hproj r).toSpec := by
  simp only [retainedPrimeIsoProjectiveLine, Iso.trans_hom, Category.assoc]
  rw [retainedCurveIsoProjectiveLine_hom_structure, ← Category.assoc,
    retainedPrimeIsoCurve_hom_inclusion]
  rfl

theorem retainedPrimeCurve_isSmooth (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    IsSmooth (retainedPrimeCurve n a ha hproj r).toSpec := by
  rw [← retainedPrimeIsoProjectiveLine_hom_structure n a ha hproj r]
  letI : IsSmooth (projectiveSpaceToSpec k 1) := projectiveLine_isSmooth
  infer_instance

/-- The Cartier class of each actual prime curve is the original computed kernel class. -/
theorem retainedPrimeCurve_cartierClass (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    cartierPicardHom (multiSurfaceSurface 2 n a ha hproj).toScheme
      ((multiSurfaceSurface 2 n a ha hproj).primeCurveCartier
        (multiSurfaceSurface_regularPoints 2 n a ha hproj) (retainedPrimeCurve n a ha hproj r)) =
      retainedClass n a ha r := by
  letI := retainedCurve_isIntegral n a ha r
  rw [retainedClass_eq_kernel]
  exact cartierPicardHom_primeCurveCartier_of_kernel
    (multiSurfaceSurface_regularPoints 2 n a ha hproj) (retainedPrimeCurve n a ha hproj r)
    (retainedInclusion n a r) (coe_retainedPrimeCurve n a ha hproj r)
    (retainedKernelLine n a ha r) (retainedKernelLine_obj n a ha r)

/-- The complete retained matrix as actual restriction degrees on actual prime curves. -/
theorem retainedPrimeCurve_restrictionDegree
    (r s : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (multiSurfaceSurface 2 n a ha hproj).picardRestrictionDegreeHom
      (retainedPrimeCurve n a ha hproj r) (retainedClass n a ha s) =
      if r = s then -FrobeniusCharacteristicTwo.retainedWeight n r else 0 := by
  letI := retainedCurve_isIntegral n a ha r
  have h := pairing_kernelLine_left (multiSurfaceSurface 2 n a ha hproj)
    (multiSurfaceSurface_regularPoints 2 n a ha hproj) (retainedPrimeCurve n a ha hproj r)
    (retainedInclusion n a r) (coe_retainedPrimeCurve n a ha hproj r)
    (retainedKernelLine n a ha r) (retainedKernelLine_obj n a ha r) (retainedClass n a ha s)
  change multiPairing 2 n a ha hproj (-Additive.ofMul (retainedKernelLine n a ha r).toPic)
    (retainedClass n a ha s) = _ at h
  rw [← retainedClass_eq_kernel n a ha r] at h
  exact h.symm.trans (retainedClass_pairing n a ha hproj r s)

/-- Every entry in the intrinsic Cartier intersection matrix of the actual prime curves. -/
theorem retainedPrimeCurve_intersectionNumber
    (r s : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedPrimeCurve n a ha hproj r).intersectionNumber
      ((multiSurfaceSurface 2 n a ha hproj).primeCurveCartier
        (multiSurfaceSurface_regularPoints 2 n a ha hproj) (retainedPrimeCurve n a ha hproj s)) =
      if r = s then -FrobeniusCharacteristicTwo.retainedWeight n r else 0 := by
  rw [← PrimeCurve.picardRestrictionDegreeHom_cartierPicardHom, retainedPrimeCurve_cartierClass]
  exact retainedPrimeCurve_restrictionDegree n a ha hproj r s

end KltDP.Examples.FrobeniusMultiCentreRetainedPrimeCurves
