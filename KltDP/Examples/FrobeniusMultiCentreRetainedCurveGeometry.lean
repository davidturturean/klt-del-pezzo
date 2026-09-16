import KltDP.Examples.FrobeniusMultiCentreRetainedCurves
import KltDP.Examples.FrobeniusExceptionalEulerDegrees

/-!
# The original retained projective-line isomorphisms respect the original field

The exceptional comparison is the original pullback projection. Its field
square follows from the accepted tower-component square and the original tower
projection square. Together with the global graph and fibre squares, this
proves smoothness over the original field for the entire same retained family.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRetainedCurveGeometry

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalEulerDegrees
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional
  FrobeniusMultiCentreChainPicard FrobeniusMultiCentreExceptionalDegreeTransport
  FrobeniusMultiCentreGraphProjectiveLine FrobeniusMultiCentreFiberProjectiveLine
  FrobeniusMultiCentreRetainedCurves FrobeniusStrictTransformSmoothCurves

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The accepted exceptional-curve isomorphism is over the original field. -/
theorem exceptionalCurveIsoProjectiveLine_hom_structure
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
    (i : Fin n) (idx : FinalIndex.{0} q) :
    (curveIso q n a ha i idx).hom ≫ projectiveSpaceToSpec k 1 =
      exceptionalCurveι q n a i idx ≫ multiStructure (q + 1) n a := by
  have hc : (componentIso q n a i idx).hom ≫ projectiveSpaceToSpec k 1 =
      finalComponentι (translatedInitial (q + 1) (a i)) q idx ≫
        ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap := by
    cases idx with
    | inl j =>
      exact (finalComponentι_comp_structure (translatedInitial (q + 1) (a i)) q
        (Sum.inl j : FinalIndex.{u} q)).symm
    | inr z =>
      exact (finalComponentι_comp_structure (translatedInitial (q + 1) (a i)) q
        (Sum.inr PUnit.unit : FinalIndex.{u} q)).symm
  change exceptionalCurveToComponent q n a i idx ≫
    ((componentIso q n a i idx).hom ≫ projectiveSpaceToSpec k 1) = _
  rw [hc, ← Category.assoc, ← exceptionalCurve_condition, Category.assoc,
    towerProjection_structure]

variable [CharP k 2]

local instance primeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

variable (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)

/-- Each retained projective-line isomorphism commutes with the original field map. -/
theorem retainedCurveIsoProjectiveLine_hom_structure
    (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (retainedCurveIsoProjectiveLine n a ha r).hom ≫ projectiveSpaceToSpec k 1 =
      retainedInclusion n a r ≫ multiStructure 2 n a := by
  rcases r with r | (i | i)
  · exact globalGraphIsoProjectiveLine_hom_structure 2 n a
  · exact globalFiberIsoProjectiveLine_hom_structure 1 n a ha i
  · exact exceptionalCurveIsoProjectiveLine_hom_structure 1 n a ha i (.inl (0 : Fin 1))

include ha in
/-- Every original retained curve is smooth over its original field. -/
theorem retainedCurve_isSmooth (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    IsSmooth (retainedInclusion n a r ≫ multiStructure 2 n a) := by
  rw [← retainedCurveIsoProjectiveLine_hom_structure n a ha r]
  letI : IsSmooth (projectiveSpaceToSpec k 1) := projectiveLine_isSmooth
  infer_instance

/-- Every original retained curve is proper over its original field. -/
theorem retainedCurve_isProper (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    IsProper (retainedInclusion n a r ≫ multiStructure 2 n a) := by
  infer_instance

include ha in
theorem retainedCurve_nonempty (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    Nonempty (retainedCurve n a r) :=
  ⟨(retainedCurveIsoProjectiveLine n a ha r).inv.base (projectiveSpace_nonempty k 1).some⟩

include ha in
/-- The same actual retained curves are integral. -/
theorem retainedCurve_isIntegral (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    IsIntegral (retainedCurve n a r) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI := retainedCurve_nonempty n a ha r
  exact isIntegral_of_isOpenImmersion (retainedCurveIsoProjectiveLine n a ha r).hom

end KltDP.Examples.FrobeniusMultiCentreRetainedCurveGeometry
