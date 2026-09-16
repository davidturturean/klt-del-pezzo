import KltDP.Examples.FrobeniusMultiCentreExceptionalDegreeTransport
import KltDP.Examples.FrobeniusStrictTransformSmoothCurves

/-!
# Smoothness and closed-point DVRs of the original global exceptional curves

The canonical prime-curve isomorphism to the actual translated tower component
composes with that component's proved projective-line isomorphism. The accepted
field-structure identities prove that this is an isomorphism over the original
field. Smoothness and the closed-point DVR theorem therefore apply to every old
and newest global exceptional prime curve, without a DVR hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalSmooth

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusTranslatedCharts FrobeniusExceptionalFinalConfiguration
  FrobeniusExceptionalChainPicard FrobeniusExceptionalEulerDegrees
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalDegreeTransport FrobeniusStrictTransformSmoothCurves

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (i : Fin n) (idx : FinalIndex.{0} q)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original global exceptional prime curve is isomorphic to the projective line. -/
def exceptionalPrimeProjectiveLineIso :
    (exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme ≅ projectiveSpace k 1 :=
  exceptionalPrimeToComponentIso q n a ha i idx hproj ≪≫
    (match idx with
    | .inl j => FrobeniusPreviousStrictIsoProjectiveLine.previousStrictIsoProjectiveLine
        ((translatedInitial (q + 1) (a i)).stage j.val)
    | .inr _ => FrobeniusGlobalExceptionalSuccessor.previousFiberIso
        ((translatedInitial (q + 1) (a i)).stage q))

/-- This is the original isomorphism over the original field, not only an abstract scheme iso. -/
theorem exceptionalPrimeProjectiveLineIso_hom_structure :
    (exceptionalPrimeProjectiveLineIso q n a ha i idx hproj).hom ≫
        projectiveSpaceToSpec k 1 =
      (exceptionalPrimeCurveSPn q n a ha i idx hproj).toSpec := by
  cases idx with
  | inl j =>
    simp only [exceptionalPrimeProjectiveLineIso, Iso.trans_hom, Category.assoc]
    have h :
        (FrobeniusPreviousStrictIsoProjectiveLine.previousStrictIsoProjectiveLine
          ((translatedInitial (q + 1) (a i)).stage j.val)).hom ≫ projectiveSpaceToSpec k 1 =
        finalComponentι (translatedInitial (q + 1) (a i)) q (Sum.inl j : FinalIndex.{0} q) ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap :=
      (finalComponentι_comp_structure (translatedInitial (q + 1) (a i)) q
        (Sum.inl j : FinalIndex.{u} q)).symm
    rw [h]
    exact exceptionalPrimeToComponentIso_hom_structure q n a ha i (.inl j) hproj
  | inr z =>
    simp only [exceptionalPrimeProjectiveLineIso, Iso.trans_hom, Category.assoc]
    have h :
        (FrobeniusGlobalExceptionalSuccessor.previousFiberIso
          ((translatedInitial (q + 1) (a i)).stage q)).hom ≫ projectiveSpaceToSpec k 1 =
        finalComponentι (translatedInitial (q + 1) (a i)) q (Sum.inr z : FinalIndex.{0} q) ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap :=
      (finalComponentι_comp_structure (translatedInitial (q + 1) (a i)) q
        (Sum.inr PUnit.unit : FinalIndex.{u} q)).symm
    rw [h]
    exact exceptionalPrimeToComponentIso_hom_structure q n a ha i (.inr z) hproj

/-- Every actual old or newest global exceptional prime curve is smooth over the original field. -/
theorem exceptionalPrime_isSmooth_toSpec :
    IsSmooth (exceptionalPrimeCurveSPn q n a ha i idx hproj).toSpec :=
  isSmooth_toSpec_of_iso _
    (exceptionalPrimeProjectiveLineIso q n a ha i idx hproj).hom
    (projectiveSpaceToSpec k 1) projectiveLine_isSmooth
    (exceptionalPrimeProjectiveLineIso_hom_structure q n a ha i idx hproj)

local instance exceptionalSmooth_stalkIsDomain
    (y : (exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme) :
    IsDomain ((exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain _ y

/-- Closed points of each original global exceptional prime curve have DVR stalks. -/
theorem exceptionalPrime_stalk_isDiscreteValuationRing
    (y : (exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme)
    (hy : IsClosed ({y} : Set (exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme)) :
    IsDiscreteValuationRing
      ((exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme.presheaf.stalk y) := by
  haveI := exceptionalPrime_isSmooth_toSpec q n a ha i idx hproj
  exact (exceptionalPrimeCurveSPn q n a ha i idx hproj).stalk_isDiscreteValuationRing_of_isSmooth y hy

end KltDP.Examples.FrobeniusMultiCentreExceptionalSmooth
