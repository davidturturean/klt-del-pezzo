import KltDP.Examples.FrobeniusMultiCentreExceptionalPrime
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.PrimeCurveDegreeTransport
import KltDP.Geometry.NumericalEquivalence

/-!
# Original exceptional-curve degree transport to its translated tower component

The actual pullback projection identifies a global exceptional curve with
its original final component in the selected tower. Composing with the
canonical isomorphism from its prime-curve scheme gives an isomorphism
over the original field, with a proved commuting inclusion square.
The accepted degree transport then applies to every tower Picard class.
Only the global surface's existing projectivity premise is retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreExceptionalDegreeTransport

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveDegreeTransport
open FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts
  FrobeniusContactTowerSelectedPoint FrobeniusExceptionalFinalConfiguration
  FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime

variable {k : Type u} [Field k]

/-- Every original tower projection commutes with the actual field structures. -/
theorem towerProjection_structure (p n : ℕ) (a : Fin n → k) (i : Fin n) :
    towerProjection p n a i ≫ ((translatedInitial p (a i)).stage p).structureMap =
      multiStructure p n a := by
  rw [← selectedProjection_structure, ← Category.assoc, towerProjection_projection]
  rfl

variable [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (i : Fin n) (idx : FinalIndex.{0} q)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original exceptional prime curve is isomorphic to its actual translated tower component. -/
def exceptionalPrimeToComponentIso :
    (exceptionalPrimeCurveSPn q n a ha i idx hproj).toScheme ≅
      finalComponent (translatedInitial (q + 1) (a i)) q idx := by
  letI := exceptionalCurve_isIntegral q n a ha i idx
  letI := exceptionalCurveToComponent_isIso q n a ha i idx
  exact (asIso (PrimeCurveInclusionLift.lift
    (exceptionalPrimeCurveSPn q n a ha i idx hproj) (exceptionalCurveι q n a i idx)
    (coe_exceptionalPrimeCurveSPn q n a ha i idx hproj))).symm ≪≫
      asIso (exceptionalCurveToComponent q n a i idx)

/-- The isomorphism is the original tower projection restricted to the actual prime curve. -/
theorem exceptionalPrimeToComponentIso_hom_inclusion :
    (exceptionalPrimeToComponentIso q n a ha i idx hproj).hom ≫
        finalComponentι (translatedInitial (q + 1) (a i)) q idx =
      (exceptionalPrimeCurveSPn q n a ha i idx hproj).inclusion ≫
        towerProjection (q + 1) n a i := by
  letI := exceptionalCurve_isIntegral q n a ha i idx
  letI := exceptionalCurveToComponent_isIso q n a ha i idx
  simp only [exceptionalPrimeToComponentIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Category.assoc]
  rw [← exceptionalCurve_condition, ← Category.assoc,
    ← PrimeCurveInclusionLift.inclusion_eq_inv_lift]

/-- The same actual isomorphism commutes with the original field structures. -/
theorem exceptionalPrimeToComponentIso_hom_structure :
    (exceptionalPrimeToComponentIso q n a ha i idx hproj).hom ≫
        (finalComponentι (translatedInitial (q + 1) (a i)) q idx ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap) =
      (exceptionalPrimeCurveSPn q n a ha i idx hproj).toSpec := by
  rw [← Category.assoc, exceptionalPrimeToComponentIso_hom_inclusion,
    Category.assoc, towerProjection_structure]
  rfl

/-- The actual tower pullback degree is the Euler degree on its original exceptional component. -/
theorem exceptionalRestrictionDegree_pullback_eq
    (p : (selectedStage (q + 1) (a i) (q + 1)).Pic) :
    (exceptionalPrimeCurveSPn q n a ha i idx hproj).picardRestrictionDegree
        (schemePicardPullbackHom (towerProjection (q + 1) n a i) p) =
      eulerDegree (finalComponentι (translatedInitial (q + 1) (a i)) q idx ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap)
        (schemePicardPullbackHom (finalComponentι (translatedInitial (q + 1) (a i)) q idx) p) := by
  have h := (exceptionalPrimeCurveSPn q n a ha i idx hproj).picardRestrictionDegree_pullback
    (towerProjection (q + 1) n a i) p
  rw [← exceptionalPrimeToComponentIso_hom_inclusion q n a ha i idx hproj,
    schemePicardPullbackHom_comp] at h
  exact h.trans (picardDegree_pullback_iso (exceptionalPrimeCurveSPn q n a ha i idx hproj)
    (exceptionalPrimeToComponentIso q n a ha i idx hproj).hom _
    (exceptionalPrimeToComponentIso_hom_structure q n a ha i idx hproj) _)

/-- The same original degree transport for the additive restriction-degree homomorphism. -/
theorem exceptionalRestrictionDegreeHom_pullback_eq
    (p : Additive (selectedStage (q + 1) (a i) (q + 1)).Pic) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
        (exceptionalPrimeCurveSPn q n a ha i idx hproj)
        ((schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive p) =
      eulerDegree (finalComponentι (translatedInitial (q + 1) (a i)) q idx ≫
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap)
        (schemePicardPullbackHom (finalComponentι (translatedInitial (q + 1) (a i)) q idx) p.toMul) :=
  exceptionalRestrictionDegree_pullback_eq q n a ha i idx hproj p.toMul

end KltDP.Examples.FrobeniusMultiCentreExceptionalDegreeTransport
