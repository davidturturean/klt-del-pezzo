import KltDP.Examples.FrobeniusMultiCentreExceptionalDegreeTransport
import KltDP.Examples.FrobeniusMultiCentreGraphExceptionalPairing
import KltDP.Examples.FrobeniusMultiCentreExceptionalGlobalClasses
import KltDP.Examples.FrobeniusExceptionalEulerUnconditional

/-!
# The actual newest exceptional class has self-pairing minus one

The accepted normal-line Euler degree on the original point-blowup fibre
is transported through the actual exceptional-curve isomorphism. Its
normal class is the inverse of the restriction of the original ambient
kernel line. This computes the newest total class and actual kernel
self-pairings on the multi-centre surface, retaining only its existing
projectivity premise. No separate tower projectivity or degree is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreNewestExceptionalSelf

open KltDP.Geometry KltDP.Geometry.ModuleCohomology
  KltDP.Geometry.NormalProjectiveSurface KltDP.Geometry.PrimeCurveDegreeTransport
  KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
  FrobeniusGlobalExceptionalNormal FrobeniusGlobalExceptionalBase
  FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
  FrobeniusExceptionalFinalConfiguration FrobeniusTowerTransportClasses
  FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreExceptionalDegreeTransport FrobeniusMultiCentreGraphExceptionalPairing

variable {k : Type u} [Field k]

local instance newestSelfOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The original global normal line has Euler degree minus one over its original field map. -/
theorem globalNormalLine_eulerDegree_eq_neg_one (A : PlaneChartedScheme k) :
    eulerDegree (globalExceptionalStructure A) (globalNormalLine A).toPic = -1 := by
  rw [eulerDegree, picardEulerValue_toPic, picardEulerValue_one,
    eulerCharacteristic_eq_pullback_inv (globalExceptionalProjectiveLineIso A) _ _
      (globalExceptionalProjectiveLineIso_hom_structure A),
    eulerCharacteristic_unit_eq (globalExceptionalProjectiveLineIso A) _ _
      (globalExceptionalProjectiveLineIso_hom_structure A)]
  exact f09_exceptional_euler_difference k A

/-- The original inverse kernel line restricts to the original normal-line Picard class. -/
theorem inverse_centerIdeal_restrict_eq_normal (A : PlaneChartedScheme k) :
    schemePicardPullbackHom (globalExceptionalInclusion A)
        ((PointBlowupGluing.globalCenterFiberIdealLine A.chart (originPoint (k := k))
          A.center_closed).toPic⁻¹) = (globalNormalLine A).toPic := by
  rw [map_inv, schemePicardPullbackHom_toPic, globalNormalLine, dualInvertibleSheaf_toPic]
  exact congrArg Inv.inv (SchemeKernelIdealIsoTransport.toPic_eq_of_iso _ _ (Iso.refl _))

variable [IsAlgClosed k] (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (i : Fin n)

/-- Restriction degree on the actual newest exceptional prime curve. -/
abbrev newestPairing : Additive (multiSurface (q + 1) n a).Pic →+ ℤ :=
  (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)

set_option maxHeartbeats 800000 in
/-- The newest total exceptional class has degree minus one on its original prime curve. -/
theorem newestPairing_total_last :
    newestPairing q n a ha hproj i (exceptionalClass (q + 1) n a i (Fin.last q)) = -1 := by
  rw [exceptionalClass_eq_pullback, translatedTotalExceptionalClass_last]
  change (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    ((schemePicardPullbackHom (towerProjection (q + 1) n a i)).toAdditive
      (translatedStepExceptionalClass (q + 1) (a i) q)) = -1
  rw [exceptionalRestrictionDegreeHom_pullback_eq]
  change eulerDegree (globalExceptionalStructure ((translatedInitial (q + 1) (a i)).stage q))
    (schemePicardPullbackHom (globalExceptionalInclusion ((translatedInitial (q + 1) (a i)).stage q))
      ((PointBlowupGluing.globalCenterFiberIdealLine
        ((translatedInitial (q + 1) (a i)).stage q).chart (originPoint (k := k))
        ((translatedInitial (q + 1) (a i)).stage q).center_closed).toPic⁻¹)) = -1
  rw [inverse_centerIdeal_restrict_eq_normal]
  exact globalNormalLine_eulerDegree_eq_neg_one _

/-- The actual inverse newest-kernel class has degree minus one on that same curve. -/
theorem newestPairing_kernel_self :
    newestPairing q n a ha hproj i
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic) = -1 := by
  rw [newestClass_SPn]
  exact newestPairing_total_last q n a ha hproj i

/-- The original newest exceptional kernel class has symmetric self-pairing minus one. -/
theorem newestKernel_pairing_self :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic) = -1 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inr PUnit.unit)
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalCurveι q n a i (.inr PUnit.unit))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalKernelLine q n a ha i (.inr PUnit.unit)) rfl
    (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic)).trans
    (newestPairing_kernel_self q n a ha hproj i)

/-- The proved original newest total class has symmetric square minus one. -/
theorem newestTotalClass_pairing_self :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i (Fin.last q))
      (exceptionalClass (q + 1) n a i (Fin.last q)) = -1 := by
  rw [← newestClass_SPn q n a ha i]
  exact newestKernel_pairing_self q n a ha hproj i

end KltDP.Examples.FrobeniusMultiCentreNewestExceptionalSelf
