import KltDP.Examples.FrobeniusGlobalBlowupCanonicalTarget
import KltDP.Examples.FrobeniusBlowupCanonicalGlobalFactor

/-!
# The original canonical factor on the whole-stage affine blowup piece

The accepted whole center-fiber ideal comparison retains its original
inclusion. Tensor it with the actual open differential isomorphism, then
transport the original Rees canonical factor through the proved source and
target comparisons. The result factors exactly the original whole-stage
differential restricted to its actual affine blowup open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupCanonicalAffineFactor

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupDifferentialAffine
open FrobeniusGlobalBlowupCanonicalTarget FrobeniusBlowupGlobalDifferentialCharts
open FrobeniusBlowupGlobalCanonicalTarget FrobeniusBlowupCanonicalGlobalFactor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance wholeAffineFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

local instance wholeAffineFactorOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

variable (A : PlaneChartedScheme k)

/-- The original Rees ideal is the pullback of the same original entire center-fiber kernel. -/
def affineIdealToWholeIso :
    AffineBlowup.exceptionalIdealModule (centerIdeal (k := k)) ≅
      (schemeModulePullback A.nextAffineBlowup).obj (wholeExceptionalIdeal A) :=
  (PointBlowupGluing.globalCenterFiberIdealAffineIso
    A.chart (originPoint (k := k)) A.center_closed).symm

/-- The actual inverse ideal comparison preserves the original ideal inclusion. -/
theorem affineIdealToWholeIso_inclusion :
    (affineIdealToWholeIso A).hom ≫
        ((schemeModulePullback A.nextAffineBlowup).map (wholeExceptionalInclusion A) ≫
          (schemeModulePullbackUnitIso A.nextAffineBlowup).hom) =
      schemeKernelIdealι (AffineBlowup.exceptionalι (centerIdeal (k := k))) := by
  change (PointBlowupGluing.globalCenterFiberIdealAffineIso
      A.chart (originPoint (k := k)) A.center_closed).inv ≫
    pulledKernelInclusion
      (PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k)) A.center_closed)
      (PointBlowupGluing.affineBlowupι A.chart (originPoint (k := k)) A.center_closed) = _
  rw [← PointBlowupGluing.globalCenterFiberIdealAffineIso_hom_ι, Iso.inv_hom_id_assoc]
  rfl

/-- The original tensor pullback identifies the actual global and Rees ideal/top targets. -/
def affineTargetIso :
    (schemeModulePullback A.nextAffineBlowup).obj (wholeCanonicalTarget A) ≅
      exceptionalCanonicalTensor (k := k) :=
  schemeModulePullbackTensorIso A.nextAffineBlowup (wholeExceptionalIdeal A) (nextTop A) ≪≫
    tensorIso (affineIdealToWholeIso A).symm (affineBlowupIso A)

private def affineTargetIso_inclusion_proof (k : Type u) [Field k]
    (A : PlaneChartedScheme k) :=
  schemeModulePullbackTensorIso_comparison_inclusion A.nextAffineBlowup
    (wholeExceptionalInclusion A) (nextTop A) (affineIdealToWholeIso A) (affineBlowupIso A)
    (schemeKernelIdealι (AffineBlowup.exceptionalι (centerIdeal (k := k))))
    (affineIdealToWholeIso_inclusion A)

/-- This target isomorphism retains the whole original ideal-tensor inclusion. -/
theorem affineTargetIso_inclusion :
    (affineTargetIso A).hom ≫ exceptionalCanonicalInclusion (k := k) =
      (schemeModulePullback A.nextAffineBlowup).map (wholeCanonicalInclusion A) ≫
        (affineBlowupIso A).hom := by
  simpa only [affineTargetIso, exceptionalCanonicalInclusion, exceptionalInclusionToUnit,
    wholeCanonicalInclusion, schemeStructureTensorInclusion] using
      affineTargetIso_inclusion_proof k A

/-- The actual affine whole-stage factor is the original Rees factor through original comparisons. -/
def affineCanonicalFactorIso :
    (schemeModulePullback A.nextAffineBlowup).obj
        ((schemeModulePullback A.nextProjection).obj (oldTop A)) ≅
      (schemeModulePullback A.nextAffineBlowup).obj (wholeCanonicalTarget A) :=
  affineSourceIso A ≪≫ canonicalBlowupIso (k := k) ≪≫ (affineTargetIso A).symm

/-- Its composite is precisely the actual pulled whole-stage differential. -/
theorem affineCanonicalFactorIso_comp :
    (affineCanonicalFactorIso A).hom ≫
        (schemeModulePullback A.nextAffineBlowup).map (wholeCanonicalInclusion A) =
      (schemeModulePullback A.nextAffineBlowup).map (nextDifferentialMap A) := by
  apply (cancel_mono (affineBlowupIso A).hom).mp
  simp only [affineCanonicalFactorIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← affineTargetIso_inclusion, Iso.inv_hom_id_assoc,
    canonicalBlowupIso_comp, nextDifferentialMap_affineIso]

end KltDP.Examples.FrobeniusGlobalBlowupCanonicalAffineFactor
