import KltDP.Examples.FrobeniusStrictTransformSecondChartTensorFrame
import KltDP.Geometry.SchemeOpenChartComparison
import KltDP.Geometry.SchemeKernelFrameSquare

/-!
# Original total-versus-product comparison on the second whole-stage chart

The original second Rees blowdown induces a map from its actual image open to
the previous first open, over the literal whole-stage projection. Transporting
the original previous strict frame through that square gives the same pulled
equation as the original product frame. The resulting isomorphism therefore
preserves both actual ambient ideal maps. No coefficient equality is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformSecondChartComparison

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformInvertible
open FrobeniusGraphPicardClassAffine FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformSecondChartTensorFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original second-chart blowdown between the actual image opens of consecutive stages. -/
def secondOpenStepProjection (n : ℕ) :
    (secondAffineOpen (k := k) n).1.toScheme ⟶ (firstAffineOpen (k := k) n).1.toScheme :=
  schemeOpenChartMap (secondStageChart n)
    (((projectiveProductInitial (k := k)).stage n).chart) (secondCoordinateBlowdown (k := k))

/-- Both open inclusions commute with the literal whole-stage one-step projection. -/
@[reassoc] theorem secondOpenStepProjection_square (n : ℕ) :
    secondOpenStepProjection (k := k) n ≫ (firstAffineOpen n).1.ι =
      (secondAffineOpen n).1.ι ≫ (projectiveProductInitial (k := k)).stepProjection n :=
  schemeOpenChartMap_ι (secondStageChart n)
    (((projectiveProductInitial (k := k)).stage n).chart) (secondCoordinateBlowdown (k := k))
    ((projectiveProductInitial (k := k)).stepProjection n)
    (secondStageChart_projection (k := k) n)

/-- Its actual section map pulls the previous frame equation to the original second total equation. -/
theorem secondOpenStepProjection_equation (n m : ℕ) :
    (secondOpenStepProjection (k := k) n).appTop (firstOpenEquation n (m + 1)) =
      secondTotalOpenEquation n m :=
  schemeOpenChartMap_section (secondStageChart n)
    (((projectiveProductInitial (k := k)).stage n).chart) (secondCoordinateBlowdown (k := k))
    (firstEquation (m + 1))

/-- The original previous strict frame transported to the literal iterated one-step pullback. -/
def strictTotalSecondOpenFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) :=
  schemeKernelFrameOnSquare (strictTransformι n ((m + 1) + n)) (firstAffineOpen n).1.ι
    (secondOpenStepProjection n) (secondAffineOpen n).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (secondOpenStepProjection_square n)
    (strictKernelFirstOpenFrame n (m + 1))

/-- The original iterated pulled inclusion multiplies by the same actual second total equation. -/
theorem strictTotalSecondOpenFrame_inclusion (n m : ℕ) :
    (strictTotalSecondOpenFrame (k := k) n m).hom ≫
      (schemeModulePullback (secondAffineOpen n).1.ι).map
        (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
          ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom =
        (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme) (secondTotalOpenEquation n m) :
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) := by
  have h := schemeKernelFrameOnSquare_inclusion
    (strictTransformι (k := k) n ((m + 1) + n)) (firstAffineOpen n).1.ι
    (secondOpenStepProjection n) (secondAffineOpen n).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (secondOpenStepProjection_square n)
    (strictKernelFirstOpenFrame n (m + 1)) (firstOpenEquation n (m + 1))
    (strictKernelFirstOpenFrame_inclusion n (m + 1))
  simpa only [secondOpenStepProjection_equation] using h

/-- The actual pulled previous kernel and exceptional-times-strict tensor agree on the second open. -/
def strictTotalProductSecondOpenIso (n m : ℕ) :
    (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (strictExceptionalTensorLine n m).obj :=
  (strictTotalSecondOpenFrame n m).symm ≪≫ strictExceptionalSecondOpenFrame n m

/-- This second-chart isomorphism preserves both literal original ambient ideal maps. -/
theorem strictTotalProductSecondOpenIso_inclusion (n m : ℕ) :
    (strictTotalProductSecondOpenIso (k := k) n m).hom ≫
      (schemeModulePullback (secondAffineOpen n).1.ι).map (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom =
    (schemeModulePullback (secondAffineOpen n).1.ι).map
      (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom := by
  simp only [strictTotalProductSecondOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [strictExceptionalSecondOpenFrame_inclusion,
    ← strictTotalSecondOpenFrame_inclusion, Iso.inv_hom_id_assoc]

end KltDP.Examples.FrobeniusStrictTransformSecondChartComparison
