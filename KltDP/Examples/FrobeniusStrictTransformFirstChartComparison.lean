import KltDP.Examples.FrobeniusStrictTransformFirstChartTensorFrame
import KltDP.Geometry.SchemeOpenChartComparison
import KltDP.Geometry.SchemeKernelFrameSquare

/-!
# Original total-versus-product comparison on the first whole-stage chart

The original coordinate blowdown induces a map between the actual first affine
opens. Its inclusion square is the previously proved original stage-projection
square, and its section map pulls the previous frame equation back to the actual
total equation. The existing pullback and unit comparisons transport the original
previous strict frame to the literal iterated pullback. It therefore agrees with
the original product frame over the actual ambient structure module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFirstChartComparison

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformInvertible
open FrobeniusGraphPicardClassAffine FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformFirstChartProduct FrobeniusStrictTransformFirstChartTensorFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original coordinate blowdown between the literal first affine opens of consecutive stages. -/
def firstOpenStepProjection (n : ℕ) :
    (firstAffineOpen (k := k) (n + 1)).1.toScheme ⟶
      (firstAffineOpen (k := k) n).1.toScheme :=
  schemeOpenChartMap (((projectiveProductInitial (k := k)).stage (n + 1)).chart)
    (((projectiveProductInitial (k := k)).stage n).chart) (coordinateBlowdown (k := k))

/-- This map is over the original whole-stage blowdown and both original open inclusions. -/
@[reassoc] theorem firstOpenStepProjection_square (n : ℕ) :
    firstOpenStepProjection (k := k) n ≫ (firstAffineOpen n).1.ι =
      (firstAffineOpen (n + 1)).1.ι ≫ (projectiveProductInitial (k := k)).stepProjection n :=
  schemeOpenChartMap_ι (((projectiveProductInitial (k := k)).stage (n + 1)).chart)
    (((projectiveProductInitial (k := k)).stage n).chart) (coordinateBlowdown (k := k))
    ((projectiveProductInitial (k := k)).stepProjection n)
    (by simpa only [coordinateBlowdown_eq] using firstStageChart_projection (k := k) n)

/-- The actual open map has exactly the same pulled equation as the original coordinate blowdown. -/
theorem firstOpenStepProjection_equation (n m : ℕ) :
    (firstOpenStepProjection (k := k) n).appTop (firstOpenEquation n (m + 1)) =
      firstTotalOpenEquation n m :=
  schemeOpenChartMap_section (((projectiveProductInitial (k := k)).stage (n + 1)).chart)
    (((projectiveProductInitial (k := k)).stage n).chart) (coordinateBlowdown (k := k))
    (firstEquation (m + 1))

/-- The original previous strict frame transported to the literal iterated one-step pullback. -/
def strictTotalFirstOpenFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) :=
  schemeKernelFrameOnSquare (strictTransformι n ((m + 1) + n)) (firstAffineOpen n).1.ι
    (firstOpenStepProjection n) (firstAffineOpen (n + 1)).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (firstOpenStepProjection_square n)
    (strictKernelFirstOpenFrame n (m + 1))

/-- Its original iterated pulled inclusion multiplies by the same actual total-transform equation. -/
theorem strictTotalFirstOpenFrame_inclusion (n m : ℕ) :
    (strictTotalFirstOpenFrame (k := k) n m).hom ≫
      (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map
        (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
          ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom =
        (schemeScalarEnd (Y := (firstAffineOpen (k := k) (n + 1)).1.toScheme) (firstTotalOpenEquation n m) :
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf) := by
  have h := schemeKernelFrameOnSquare_inclusion
    (strictTransformι (k := k) n ((m + 1) + n)) (firstAffineOpen n).1.ι
    (firstOpenStepProjection n) (firstAffineOpen (n + 1)).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (firstOpenStepProjection_square n)
    (strictKernelFirstOpenFrame n (m + 1)) (firstOpenEquation n (m + 1))
    (strictKernelFirstOpenFrame_inclusion n (m + 1))
  simpa only [firstOpenStepProjection_equation] using h

/-- The actual pulled previous strict ideal and original exceptional-times-strict tensor line
are isomorphic on the original first affine open. -/
def strictTotalProductFirstOpenIso (n m : ℕ) :
    (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        (strictExceptionalTensorLine n m).obj :=
  (strictTotalFirstOpenFrame n m).symm ≪≫ strictExceptionalFirstOpenFrame n m

/-- The actual first-chart isomorphism preserves both original ambient ideal maps. -/
theorem strictTotalProductFirstOpenIso_inclusion (n m : ℕ) :
    (strictTotalProductFirstOpenIso (k := k) n m).hom ≫
      (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map
        (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom =
    (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map
      (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom := by
  simp only [strictTotalProductFirstOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [strictExceptionalFirstOpenFrame_inclusion,
    ← strictTotalFirstOpenFrame_inclusion, Iso.inv_hom_id_assoc]

end KltDP.Examples.FrobeniusStrictTransformFirstChartComparison
