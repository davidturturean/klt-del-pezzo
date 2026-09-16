import KltDP.Examples.FrobeniusStrictTransformFirstChartComparison
import KltDP.Examples.FrobeniusStrictTransformSecondChartComparison
import KltDP.Examples.FrobeniusStrictTransformProductCover
import KltDP.Examples.FrobeniusStrictTransformProductPuncture
import KltDP.Geometry.SchemeModuleMonicFactorOnCover

/-!
# The original whole-stage total/exceptional/strict ideal isomorphism

The two original Rees opens and the actual current-center complement cover the
whole successor stage. Their already normalized original isomorphisms kill the
cokernel obstruction to factoring the pulled previous inclusion through the
original product inclusion. The pinned monoLift is the resulting global map.
Monicity proves it restricts to each original local map; hence it is an
isomorphism over the original ambient structure module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformTotalProduct

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformFirstChartComparison
open FrobeniusStrictTransformSecondChartComparison
open FrobeniusStrictTransformProductPuncture FrobeniusStrictTransformProductCover

private theorem cancel_final_iso {C : Type*} [Category C]
    {M N Q R : C} (e : Q ≅ R) (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ Q)
    (h : a ≫ b ≫ e.hom = c ≫ e.hom) : a ≫ b = c := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc] using h

variable {k : Type u} [Field k]

local instance totalProductOriginalMono (n m : ℕ) :
    Mono (strictExceptionalProduct (k := k) n m) :=
  strictExceptionalProduct_mono n m

/-- The three already constructed isomorphisms between the literal original pullbacks. -/
def strictTotalProductLocalIso (n m : ℕ) (i : Option Bool) :
    (schemeModulePullback (strictProductCoverOpen (k := k) n i).ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) ≅
      (schemeModulePullback (strictProductCoverOpen (k := k) n i).ι).obj
        (strictExceptionalTensorLine n m).obj := by
  cases i with
  | none => exact strictTotalProductFirstOpenIso n m
  | some i =>
    cases i with
    | false => exact strictTotalProductSecondOpenIso n m
    | true => exact strictTotalProductPunctureIso n m

/-- Each member retains both actual ambient maps, including the chosen pullback unit comparison. -/
theorem strictTotalProductLocalIso_inclusion (n m : ℕ) (i : Option Bool) :
    (strictTotalProductLocalIso (k := k) n m i).hom ≫
      (schemeModulePullback (strictProductCoverOpen n i).ι).map (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (strictProductCoverOpen n i).ι).hom =
    (schemeModulePullback (strictProductCoverOpen n i).ι).map
      (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (strictProductCoverOpen n i).ι).hom := by
  cases i with
  | none => exact strictTotalProductFirstOpenIso_inclusion n m
  | some i =>
    cases i with
    | false => exact strictTotalProductSecondOpenIso_inclusion n m
    | true => exact strictTotalProductPunctureIso_inclusion n m

/-- Cancellation of that same unit isomorphism gives equality of the literal pullback maps. -/
theorem strictTotalProductLocalIso_map (n m : ℕ) (i : Option Bool) :
    (strictTotalProductLocalIso (k := k) n m i).hom ≫
      (schemeModulePullback (strictProductCoverOpen n i).ι).map (strictExceptionalProduct n m) =
    (schemeModulePullback (strictProductCoverOpen n i).ι).map
      (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n)) :=
  cancel_final_iso (schemeModulePullbackUnitIso (strictProductCoverOpen n i).ι)
    (strictTotalProductLocalIso n m i).hom _ _ (strictTotalProductLocalIso_inclusion n m i)

/-- The original previous strict ideal pulled back by the original blowdown is the original
exceptional-times-successor-strict tensor line on the entire successor stage. -/
def strictTotalProductIso (n m : ℕ) :
    (schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (strictTransformι n ((m + 1) + n))) ≅
      (strictExceptionalTensorLine n m).obj :=
  schemeModuleMonicFactorIsoOnOpenCover (strictProductCoverOpen n)
    (strictProductCoverOpen_covers n) (strictExceptionalProduct n m)
    (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
      ((projectiveProductInitial (k := k)).stepProjection n))
    (strictTotalProductLocalIso n m) (strictTotalProductLocalIso_map n m)

/-- The whole-stage isomorphism preserves the literal original ambient ideal inclusion. -/
@[reassoc] theorem strictTotalProductIso_inclusion (n m : ℕ) :
    (strictTotalProductIso (k := k) n m).hom ≫ strictExceptionalProduct n m =
      pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n) :=
  schemeModuleMonicFactorIsoOnOpenCover_comp (strictProductCoverOpen n)
    (strictProductCoverOpen_covers n) (strictExceptionalProduct n m)
    (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
      ((projectiveProductInitial (k := k)).stepProjection n))
    (strictTotalProductLocalIso n m) (strictTotalProductLocalIso_map n m)

/-- Compatibility is proved by equality to the restriction of the original global map on each open. -/
theorem strictTotalProductIso_restrict (n m : ℕ) (i : Option Bool) :
    (schemeModulePullback (strictProductCoverOpen n i).ι).map
        (strictTotalProductIso (k := k) n m).hom = (strictTotalProductLocalIso n m i).hom :=
  schemeModuleMonicFactorIsoOnOpenCover_map (strictProductCoverOpen n)
    (strictProductCoverOpen_covers n) (strictExceptionalProduct n m)
    (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
      ((projectiveProductInitial (k := k)).stepProjection n))
    (strictTotalProductLocalIso n m) (strictTotalProductLocalIso_map n m) i

/-- The original ambient inclusion uniquely determines this whole-stage factor. -/
theorem strictTotalProductIso_hom_unique (n m : ℕ)
    (a : (schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (strictTransformι n ((m + 1) + n))) ⟶
      (strictExceptionalTensorLine n m).obj)
    (ha : a ≫ strictExceptionalProduct n m =
      pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n)) :
    a = (strictTotalProductIso n m).hom :=
  (cancel_mono (strictExceptionalProduct n m)).mp
    (ha.trans (strictTotalProductIso_inclusion n m).symm)

end KltDP.Examples.FrobeniusStrictTransformTotalProduct
