import KltDP.Examples.FrobeniusOldExceptionalFirstChartFrame
import KltDP.Examples.FrobeniusOldExceptionalPuncture
import KltDP.Examples.FrobeniusStrictTransformProductCover
import KltDP.Geometry.SchemeModuleMonicFactorOnCover
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The whole-stage pullback-ideal identity for the older exceptional curve

The two Rees affine opens of the `(j+2)`-nd stage and the complement of the newest exceptional
curve `E_{j+1}` cover the stage (the lane's `strictProductCoverOpen (j+1)`). On each member the
lane has identified the pullback `π^* I(E_j)` of the ideal of the previous exceptional curve with
the tensor line `I(E_{j+1}) ⊗ I(C_j)` of the newest exceptional curve and of the strict transform
`C_j = previousStrictTransform (A.stage j)` of `E_j`, compatibly with the product inclusion
`exceptionalOldProduct j` into the structure sheaf. Since that product inclusion is a monomorphism,
the accepted monic-factor gluing produces the whole-stage isomorphism

  `π^* I(E_j) ≅ I(E_{j+1}) ⊗ I(C_j)`   (`oldTotalProductIso`)

preserving the ambient ideal inclusions (`oldTotalProductIso_inclusion`); its restriction to each
member of the cover is the local isomorphism (`oldTotalProductIso_restrict`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalTotalProduct

open KltDP.Geometry
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformProductCover
open FrobeniusOldExceptionalChartIdeals FrobeniusOldExceptionalSecondChartFrame
open FrobeniusOldExceptionalFirstChartFrame FrobeniusOldExceptionalPuncture

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance oldTotalSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance oldTotalModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance oldTotalModulesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

/-! ### Generic lemmas, as in the lane's product-kernel and total-product modules -/

private def lineTensorEquivalenceOfInverse {C : Type*} [Category C] [MonoidalCategory C]
    [SymmetricCategory C] {A D : C} (d : A ⊗ D ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft A) (tensorLeft D)
    ((tensorLeftTensor D A).symm ≪≫
      (tensoringLeft C).mapIso ((β_ D A) ≪≫ d) ≪≫ leftUnitorNatIso C).symm
    ((tensorLeftTensor A D).symm ≪≫
      (tensoringLeft C).mapIso d ≪≫ leftUnitorNatIso C)

private theorem tensorLeft_preservesMonomorphisms_of_inverse {C : Type*} [Category C]
    [MonoidalCategory C] [SymmetricCategory C] {A D : C} (d : A ⊗ D ≅ 𝟙_ C) :
    (tensorLeft A).PreservesMonomorphisms :=
  have adj : tensorLeft D ⊣ tensorLeft A := (lineTensorEquivalenceOfInverse d).symm.toAdjunction
  Functor.preservesMonomorphisms_of_adjunction adj

private theorem lineTensor_preservesMonomorphisms {X : Scheme.{u}}
    (L : InvertibleSheaf X) : (tensorLeft L.obj).PreservesMonomorphisms :=
  tensorLeft_preservesMonomorphisms_of_inverse
    (KltDP.SheafOfModules.tensorDualIsoUnit X.sheaf.val X.ringCatSheaf.cond L.obj :
      L.obj ⊗ KltDP.SheafOfModules.dual X.ringCatSheaf L.obj ≅ 𝟙_ X.Modules)

private theorem unitIso_rightUnitor_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) {M N : C} (f : M ⟶ N) :
    f ▷ O ≫ (N ◁ e.inv ≫ (ρ_ N).hom) = (M ◁ e.inv ≫ (ρ_ M).hom) ≫ f := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

private theorem structureTensorRightIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) :
    f ▷ _root_.SheafOfModules.unit X.ringCatSheaf ≫ (schemeStructureTensorRightIso N).hom =
      (schemeStructureTensorRightIso M).hom ≫ f := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  exact unitIso_rightUnitor_naturality (C := X.Modules) e f

private theorem cancel_final_iso {C : Type*} [Category C]
    {M N Q R : C} (e : Q ≅ R) (a : M ⟶ N) (b : N ⟶ Q) (c : M ⟶ Q)
    (h : a ≫ b ≫ e.hom = c ≫ e.hom) : a ≫ b = c := by
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc] using h

variable {k : Type u} [Field k]

local instance oldTotalOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- Tensor cancellation for the invertible exceptional line makes the product inclusion injective. -/
theorem exceptionalOldProduct_mono (j : ℕ) : Mono (exceptionalOldProduct (k := k) j) := by
  letI := lineTensor_preservesMonomorphisms (stepExceptionalIdealLine (k := k) (j + 1))
  rw [exceptionalOldProduct, tensorHom_def', Category.assoc, structureTensorRightIso_naturality]
  haveI : Mono (schemeKernelIdealι (oldExceptionalStrictι (k := k) j)) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono (schemeKernelIdealι
      (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc
        (k := k) (j + 1))) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono (schemeKernelIdeal
      (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc
        (k := k) (j + 1)) ◁ schemeKernelIdealι (oldExceptionalStrictι j)) :=
    inferInstanceAs (Mono ((tensorLeft (stepExceptionalIdealLine (k := k) (j + 1)).obj).map
      (schemeKernelIdealι (oldExceptionalStrictι j))))
  infer_instance

local instance oldTotalProductMono (j : ℕ) : Mono (exceptionalOldProduct (k := k) j) :=
  exceptionalOldProduct_mono j

/-- The source object of a morphism, kept reducible so that it unfolds to the literal object. -/
abbrev homSource {C : Type*} [Category C] {A B : C} (_f : A ⟶ B) : C := A

/-- The tensor line `I(E_{j+1}) ⊗ I(C_j)` on stage `j+2`, literally the source of the product
inclusion `exceptionalOldProduct j` (so that no elaboration has to identify two elaborations of
the tensor product). -/
abbrev exceptionalOldTensor (j : ℕ) : (projectiveContactStage (k := k) (j + 1 + 1)).Modules :=
  homSource (exceptionalOldProduct (k := k) j)

/-- The three local isomorphisms between the literal pullbacks, indexed by the cover. -/
def oldTotalProductLocalIso (j : ℕ) (i : Option Bool) :
    (schemeModulePullback (strictProductCoverOpen (k := k) (j + 1) i).ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection (j + 1))).obj
          (schemeKernelIdeal (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
            (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j))) ≅
      (schemeModulePullback (strictProductCoverOpen (k := k) (j + 1) i).ι).obj
        (exceptionalOldTensor (k := k) j) := by
  cases i with
  | none => exact oldTotalProductFirstOpenIso j
  | some i =>
    cases i with
    | false => exact oldTotalProductSecondOpenIso j
    | true => exact oldTotalProductPunctureIso j

/-- Each member retains both ambient maps, including the pullback unit comparison. -/
theorem oldTotalProductLocalIso_inclusion (j : ℕ) (i : Option Bool) :
    (oldTotalProductLocalIso (k := k) j i).hom ≫
      (schemeModulePullback (strictProductCoverOpen (j + 1) i).ι).map (exceptionalOldProduct j) ≫
      (schemeModulePullbackUnitIso (strictProductCoverOpen (j + 1) i).ι).hom =
    (schemeModulePullback (strictProductCoverOpen (j + 1) i).ι).map
      (pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        ((projectiveProductInitial (k := k)).stepProjection (j + 1))) ≫
      (schemeModulePullbackUnitIso (strictProductCoverOpen (j + 1) i).ι).hom := by
  -- the chart and complement lemmas state the pulled inclusion with the codomain in the
  -- `(A.stage (j+2)).carrier` form; `convert` lets the reducible `projectiveContactStage` unfold
  cases i with
  | none => convert oldTotalProductFirstOpenIso_inclusion (k := k) j using 3
  | some i =>
    cases i with
    | false => convert oldTotalProductSecondOpenIso_inclusion (k := k) j using 3
    | true => convert oldTotalProductPunctureIso_inclusion (k := k) j using 3

/-- Cancellation of the unit isomorphism gives equality of the literal pullback maps. -/
theorem oldTotalProductLocalIso_map (j : ℕ) (i : Option Bool) :
    (oldTotalProductLocalIso (k := k) j i).hom ≫
      (schemeModulePullback (strictProductCoverOpen (j + 1) i).ι).map (exceptionalOldProduct j) =
    (schemeModulePullback (strictProductCoverOpen (j + 1) i).ι).map
      (pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        ((projectiveProductInitial (k := k)).stepProjection (j + 1))) :=
  cancel_final_iso (schemeModulePullbackUnitIso (strictProductCoverOpen (j + 1) i).ι)
    (oldTotalProductLocalIso j i).hom _ _ (oldTotalProductLocalIso_inclusion j i)

/-- The ideal of the previous exceptional curve pulled back by the blowdown is the tensor of the
ideals of the newest exceptional curve and of the strict transform, on the entire stage `j+2`. -/
def oldTotalProductIso (j : ℕ) :
    (schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection (j + 1))).obj
        (schemeKernelIdeal (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
          (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)) ≅
      exceptionalOldTensor (k := k) j :=
  -- The pulled inclusion is stated with the stage-`(j+1)` scheme in the `(A.stage (j+1)).carrier`
  -- form so that its source is literally the object of the local isomorphisms.
  schemeModuleMonicFactorIsoOnOpenCover (strictProductCoverOpen (j + 1))
    (strictProductCoverOpen_covers (j + 1)) (exceptionalOldProduct j)
    (pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
      (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
      ((projectiveProductInitial (k := k)).stepProjection (j + 1)))
    (oldTotalProductLocalIso j) (oldTotalProductLocalIso_map j)

/-- The whole-stage isomorphism preserves the literal ambient ideal inclusion. -/
@[reassoc] theorem oldTotalProductIso_inclusion (j : ℕ) :
    (oldTotalProductIso (k := k) j).hom ≫ exceptionalOldProduct j =
      pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        ((projectiveProductInitial (k := k)).stepProjection (j + 1)) := by
  unfold oldTotalProductIso
  exact schemeModuleMonicFactorIsoOnOpenCover_comp (strictProductCoverOpen (j + 1))
    (strictProductCoverOpen_covers (j + 1)) (exceptionalOldProduct j)
    (pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
      (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
      ((projectiveProductInitial (k := k)).stepProjection (j + 1)))
    (oldTotalProductLocalIso j) (oldTotalProductLocalIso_map j)

/-- Its restriction to each member of the cover is the local isomorphism. -/
theorem oldTotalProductIso_restrict (j : ℕ) (i : Option Bool) :
    (schemeModulePullback (strictProductCoverOpen (j + 1) i).ι).map
        (oldTotalProductIso (k := k) j).hom = (oldTotalProductLocalIso j i).hom := by
  unfold oldTotalProductIso
  exact schemeModuleMonicFactorIsoOnOpenCover_map (strictProductCoverOpen (j + 1))
    (strictProductCoverOpen_covers (j + 1)) (exceptionalOldProduct j)
    (pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
      (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
      ((projectiveProductInitial (k := k)).stepProjection (j + 1)))
    (oldTotalProductLocalIso j) (oldTotalProductLocalIso_map j) i

/-- The ambient inclusion uniquely determines this whole-stage factor. -/
theorem oldTotalProductIso_hom_unique (j : ℕ)
    (a : (schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection (j + 1))).obj
        (schemeKernelIdeal (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
          (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)) ⟶
      exceptionalOldTensor (k := k) j)
    (ha : a ≫ exceptionalOldProduct j =
      pulledKernelInclusion (Y := ((projectiveProductInitial (k := k)).stage (j + 1)).carrier)
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        ((projectiveProductInitial (k := k)).stepProjection (j + 1))) :
    a = (oldTotalProductIso j).hom :=
  (cancel_mono (exceptionalOldProduct j)).mp (ha.trans (oldTotalProductIso_inclusion j).symm)

end KltDP.Examples.FrobeniusOldExceptionalTotalProduct
