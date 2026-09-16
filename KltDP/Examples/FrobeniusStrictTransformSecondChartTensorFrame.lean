import KltDP.Examples.FrobeniusStrictTransformSecondChartProduct
import KltDP.Geometry.SchemeKernelAffineOpenFrame
import KltDP.Geometry.SchemeStructureTensorScalar

/-!
# The original exceptional-times-strict tensor frame on the second stage chart

The literal global exceptional kernel has the regular equation v on the original
second Rees open. Its normalized frame tensors with the original strict-kernel
frame through the chosen pullback tensor comparison. The resulting original
product inclusion multiplies by the actual blowdown's pulled previous equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformSecondChartTensorFrame

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusExceptionalSuccessorChart FrobeniusGraphPicardClassAffine
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformSecondChartAlgebra
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformSecondChartProduct

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance secondChartTensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

local instance secondTensorOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The literal center-fiber inclusion of the successor stage, with its codomain written as
`projectiveContactStage (n + 1)` so that all statements below live on one scheme expression. -/
def stepExceptionalInclusionSucc (n : ℕ) :
    PointBlowupGluing.globalCenterFiber ((projectiveProductInitial (k := k)).stage n).chart
        (originPoint (k := k)) ((projectiveProductInitial (k := k)).stage n).center_closed ⟶
      projectiveContactStage (k := k) (n + 1) :=
  stepExceptionalInclusion n

instance secondTensorStepExceptionalInclusionSucc_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (stepExceptionalInclusionSucc (k := k) n) :=
  inferInstanceAs (IsClosedImmersion (PointBlowupGluing.globalCenterFiberι
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed))

/-- The actual exceptional coordinate in the original second open's ambient section ring. -/
def secondExceptionalAmbientEquation (n : ℕ) :
    Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1) :=
  secondSectionsEquiv n vEquation

/-- The literal global center-fiber kernel ideal on the second affine open, regarded in the
section ring of the successor stage scheme. -/
def stepExceptionalSecondOpenIdeal (n : ℕ) :
    Ideal Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1) :=
  (stepExceptionalInclusionSucc n).ker.ideal (secondAffineOpen n)

/-- The original global fiber kernel has this exact principal ideal on the original second open. -/
theorem stepExceptionalIdeal_secondAffineOpen (n : ℕ) :
    stepExceptionalSecondOpenIdeal (k := k) n = Ideal.span {secondExceptionalAmbientEquation n} := by
  let e := secondSectionsEquiv (k := k) n
  have h : (stepExceptionalSecondOpenIdeal (k := k) n).comap e.toRingHom =
      Ideal.span {vEquation} :=
    stepExceptionalSecondChartIdeal_eq_span n
  change stepExceptionalSecondOpenIdeal (k := k) n = Ideal.span {e vEquation}
  calc
    _ = ((stepExceptionalSecondOpenIdeal (k := k) n).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {vEquation}).map e.toRingHom := by rw [h]
    _ = _ := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

/-- Regularity is inherited from the original Rees chart equation. -/
theorem secondExceptionalAmbientEquation_regular (n : ℕ) :
    secondExceptionalAmbientEquation (k := k) n ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1) := by
  let e := secondSectionsEquiv (k := k) n
  apply mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
  change e.symm (e vEquation) ∈ nonZeroDivisors (reesVChartRing k)
  simpa only [e.symm_apply_apply] using
    chartBaseMap_equation_mem_nonZeroDivisors (centerIdeal (k := k)) centerV

/-- The exceptional equation in the original second open scheme's own global sections. -/
def secondExceptionalOpenEquation (n : ℕ) :
    Γ((secondAffineOpen (k := k) n).1.toScheme, ⊤) :=
  gluedAffineEquation (secondAffineOpen n) (secondExceptionalAmbientEquation n)

/-- A normalized frame of the original global exceptional kernel on its actual second open. -/
def stepExceptionalSecondOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (schemeKernelIdeal (stepExceptionalInclusionSucc n)) :=
  schemeKernelAffineOpenFrame (stepExceptionalInclusionSucc n) (secondAffineOpen n)
    (secondExceptionalAmbientEquation n) (stepExceptionalIdeal_secondAffineOpen n)
    (secondExceptionalAmbientEquation_regular n)

theorem stepExceptionalSecondOpenFrame_inclusion (n : ℕ) :
    (stepExceptionalSecondOpenFrame (k := k) n).hom ≫
        pulledKernelInclusion (stepExceptionalInclusionSucc n) (secondAffineOpen n).1.ι =
      (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme)
          (secondExceptionalOpenEquation n) :
        _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) :=
  schemeKernelAffineOpenFrame_inclusion (stepExceptionalInclusionSucc n) (secondAffineOpen n)
    (secondExceptionalAmbientEquation n) (stepExceptionalIdeal_secondAffineOpen n)
    (secondExceptionalAmbientEquation_regular n)

/-- The actual second Rees chart's original morphism to the previous plane chart. -/
def secondCoordinateBlowdown : Spec (CommRingCat.of (reesVChartRing k)) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV))

/-- The original section map has exactly one exceptional factor, including the terminal residual. -/
theorem secondStepEquation_section_factorization (m : ℕ) :
    (secondCoordinateBlowdown (k := k)).appTop (firstEquation (m + 1)) =
      (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv vEquation *
        (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv
          (secondResidualEquation m) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV)))
    (vCoord - uCoord ^ (m + 1))
  change (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv
      (chartBaseMap (centerIdeal (k := k)) centerV (vCoord - uCoord ^ (m + 1))) =
    (secondCoordinateBlowdown (k := k)).appTop (firstEquation (m + 1)) at h
  rw [secondTotalEquation_factorization, map_mul] at h
  exact h.symm

/-- The actual pulled previous equation, through the two original second-open section comparisons. -/
def secondTotalOpenEquation (n m : ℕ) :
    Γ((secondAffineOpen (k := k) n).1.toScheme, ⊤) :=
  (secondAffineOpen n).1.topIso.inv
    (((secondStageChart n).appIso ⊤).inv
      ((secondCoordinateBlowdown (k := k)).appTop (firstEquation (m + 1))))

theorem secondTotalOpenEquation_factorization (n m : ℕ) :
    secondTotalOpenEquation (k := k) n m =
      secondExceptionalOpenEquation n * secondOpenEquation n m := by
  change (secondAffineOpen n).1.topIso.inv
      (((secondStageChart n).appIso ⊤).inv
        ((secondCoordinateBlowdown (k := k)).appTop (firstEquation (m + 1)))) =
    (secondAffineOpen n).1.topIso.inv (((secondStageChart n).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv vEquation)) *
      (secondAffineOpen n).1.topIso.inv (((secondStageChart n).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv (secondResidualEquation m)))
  rw [secondStepEquation_section_factorization, map_mul, map_mul]

/-- Generic form of the tensor-frame inclusion: two normalized kernel frames on an actual open
tensor to a frame whose inclusion multiplies by the product of the two equations. -/
private theorem tensorFrame_inclusion_generic {Y Z : Scheme.{u}} (i : Z ⟶ Y) {M N : Y.Modules}
    (g : M ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (h : N ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (Fe : _root_.SheafOfModules.unit Z.ringCatSheaf ≅ (schemeModulePullback i).obj M)
    (Fs : _root_.SheafOfModules.unit Z.ringCatSheaf ≅ (schemeModulePullback i).obj N)
    (d₁ d₂ : Γ(Z, ⊤))
    (he : Fe.hom ≫ (schemeModulePullback i).map g ≫ (schemeModulePullbackUnitIso i).hom =
      schemeScalarEnd d₁)
    (hs : Fs.hom ≫ (schemeModulePullback i).map h ≫ (schemeModulePullbackUnitIso i).hom =
      schemeScalarEnd d₂) :
    ((schemeStructureTensorRightIso (_root_.SheafOfModules.unit Z.ringCatSheaf)).symm ≪≫
        tensorIso Fe Fs ≪≫ (schemeModulePullbackTensorIso i M N).symm).hom ≫
      (schemeModulePullback i).map ((g ⊗ h) ≫
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom) ≫
      (schemeModulePullbackUnitIso i).hom =
    schemeScalarEnd (d₁ * d₂) := by
  rw [← schemeModulePullbackTensorIso_product, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_hom, tensorIso_hom, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    ← tensor_comp_assoc, he, hs, schemeStructureTensor_scalar_mul]

/-- The tensor of the original exceptional and strict frames through the chosen pullback comparison. -/
def strictExceptionalSecondOpenFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (strictExceptionalTensorLine n m).obj :=
  (schemeStructureTensorRightIso
      (_root_.SheafOfModules.unit (secondAffineOpen n).1.toScheme.ringCatSheaf)).symm ≪≫
    tensorIso (stepExceptionalSecondOpenFrame n) (strictKernelSecondOpenFrame n m) ≪≫
    (schemeModulePullbackTensorIso (secondAffineOpen n).1.ι
      (schemeKernelIdeal (stepExceptionalInclusionSucc n))
      (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1))))).symm

/-- The literal product inclusion multiplies by the actual pulled previous equation. -/
theorem strictExceptionalSecondOpenFrame_inclusion (n m : ℕ) :
    (strictExceptionalSecondOpenFrame (k := k) n m).hom ≫
      (schemeModulePullback (secondAffineOpen n).1.ι).map (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom =
        (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme)
            (secondTotalOpenEquation n m) :
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) := by
  rw [secondTotalOpenEquation_factorization]
  exact tensorFrame_inclusion_generic (secondAffineOpen (k := k) n).1.ι
    (schemeKernelIdealι (stepExceptionalInclusionSucc n))
    (schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1))))
    (stepExceptionalSecondOpenFrame n) (strictKernelSecondOpenFrame n m)
    (secondExceptionalOpenEquation n) (secondOpenEquation n m)
    (stepExceptionalSecondOpenFrame_inclusion n) (strictKernelSecondOpenFrame_inclusion n m)

end KltDP.Examples.FrobeniusStrictTransformSecondChartTensorFrame
