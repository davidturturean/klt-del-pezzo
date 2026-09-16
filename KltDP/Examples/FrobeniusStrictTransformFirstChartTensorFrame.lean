import KltDP.Examples.FrobeniusStrictTransformFirstChartProduct
import KltDP.Geometry.SchemeKernelAffineOpenFrame
import KltDP.Geometry.SchemeStructureTensorScalar

/-!
# The original exceptional-times-strict tensor frame on the first stage chart

The actual global exceptional kernel has the proved regular equation u on the
literal first affine open. Its normalized kernel frame tensors with the original
successor strict-kernel frame. The chosen pullback tensor comparison preserves the
original product map, and the resulting frame multiplies by the actual blowdown's
pullback of the previous strict equation. All fields and n,m including zero remain.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFirstChartTensorFrame

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformInvertible
open FrobeniusGraphPicardClassAffine FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformFirstChartProduct

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance firstChartTensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

local instance firstTensorOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The literal center-fiber inclusion of the successor stage, with its codomain written as
`projectiveContactStage (n + 1)` so that all statements below live on one scheme expression. -/
def stepExceptionalInclusionSucc (n : ℕ) :
    PointBlowupGluing.globalCenterFiber ((projectiveProductInitial (k := k)).stage n).chart
        (originPoint (k := k)) ((projectiveProductInitial (k := k)).stage n).center_closed ⟶
      projectiveContactStage (k := k) (n + 1) :=
  stepExceptionalInclusion n

instance firstTensorStepExceptionalInclusionSucc_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (stepExceptionalInclusionSucc (k := k) n) :=
  inferInstanceAs (IsClosedImmersion (PointBlowupGluing.globalCenterFiberι
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed))

/-- The original exceptional coordinate in the ambient first chart's section ring. -/
def firstExceptionalAmbientEquation (n : ℕ) :
    Γ(projectiveContactStage (k := k) (n + 1), (firstAffineOpen (n + 1)).1) :=
  (((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord)

/-- The literal global center-fiber kernel ideal on the first affine open, regarded in the
section ring of the successor stage scheme. -/
def stepExceptionalFirstOpenIdeal (n : ℕ) :
    Ideal Γ(projectiveContactStage (k := k) (n + 1), (firstAffineOpen (n + 1)).1) :=
  (stepExceptionalInclusionSucc n).ker.ideal (firstAffineOpen (n + 1))

/-- The original global fiber kernel has this equation on the literal first affine open. -/
theorem stepExceptionalIdeal_firstAffineOpen (n : ℕ) :
    stepExceptionalFirstOpenIdeal (k := k) n = Ideal.span {firstExceptionalAmbientEquation n} := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.trans
    (((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have h : (stepExceptionalFirstOpenIdeal (k := k) n).comap e.toRingHom = Ideal.span {uCoord} :=
    stepExceptionalFirstChartIdeal_eq_span n
  change stepExceptionalFirstOpenIdeal (k := k) n = Ideal.span {e uCoord}
  calc
    _ = ((stepExceptionalFirstOpenIdeal (k := k) n).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {uCoord}).map e.toRingHom := by rw [h]
    _ = _ := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

/-- The original exceptional coordinate stays regular under the two section-ring isomorphisms. -/
theorem firstExceptionalAmbientEquation_regular (n : ℕ) :
    firstExceptionalAmbientEquation (k := k) n ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) (n + 1), (firstAffineOpen (n + 1)).1) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.trans
    (((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).symm.commRingCatIsoToRingEquiv
  apply mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
  change e.symm (e uCoord) ∈ nonZeroDivisors (planeRing k)
  simpa only [e.symm_apply_apply] using mem_nonZeroDivisors_of_ne_zero (uCoord_ne_zero (k := k))

/-- The same coordinate in the original first affine open's own global section ring. -/
def firstExceptionalOpenEquation (n : ℕ) :
    Γ((firstAffineOpen (k := k) (n + 1)).1.toScheme, ⊤) :=
  gluedAffineEquation (firstAffineOpen (n + 1)) (firstExceptionalAmbientEquation n)

/-- The actual global exceptional kernel is framed on the original first affine open. -/
def stepExceptionalFirstOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        (schemeKernelIdeal (stepExceptionalInclusionSucc n)) :=
  schemeKernelAffineOpenFrame (stepExceptionalInclusionSucc n) (firstAffineOpen (n + 1))
    (firstExceptionalAmbientEquation n) (stepExceptionalIdeal_firstAffineOpen n)
    (firstExceptionalAmbientEquation_regular n)

theorem stepExceptionalFirstOpenFrame_inclusion (n : ℕ) :
    (stepExceptionalFirstOpenFrame (k := k) n).hom ≫
        pulledKernelInclusion (stepExceptionalInclusionSucc n) (firstAffineOpen (n + 1)).1.ι =
      (schemeScalarEnd (Y := (firstAffineOpen (k := k) (n + 1)).1.toScheme)
          (firstExceptionalOpenEquation n) :
        _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf) :=
  schemeKernelAffineOpenFrame_inclusion (stepExceptionalInclusionSucc n) (firstAffineOpen (n + 1))
    (firstExceptionalAmbientEquation n) (stepExceptionalIdeal_firstAffineOpen n)
    (firstExceptionalAmbientEquation_regular n)

/-- The original chart blowdown pulls the previous residual equation back with one exceptional factor. -/
theorem firstStepEquation_section_factorization (m : ℕ) :
    (coordinateBlowdown (k := k)).appTop (firstEquation (m + 1)) =
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord * firstEquation m := by
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv
    (firstStepEquation_factorization (k := k) m)
  change (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).hom
        ((coordinateBlowdown (k := k)).appTop (firstEquation (m + 1)))) =
    (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (uCoord * (vCoord - uCoord ^ m)) at h
  rw [Iso.hom_inv_id_apply, map_mul] at h
  exact h

/-- The actual chart-section pullback of the previous strict equation on the original successor open. -/
def firstTotalOpenEquation (n m : ℕ) :
    Γ((firstAffineOpen (k := k) (n + 1)).1.toScheme, ⊤) :=
  (firstAffineOpen (n + 1)).1.topIso.inv
    ((((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv
      ((coordinateBlowdown (k := k)).appTop (firstEquation (m + 1))))

/-- Its exceptional and strict factors are the sections of the two original normalized frames. -/
theorem firstTotalOpenEquation_factorization (n m : ℕ) :
    firstTotalOpenEquation (k := k) n m =
      firstExceptionalOpenEquation n * firstOpenEquation (n + 1) m := by
  simp only [firstTotalOpenEquation, firstStepEquation_section_factorization, map_mul,
    firstExceptionalOpenEquation, firstOpenEquation, gluedAffineEquation,
    firstExceptionalAmbientEquation, firstAmbientEquation]

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

/-- The tensor of the original two kernel frames, through the chosen original pullback tensor iso. -/
def strictExceptionalFirstOpenFrame (n m : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        (strictExceptionalTensorLine n m).obj :=
  (schemeStructureTensorRightIso
      (_root_.SheafOfModules.unit (firstAffineOpen (n + 1)).1.toScheme.ringCatSheaf)).symm ≪≫
    tensorIso (stepExceptionalFirstOpenFrame n) (strictKernelFirstOpenFrame (n + 1) m) ≪≫
    (schemeModulePullbackTensorIso (firstAffineOpen (n + 1)).1.ι
      (schemeKernelIdeal (stepExceptionalInclusionSucc n))
      (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1))))).symm

/-- The original product inclusion multiplies by the actual total-transform chart equation. -/
theorem strictExceptionalFirstOpenFrame_inclusion (n m : ℕ) :
    (strictExceptionalFirstOpenFrame (k := k) n m).hom ≫
      (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map
        (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom =
        (schemeScalarEnd (Y := (firstAffineOpen (k := k) (n + 1)).1.toScheme)
            (firstTotalOpenEquation n m) :
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit
              (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf) := by
  rw [firstTotalOpenEquation_factorization]
  exact tensorFrame_inclusion_generic (firstAffineOpen (k := k) (n + 1)).1.ι
    (schemeKernelIdealι (stepExceptionalInclusionSucc n))
    (schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1))))
    (stepExceptionalFirstOpenFrame n) (strictKernelFirstOpenFrame (n + 1) m)
    (firstExceptionalOpenEquation n) (firstOpenEquation (n + 1) m)
    (stepExceptionalFirstOpenFrame_inclusion n) (strictKernelFirstOpenFrame_inclusion (n + 1) m)

end KltDP.Examples.FrobeniusStrictTransformFirstChartTensorFrame
