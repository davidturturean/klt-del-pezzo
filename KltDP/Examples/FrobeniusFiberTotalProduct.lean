import KltDP.Examples.FrobeniusFiberPuncture
import KltDP.Examples.FrobeniusStrictTransformFirstChartComparison
import KltDP.Examples.FrobeniusStrictTransformSecondChartComparison
import KltDP.Examples.FrobeniusStrictTransformProductCover
import KltDP.Geometry.SchemeModuleMonicFactorOnCover
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The whole-stage pullback-ideal identity for the strict `b`-fibre

The two Rees affine opens of stage `n+1` and the complement of the newest exceptional curve `E_n`
cover the stage (the lane's `strictProductCoverOpen n`). On each member this module identifies the
pullback `π^* I(F_n)` of the ideal of the strict fibre `F_n = liftedFiberClosure n` with the tensor
line `I(E_n) ⊗ I(F_{n+1})`, compatibly with the product inclusion `fiberExceptionalProduct n` into
the structure sheaf:

* on the first Rees open the strict fibre has the regular equation `v` at both stages, `E_n` has
  the equation `u`, and the chart blowdown pulls `v` back to `u·v`
  (`fiberTotalProductFirstOpenIso_inclusion`);
* on the second Rees open the strict fibre of stage `n+1` is absent (unit frame `1`), and the
  pulled fibre equation is the exceptional equation `v` of `E_n`
  (`fiberTotalProductSecondOpenIso_inclusion`);
* on the centre complement the member is `fiberTotalProductPunctureIso` from
  `FrobeniusFiberPuncture`.

Since the product inclusion is a monomorphism, the accepted monic-factor gluing produces the
whole-stage isomorphism `π^* I(F_n) ≅ I(E_n) ⊗ I(F_{n+1})` (`fiberTotalProductIso`) preserving the
ambient ideal inclusions (`fiberTotalProductIso_inclusion`); its restriction to each member of the
cover is the local isomorphism (`fiberTotalProductIso_restrict`). The Picard relation
`F_{n+1} = π^* F_n - E_n` is drawn in `FrobeniusFiberPicard` (relative to the invertibility of the
stage-`0` strict-fibre ideal, which is not proved in this lane).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusFiberTotalProduct

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusExceptionalSuccessorChart FrobeniusFiberClosure FrobeniusFiberStrictCharts
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformProductCover
open FrobeniusStrictTransformFirstChartProduct FrobeniusStrictTransformSecondChartProduct
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformFirstChartTensorFrame FrobeniusStrictTransformSecondChartTensorFrame
open FrobeniusStrictTransformFirstChartComparison FrobeniusStrictTransformSecondChartComparison
open FrobeniusFiberPuncture

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance fiberTotalSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance fiberTotalModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance fiberTotalModulesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

/-! ### Generic lemmas, as in the lane's tensor-frame, product-kernel and total-product modules -/

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

local instance fiberTotalOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ### The strict fibre framed on the current chart open -/

/-- The fibre coordinate `v` in the ambient section ring of the current chart open. -/
def fiberFirstAmbientEquation (n : ℕ) :
    Γ(projectiveContactStage (k := k) n, (firstAffineOpen n).1) :=
  (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord)

/-- The kernel ideal of the strict fibre on the current chart open, in the ambient section ring. -/
def fiberStrictFirstOpenIdeal (n : ℕ) :
    Ideal Γ(projectiveContactStage (k := k) n, (firstAffineOpen n).1) :=
  (fiberClosureInclusion (projectiveProductInitial (k := k)) n).ker.ideal (firstAffineOpen n)

theorem fiberStrictIdeal_firstAffineOpen (n : ℕ) :
    fiberStrictFirstOpenIdeal (k := k) n = Ideal.span {fiberFirstAmbientEquation n} := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.trans
    (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have h : (fiberStrictFirstOpenIdeal (k := k) n).comap e.toRingHom = Ideal.span {vCoord} :=
    fiberStrictFirstChartIdeal_eq_span n
  change fiberStrictFirstOpenIdeal (k := k) n = Ideal.span {e vCoord}
  calc
    _ = ((fiberStrictFirstOpenIdeal (k := k) n).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    _ = (Ideal.span {vCoord}).map e.toRingHom := by rw [h]
    _ = _ := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl

theorem fiberFirstAmbientEquation_regular (n : ℕ) :
    fiberFirstAmbientEquation (k := k) n ∈
      nonZeroDivisors Γ(projectiveContactStage (k := k) n, (firstAffineOpen n).1) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.trans
    (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).symm.commRingCatIsoToRingEquiv
  have hv : vCoord (k := k) ≠ 0 := Polynomial.X_ne_zero
  apply mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
  change e.symm (e vCoord) ∈ nonZeroDivisors (planeRing k)
  simpa only [e.symm_apply_apply] using mem_nonZeroDivisors_of_ne_zero hv

/-- The fibre coordinate in the chart open's own global section ring. -/
def fiberFirstOpenEquation (n : ℕ) : Γ((firstAffineOpen (k := k) n).1.toScheme, ⊤) :=
  gluedAffineEquation (firstAffineOpen n) (fiberFirstAmbientEquation n)

/-- The strict-fibre kernel framed on the current chart open. -/
def fiberKernelFirstOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) n).1.ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n)) :=
  schemeKernelAffineOpenFrame (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    (firstAffineOpen n) (fiberFirstAmbientEquation n) (fiberStrictIdeal_firstAffineOpen n)
    (fiberFirstAmbientEquation_regular n)

theorem fiberKernelFirstOpenFrame_inclusion (n : ℕ) :
    (fiberKernelFirstOpenFrame (k := k) n).hom ≫
        pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
          (firstAffineOpen n).1.ι =
      (schemeScalarEnd (Y := (firstAffineOpen (k := k) n).1.toScheme) (fiberFirstOpenEquation n) :
        _root_.SheafOfModules.unit (firstAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) n).1.toScheme.ringCatSheaf) :=
  schemeKernelAffineOpenFrame_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    (firstAffineOpen n) (fiberFirstAmbientEquation n) (fiberStrictIdeal_firstAffineOpen n)
    (fiberFirstAmbientEquation_regular n)

/-! ### The first Rees open: `π^*(v) = u·v` -/

/-- The chart blowdown pulls the fibre coordinate back to `u·v`. -/
theorem fiberStep_section :
    (coordinateBlowdown (k := k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord) =
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord *
        (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartSubstitution (k := k))))
    (vCoord (k := k))
  change (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (chartSubstitution vCoord) =
    (Spec.map (CommRingCat.ofHom (chartSubstitution (k := k)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord) at h
  rw [chartSubstitution_v, map_mul] at h
  rw [coordinateBlowdown_eq]
  exact h.symm

/-- The pulled fibre equation on the first Rees open of the next stage. -/
def fiberTotalFirstOpenEquation (n : ℕ) : Γ((firstAffineOpen (k := k) (n + 1)).1.toScheme, ⊤) :=
  (firstAffineOpen (n + 1)).1.topIso.inv
    ((((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv
      ((coordinateBlowdown (k := k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord)))

theorem fiberTotalFirstOpenEquation_factorization (n : ℕ) :
    fiberTotalFirstOpenEquation (k := k) n =
      firstExceptionalOpenEquation n * fiberFirstOpenEquation (n + 1) := by
  change (firstAffineOpen (n + 1)).1.topIso.inv
      ((((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv
        ((coordinateBlowdown (k := k)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord))) =
    (firstAffineOpen (n + 1)).1.topIso.inv
        ((((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord)) *
      (firstAffineOpen (n + 1)).1.topIso.inv
        ((((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord))
  rw [fiberStep_section, map_mul, map_mul]

theorem firstOpenStepProjection_fiberEquation (n : ℕ) :
    (firstOpenStepProjection (k := k) n).appTop (fiberFirstOpenEquation n) =
      fiberTotalFirstOpenEquation n :=
  schemeOpenChartMap_section (((projectiveProductInitial (k := k)).stage (n + 1)).chart)
    (((projectiveProductInitial (k := k)).stage n).chart) (coordinateBlowdown (k := k))
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord)

/-- The strict-fibre frame of stage `n` transported to the pulled kernel on the first open. -/
def fiberTotalFirstOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) :=
  schemeKernelFrameOnSquare (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    (firstAffineOpen n).1.ι (firstOpenStepProjection n) (firstAffineOpen (n + 1)).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (firstOpenStepProjection_square n)
    (fiberKernelFirstOpenFrame n)

theorem fiberTotalFirstOpenFrame_inclusion (n : ℕ) :
    (fiberTotalFirstOpenFrame (k := k) n).hom ≫
      (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map
        (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
          ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom =
        (schemeScalarEnd (Y := (firstAffineOpen (k := k) (n + 1)).1.toScheme)
            (fiberTotalFirstOpenEquation n) :
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit
              (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf) := by
  have h := schemeKernelFrameOnSquare_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n) (firstAffineOpen n).1.ι
    (firstOpenStepProjection n) (firstAffineOpen (n + 1)).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (firstOpenStepProjection_square n)
    (fiberKernelFirstOpenFrame n) (fiberFirstOpenEquation n)
    (fiberKernelFirstOpenFrame_inclusion n)
  simpa only [firstOpenStepProjection_fiberEquation] using h

/-- The source object of a morphism, kept reducible so that it unfolds to the literal object. -/
abbrev homSource {C : Type*} [Category C] {A B : C} (_f : A ⟶ B) : C := A

/-- The tensor line `I(E_n) ⊗ I(F_{n+1})` on stage `n+1`, literally the source of the product
inclusion `fiberExceptionalProduct n`. -/
abbrev fiberExceptionalTensor (n : ℕ) : (projectiveContactStage (k := k) (n + 1)).Modules :=
  homSource (fiberExceptionalProduct (k := k) n)

/-- The tensor of the frames of `E_n` and of `F_{n+1}` on the first open. -/
def fiberExceptionalFirstOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        (fiberExceptionalTensor (k := k) n) :=
  (schemeStructureTensorRightIso
      (_root_.SheafOfModules.unit (firstAffineOpen (n + 1)).1.toScheme.ringCatSheaf)).symm ≪≫
    tensorIso (stepExceptionalFirstOpenFrame n) (fiberKernelFirstOpenFrame (n + 1)) ≪≫
    (schemeModulePullbackTensorIso (firstAffineOpen (n + 1)).1.ι
      (schemeKernelIdeal
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc n))
      (schemeKernelIdeal
        (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))).symm

theorem fiberExceptionalFirstOpenFrame_inclusion (n : ℕ) :
    (fiberExceptionalFirstOpenFrame (k := k) n).hom ≫
      (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom =
        (schemeScalarEnd (Y := (firstAffineOpen (k := k) (n + 1)).1.toScheme)
            (fiberTotalFirstOpenEquation n) :
          _root_.SheafOfModules.unit (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit
              (firstAffineOpen (k := k) (n + 1)).1.toScheme.ringCatSheaf) := by
  rw [fiberTotalFirstOpenEquation_factorization]
  exact tensorFrame_inclusion_generic (firstAffineOpen (k := k) (n + 1)).1.ι
    (schemeKernelIdealι
      (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc n))
    (schemeKernelIdealι (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))
    (stepExceptionalFirstOpenFrame n) (fiberKernelFirstOpenFrame (n + 1))
    (firstExceptionalOpenEquation n) (fiberFirstOpenEquation (n + 1))
    (stepExceptionalFirstOpenFrame_inclusion n) (fiberKernelFirstOpenFrame_inclusion (n + 1))

/-- On the first Rees open, the pulled ideal of `F_n` is the tensor of the ideals of `E_n` and
`F_{n+1}`. -/
def fiberTotalProductFirstOpenIso (n : ℕ) :
    (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) ≅
      (schemeModulePullback (firstAffineOpen (k := k) (n + 1)).1.ι).obj
        (fiberExceptionalTensor (k := k) n) :=
  (fiberTotalFirstOpenFrame n).symm ≪≫ fiberExceptionalFirstOpenFrame n

theorem fiberTotalProductFirstOpenIso_inclusion (n : ℕ) :
    (fiberTotalProductFirstOpenIso (k := k) n).hom ≫
      (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom =
    (schemeModulePullback (firstAffineOpen (n + 1)).1.ι).map
      (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (firstAffineOpen (n + 1)).1.ι).hom := by
  simp only [fiberTotalProductFirstOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [fiberExceptionalFirstOpenFrame_inclusion, ← fiberTotalFirstOpenFrame_inclusion,
    Iso.inv_hom_id_assoc]

/-! ### The second Rees open: the strict fibre is absent -/

/-- The strict fibre of stage `n+1` misses the second Rees open, so there its kernel ideal is
generated by `1`. -/
theorem fiberStrictIdeal_secondAffineOpen (n : ℕ) :
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).ker.ideal
        (secondAffineOpen n) =
      Ideal.span {(1 : Γ(projectiveContactStage (k := k) (n + 1), (secondAffineOpen n).1))} := by
  have hbot : (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) ⁻¹ᵁ
      (secondAffineOpen (k := k) n).1 = ⊥ := by
    apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_bot]
    exact Set.eq_empty_iff_forall_not_mem.mpr fun x hx =>
      (fiberStrict_secondChart_isEmpty (k := k) n).false ⟨x, hx⟩
  haveI : Subsingleton
      Γ(liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1),
        (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) ⁻¹ᵁ
          (secondAffineOpen (k := k) n).1) := by
    rw [hbot]
    infer_instance
  rw [Ideal.span_singleton_one, Scheme.Hom.ker_apply, Ideal.eq_top_iff_one, RingHom.mem_ker]
  exact Subsingleton.elim _ _

/-- The equation `1` of the absent strict fibre in the second open's own section ring. -/
def fiberSecondOpenEquation (n : ℕ) : Γ((secondAffineOpen (k := k) n).1.toScheme, ⊤) :=
  gluedAffineEquation (secondAffineOpen n) 1

theorem fiberSecondOpenEquation_eq_one (n : ℕ) : fiberSecondOpenEquation (k := k) n = 1 := by
  simp only [fiberSecondOpenEquation, gluedAffineEquation, map_one]

/-- The absent strict fibre has the unit frame on the second open. -/
def fiberKernelSecondOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
  schemeKernelAffineOpenFrame (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (secondAffineOpen n) 1 (fiberStrictIdeal_secondAffineOpen n) (Submonoid.one_mem _)

theorem fiberKernelSecondOpenFrame_inclusion (n : ℕ) :
    (fiberKernelSecondOpenFrame (k := k) n).hom ≫
        pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
          (secondAffineOpen n).1.ι =
      (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme)
          (fiberSecondOpenEquation n) :
        _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) :=
  schemeKernelAffineOpenFrame_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (secondAffineOpen n) 1 (fiberStrictIdeal_secondAffineOpen n) (Submonoid.one_mem _)

/-- The second-chart blowdown pulls the fibre coordinate back to the exceptional equation `v`. -/
theorem fiberSecondStep_section :
    (secondCoordinateBlowdown (k := k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord) =
      (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv vEquation := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV)))
    (vCoord (k := k))
  change (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv
      (chartBaseMap (centerIdeal (k := k)) centerV vCoord) =
    (secondCoordinateBlowdown (k := k)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord) at h
  exact h.symm

/-- The pulled fibre equation on the second Rees open. -/
def fiberTotalSecondOpenEquation (n : ℕ) : Γ((secondAffineOpen (k := k) n).1.toScheme, ⊤) :=
  (secondAffineOpen n).1.topIso.inv
    (((secondStageChart n).appIso ⊤).inv
      ((secondCoordinateBlowdown (k := k)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord)))

theorem fiberTotalSecondOpenEquation_factorization (n : ℕ) :
    fiberTotalSecondOpenEquation (k := k) n =
      secondExceptionalOpenEquation n * fiberSecondOpenEquation n := by
  rw [fiberSecondOpenEquation_eq_one, mul_one]
  change (secondAffineOpen n).1.topIso.inv
      (((secondStageChart n).appIso ⊤).inv
        ((secondCoordinateBlowdown (k := k)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord))) =
    (secondAffineOpen n).1.topIso.inv (((secondStageChart n).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv vEquation))
  rw [fiberSecondStep_section]

theorem secondOpenStepProjection_fiberEquation (n : ℕ) :
    (secondOpenStepProjection (k := k) n).appTop (fiberFirstOpenEquation n) =
      fiberTotalSecondOpenEquation n :=
  schemeOpenChartMap_section (secondStageChart n)
    (((projectiveProductInitial (k := k)).stage n).chart) (secondCoordinateBlowdown (k := k))
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv vCoord)

/-- The strict-fibre frame of stage `n` transported to the pulled kernel on the second open. -/
def fiberTotalSecondOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) :=
  schemeKernelFrameOnSquare (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    (firstAffineOpen n).1.ι (secondOpenStepProjection n) (secondAffineOpen n).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (secondOpenStepProjection_square n)
    (fiberKernelFirstOpenFrame n)

theorem fiberTotalSecondOpenFrame_inclusion (n : ℕ) :
    (fiberTotalSecondOpenFrame (k := k) n).hom ≫
      (schemeModulePullback (secondAffineOpen n).1.ι).map
        (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
          ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom =
        (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme)
            (fiberTotalSecondOpenEquation n) :
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) := by
  have h := schemeKernelFrameOnSquare_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n) (firstAffineOpen n).1.ι
    (secondOpenStepProjection n) (secondAffineOpen n).1.ι
    ((projectiveProductInitial (k := k)).stepProjection n) (secondOpenStepProjection_square n)
    (fiberKernelFirstOpenFrame n) (fiberFirstOpenEquation n)
    (fiberKernelFirstOpenFrame_inclusion n)
  simpa only [secondOpenStepProjection_fiberEquation] using h

/-- The tensor of the frames of `E_n` and of the (absent) `F_{n+1}` on the second open. -/
def fiberExceptionalSecondOpenFrame (n : ℕ) :
    _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (fiberExceptionalTensor (k := k) n) :=
  (schemeStructureTensorRightIso
      (_root_.SheafOfModules.unit (secondAffineOpen n).1.toScheme.ringCatSheaf)).symm ≪≫
    tensorIso (stepExceptionalSecondOpenFrame n) (fiberKernelSecondOpenFrame n) ≪≫
    (schemeModulePullbackTensorIso (secondAffineOpen n).1.ι
      (schemeKernelIdeal
        (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc n))
      (schemeKernelIdeal
        (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))).symm

theorem fiberExceptionalSecondOpenFrame_inclusion (n : ℕ) :
    (fiberExceptionalSecondOpenFrame (k := k) n).hom ≫
      (schemeModulePullback (secondAffineOpen n).1.ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom =
        (schemeScalarEnd (Y := (secondAffineOpen (k := k) n).1.toScheme)
            (fiberTotalSecondOpenEquation n) :
          _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf ⟶
            _root_.SheafOfModules.unit (secondAffineOpen (k := k) n).1.toScheme.ringCatSheaf) := by
  rw [fiberTotalSecondOpenEquation_factorization]
  exact tensorFrame_inclusion_generic (secondAffineOpen (k := k) n).1.ι
    (schemeKernelIdealι
      (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc n))
    (schemeKernelIdealι (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))
    (stepExceptionalSecondOpenFrame n) (fiberKernelSecondOpenFrame n)
    (secondExceptionalOpenEquation n) (fiberSecondOpenEquation n)
    (stepExceptionalSecondOpenFrame_inclusion n) (fiberKernelSecondOpenFrame_inclusion n)

/-- On the second Rees open, the pulled ideal of `F_n` is the tensor of the ideals of `E_n` and
of the (absent) `F_{n+1}`. -/
def fiberTotalProductSecondOpenIso (n : ℕ) :
    (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) ≅
      (schemeModulePullback (secondAffineOpen (k := k) n).1.ι).obj
        (fiberExceptionalTensor (k := k) n) :=
  (fiberTotalSecondOpenFrame n).symm ≪≫ fiberExceptionalSecondOpenFrame n

theorem fiberTotalProductSecondOpenIso_inclusion (n : ℕ) :
    (fiberTotalProductSecondOpenIso (k := k) n).hom ≫
      (schemeModulePullback (secondAffineOpen n).1.ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom =
    (schemeModulePullback (secondAffineOpen n).1.ι).map
      (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (secondAffineOpen n).1.ι).hom := by
  simp only [fiberTotalProductSecondOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [fiberExceptionalSecondOpenFrame_inclusion, ← fiberTotalSecondOpenFrame_inclusion,
    Iso.inv_hom_id_assoc]

/-! ### The whole-stage gluing -/

/-- Tensor cancellation for the invertible exceptional line makes the product inclusion
injective. -/
theorem fiberExceptionalProduct_mono (n : ℕ) : Mono (fiberExceptionalProduct (k := k) n) := by
  letI := lineTensor_preservesMonomorphisms (stepExceptionalIdealLine (k := k) n)
  rw [fiberExceptionalProduct, tensorHom_def', Category.assoc, structureTensorRightIso_naturality]
  haveI : Mono (schemeKernelIdealι
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono (schemeKernelIdealι (Y := projectiveContactStage (k := k) (n + 1))
      (stepExceptionalInclusion (k := k) n)) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono (schemeKernelIdeal (Y := projectiveContactStage (k := k) (n + 1))
      (stepExceptionalInclusion (k := k) n) ◁
      schemeKernelIdealι (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
    inferInstanceAs (Mono ((tensorLeft (stepExceptionalIdealLine (k := k) n).obj).map
      (schemeKernelIdealι (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))))
  infer_instance

local instance fiberTotalProductMono (n : ℕ) : Mono (fiberExceptionalProduct (k := k) n) :=
  fiberExceptionalProduct_mono n

/-- The three local isomorphisms between the literal pullbacks, indexed by the cover. -/
def fiberTotalProductLocalIso (n : ℕ) (i : Option Bool) :
    (schemeModulePullback (strictProductCoverOpen (k := k) n i).ι).obj
        ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) ≅
      (schemeModulePullback (strictProductCoverOpen (k := k) n i).ι).obj
        (fiberExceptionalTensor (k := k) n) := by
  cases i with
  | none => exact fiberTotalProductFirstOpenIso n
  | some i =>
    cases i with
    | false => exact fiberTotalProductSecondOpenIso n
    | true => exact fiberTotalProductPunctureIso n

/-- Each member retains both ambient maps, including the pullback unit comparison. -/
theorem fiberTotalProductLocalIso_inclusion (n : ℕ) (i : Option Bool) :
    (fiberTotalProductLocalIso (k := k) n i).hom ≫
      (schemeModulePullback (strictProductCoverOpen n i).ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (strictProductCoverOpen n i).ι).hom =
    (schemeModulePullback (strictProductCoverOpen n i).ι).map
      (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (strictProductCoverOpen n i).ι).hom := by
  cases i with
  | none => exact fiberTotalProductFirstOpenIso_inclusion n
  | some i =>
    cases i with
    | false => exact fiberTotalProductSecondOpenIso_inclusion n
    | true => exact fiberTotalProductPunctureIso_inclusion n

/-- Cancellation of the unit isomorphism gives equality of the literal pullback maps. -/
theorem fiberTotalProductLocalIso_map (n : ℕ) (i : Option Bool) :
    (fiberTotalProductLocalIso (k := k) n i).hom ≫
      (schemeModulePullback (strictProductCoverOpen n i).ι).map (fiberExceptionalProduct n) =
    (schemeModulePullback (strictProductCoverOpen n i).ι).map
      (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n)) :=
  cancel_final_iso (schemeModulePullbackUnitIso (strictProductCoverOpen n i).ι)
    (fiberTotalProductLocalIso n i).hom _ _ (fiberTotalProductLocalIso_inclusion n i)

/-- The ideal of the strict fibre pulled back by the blowdown is the tensor of the ideals of the
newest exceptional curve and of the next strict fibre, on the entire stage `n+1`. -/
def fiberTotalProductIso (n : ℕ) :
    (schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n)) ≅
      fiberExceptionalTensor (k := k) n :=
  schemeModuleMonicFactorIsoOnOpenCover (strictProductCoverOpen n)
    (strictProductCoverOpen_covers n) (fiberExceptionalProduct n)
    (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
      ((projectiveProductInitial (k := k)).stepProjection n))
    (fiberTotalProductLocalIso n) (fiberTotalProductLocalIso_map n)

/-- The whole-stage isomorphism preserves the literal ambient ideal inclusion. -/
@[reassoc] theorem fiberTotalProductIso_inclusion (n : ℕ) :
    (fiberTotalProductIso (k := k) n).hom ≫ fiberExceptionalProduct n =
      pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n) :=
  schemeModuleMonicFactorIsoOnOpenCover_comp (strictProductCoverOpen n)
    (strictProductCoverOpen_covers n) (fiberExceptionalProduct n)
    (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
      ((projectiveProductInitial (k := k)).stepProjection n))
    (fiberTotalProductLocalIso n) (fiberTotalProductLocalIso_map n)

/-- Its restriction to each member of the cover is the local isomorphism. -/
theorem fiberTotalProductIso_restrict (n : ℕ) (i : Option Bool) :
    (schemeModulePullback (strictProductCoverOpen n i).ι).map
        (fiberTotalProductIso (k := k) n).hom = (fiberTotalProductLocalIso n i).hom :=
  schemeModuleMonicFactorIsoOnOpenCover_map (strictProductCoverOpen n)
    (strictProductCoverOpen_covers n) (fiberExceptionalProduct n)
    (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
      ((projectiveProductInitial (k := k)).stepProjection n))
    (fiberTotalProductLocalIso n) (fiberTotalProductLocalIso_map n) i

/-- The ambient inclusion uniquely determines this whole-stage factor. -/
theorem fiberTotalProductIso_hom_unique (n : ℕ)
    (a : (schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n)) ⟶
      fiberExceptionalTensor (k := k) n)
    (ha : a ≫ fiberExceptionalProduct n =
      pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n)) :
    a = (fiberTotalProductIso n).hom :=
  (cancel_mono (fiberExceptionalProduct n)).mp (ha.trans (fiberTotalProductIso_inclusion n).symm)

end KltDP.Examples.FrobeniusFiberTotalProduct
