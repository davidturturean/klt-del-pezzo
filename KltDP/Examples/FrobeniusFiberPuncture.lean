import KltDP.Examples.FrobeniusFiberStrictCharts
import KltDP.Examples.FrobeniusStrictTransformProductPuncture
import KltDP.Geometry.SchematicImageOpenImmersion
import KltDP.Geometry.SchematicImageGlued
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The strict `b`-fibre over the centre complement

Over the complement `nextPuncture n` of the newest exceptional curve `E_n` in stage `n+1`, the
one-step blowdown `π` is an isomorphism onto the complement `currentPuncture n` of the centre in
stage `n`. The strict fibre `F_{n+1} = liftedFiberClosure n+1` maps onto the strict fibre `F_n`
(`fiberStepProjection`, obtained from the schematic image of `F_{n+1} → stage n`, whose ideal is
the ideal of `F_n` because the two chart lines agree after the blowdown), and over the centre
complements this map is an isomorphism, so `F_{n+1}` restricted to the complement is the pullback
of `F_n` restricted to the complement. Following the accepted `FrobeniusStrictTransformStepPuncture`
construction this gives the kernel-module identification

  `π^* I(F_n) |_{nextPuncture n} ≅ I(F_{n+1}) |_{nextPuncture n}`

preserving the ambient inclusions (`fiberPulledPreviousPunctureIso_inclusion`), and, since `I(E_n)`
is the structure sheaf there, the centre-complement member of the three-open comparison
`π^* I(F_n) ≅ I(E_n) ⊗ I(F_{n+1})` for the product morphism `fiberExceptionalProduct n`
(`fiberTotalProductPunctureIso_inclusion`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace KltDP.Examples.FrobeniusFiberPuncture

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusFiberClosure FrobeniusFiberStrictCharts
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformProductPuncture
open FrobeniusStrictTransformFirstChartProduct
open FrobeniusStageComplement.PlaneChartedScheme

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance fiberPunctureModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-! ### Generic restriction lemmas, as in the accepted step-puncture module -/

private theorem restrictSquare_range {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) (s : A ⟶ B)
    (h : s ≫ b = a ≫ p) (U : Y.Opens) :
    Set.range ((a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s).base ⊆
      Set.range (b ⁻¹ᵁ U).ι.base := by
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨s.base x.val, ?_⟩, rfl⟩
  change (s ≫ b).base x.val ∈ U
  rw [h]
  exact x.property

private theorem restrictSquare_comm {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) (s : A ⟶ B)
    (h : s ≫ b = a ≫ p) (U : Y.Opens)
    (t : (a ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme ⟶ (b ⁻¹ᵁ U).toScheme)
    (ht : t ≫ (b ⁻¹ᵁ U).ι = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s) :
    (a ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U) = t ≫ (b ∣_ U) := by
  apply (cancel_mono U.ι).mp
  calc
    _ = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ a ≫ p := by
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
    _ = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s ≫ b := by rw [h]
    _ = (t ≫ (b ⁻¹ᵁ U).ι) ≫ b := by
      simpa only [Category.assoc] using (congrArg (fun f => f ≫ b) ht).symm
    _ = _ := by simp only [Category.assoc, morphismRestrict_ι]

private theorem restrictSquare_surjective {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) (s : A ⟶ B)
    (h : s ≫ b = a ≫ p) (U : Y.Opens)
    (t : (a ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme ⟶ (b ⁻¹ᵁ U).toScheme)
    (ht : t ≫ (b ⁻¹ᵁ U).ι = (a ⁻¹ᵁ (p ⁻¹ᵁ U)).ι ≫ s)
    (hs : Surjective s) : Surjective t := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := hs.1 y.val
  have hmem : x ∈ a ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    change (a ≫ p).base x ∈ U
    rw [← h]
    change b.base (s.base x) ∈ U
    rw [hx]
    exact y.property
  refine ⟨⟨x, hmem⟩, (b ⁻¹ᵁ U).ι.isOpenEmbedding.injective ?_⟩
  change (t ≫ (b ⁻¹ᵁ U).ι).base ⟨x, hmem⟩ = (b ⁻¹ᵁ U).ι.base y
  rw [ht]
  exact hx

/-! ### Generic kernel-module lemmas, as in the accepted step-puncture module -/

private theorem kernel_eqToIso_hom_ι {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (eqToIso (congrArg schemeKernelIdeal h)).hom ≫ schemeKernelIdealι g =
      schemeKernelIdealι f := by
  subst g
  exact Category.id_comp _

private theorem precompKernel_asIso_inv_ι {A B Y : Scheme.{u}}
    (s : A ⟶ B) [IsIso s] (b : B ⟶ Y) :
    (schemeKernelPrecompIso (asIso s) b).inv ≫ schemeKernelIdealι (s ≫ b) =
      schemeKernelIdealι b :=
  schemeKernelPrecompIso_inv_ι (asIso s) b

private theorem localKernelSquareIso_inclusion {A B X Y : Scheme.{u}}
    (a : A ⟶ X) (b : B ⟶ Y) (p : X ⟶ Y) [IsOpenImmersion p]
    (s : A ⟶ B) [IsIso s] (h : a ≫ p = s ≫ b) :
    ((schemeModulePullback p).mapIso
        ((schemeKernelPrecompIso (asIso s) b).symm ≪≫
          eqToIso (congrArg schemeKernelIdeal h.symm)) ≪≫
        schemeKernelPostcompOpenIso a p).hom ≫ schemeKernelIdealι a =
      (schemeModulePullback p).map (schemeKernelIdealι b) ≫
        (schemeModulePullbackUnitIso p).hom := by
  rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    schemeKernelPostcompOpenIso_hom_ι, ← Category.assoc, ← Functor.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    kernel_eqToIso_hom_ι h.symm, precompKernel_asIso_inv_ι]

private theorem localToGlobalKernelIso_inclusion {A B X Y : Scheme.{u}}
    (f : A ⟶ X) (g : B ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (p : V.toScheme ⟶ U.toScheme)
    (e : (schemeModulePullback p).obj (schemeKernelIdeal (f ∣_ U)) ≅
      schemeKernelIdeal (g ∣_ V))
    (he : e.hom ≫ schemeKernelIdealι (g ∣_ V) =
      (schemeModulePullback p).map (schemeKernelIdealι (f ∣_ U)) ≫
        (schemeModulePullbackUnitIso p).hom) :
    ((schemeModulePullback p).mapIso (localKernelToGlobalPullbackIso f U).symm ≪≫
        e ≪≫ localKernelToGlobalPullbackIso g V).hom ≫ pulledKernelInclusion g V.ι =
      (schemeModulePullback p).map (pulledKernelInclusion f U.ι) ≫
        (schemeModulePullbackUnitIso p).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    localKernelToGlobalPullbackIso_inclusion, he]
  rw [← Category.assoc, ← Functor.map_comp,
    ← localKernelToGlobalPullbackIso_inclusion f U,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem kernelPullbackCompIso_inclusion {A X Y Z : Scheme.{u}}
    (f : A ⟶ Y) (i : X ⟶ Y) (g : Z ⟶ X) :
    (schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f) ≫
        pulledKernelInclusion f (g ≫ i) =
      (schemeModulePullback g).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso g).hom := by
  simp only [pulledKernelInclusion, Category.assoc]
  rw [← Category.assoc ((schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f)),
    ← (schemeModulePullbackCompIso g i).hom.naturality (schemeKernelIdealι f),
    Category.assoc, schemeModulePullbackCompIso_unit]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

private theorem totalKernelTransport_inclusion {A B X Y U V : Scheme.{u}}
    (f : A ⟶ Y) (g : B ⟶ X) (i : V ⟶ Y) (j : U ⟶ X)
    (p : U ⟶ V) (q : U ⟶ Y) (h : q = p ≫ i)
    (e : (schemeModulePullback p).obj ((schemeModulePullback i).obj (schemeKernelIdeal f)) ≅
      (schemeModulePullback j).obj (schemeKernelIdeal g))
    (he : e.hom ≫ pulledKernelInclusion g j =
      (schemeModulePullback p).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso p).hom) :
    ((eqToIso (congrArg schemeModulePullback h)).app (schemeKernelIdeal f) ≪≫
        ((schemeModulePullbackCompIso p i).app (schemeKernelIdeal f)).symm ≪≫ e).hom ≫
      pulledKernelInclusion g j = pulledKernelInclusion f q := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [he, ← kernelPullbackCompIso_inclusion f i p, Iso.inv_hom_id_app_assoc]
  exact pulledKernelInclusion_congr f h

/-! ### Generic unit-tensor lemmas, as in the lane's product-puncture module -/

private def unitTensorLeftIso {C : Type*} [Category C] [MonoidalCategory C] {O : C}
    (e : 𝟙_ C ≅ O) (M : C) : O ⊗ M ≅ M :=
  (tensorRight M).mapIso e.symm ≪≫ λ_ M

private theorem unitTensorLeftIso_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) {M N : C} (g : M ⟶ N) :
    O ◁ g ≫ (unitTensorLeftIso e N).hom = (unitTensorLeftIso e M).hom ≫ g := by
  simp only [unitTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorRight_map]
  rw [whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]

private theorem unitTensorLeftIso_eq_right {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) :
    O ◁ e.inv ≫ (ρ_ O).hom = (unitTensorLeftIso e O).hom := by
  simp only [unitTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorRight_map]
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, Category.assoc, ← rightUnitor_naturality, ← leftUnitor_naturality,
    whisker_exchange_assoc, unitors_equal]

private def structureTensorLeftIso {X : Scheme.{u}} (M : X.Modules) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⊗ M ≅ M :=
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  unitTensorLeftIso e M

private theorem structureTensorLeftIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) :
    _root_.SheafOfModules.unit X.ringCatSheaf ◁ g ≫
        (structureTensorLeftIso N).hom = (structureTensorLeftIso M).hom ≫ g :=
  unitTensorLeftIso_naturality _ g

private theorem structure_mul_eq_left (X : Scheme.{u}) :
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
      (structureTensorLeftIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  exact unitTensorLeftIso_eq_right (C := X.Modules) e

variable {k : Type u} [Field k]

local instance fiberPunctureOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ### The strict fibre of the next stage maps onto the strict fibre of the current stage -/

/-- The strict fibre lines of consecutive stages agree after the one-step blowdown. -/
@[reassoc] theorem fiberResidual_stepProjection (n : ℕ) :
    fiberResidual (projectiveProductInitial (k := k)) (n + 1) ≫
        (projectiveProductInitial (k := k)).stepProjection n =
      fiberResidual (projectiveProductInitial (k := k)) n := by
  have h2 : ((projectiveProductInitial (k := k)).stage (n + 1)).chart ≫
      (projectiveProductInitial (k := k)).stepProjection n =
        coordinateBlowdown ≫ ((projectiveProductInitial (k := k)).stage n).chart :=
    PlaneChartedScheme.nextChart_projection ((projectiveProductInitial (k := k)).stage n)
  simp only [fiberResidual]
  rw [Category.assoc, h2, fiberCurve_blowdown_assoc]

/-- The projected strict fibre of the next stage has the ideal of the current strict fibre. -/
theorem fiberStep_composite_ker (n : ℕ) :
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
      (projectiveProductInitial (k := k)).stepProjection n).ker =
        liftedFiberClosureIdeal (projectiveProductInitial (k := k)) n := by
  rw [← SchematicImageOpenImmersion.ker_precompose_openImmersion
    (fiberResidualToClosure (projectiveProductInitial (k := k)) (n + 1))
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
      (projectiveProductInitial (k := k)).stepProjection n),
    ← Category.assoc, fiberResidualToClosure_inclusion, fiberResidual_stepProjection,
    liftedFiberClosureIdeal_eq]

private theorem gluedTo_eqToIso_hom {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h)).hom ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

/-- The schematic image of the projected next strict fibre is the current strict fibre. -/
def fiberStepImageIso (n : ℕ) :
    SchematicImageGlued.image
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
        (projectiveProductInitial (k := k)).stepProjection n) ≅
      liftedFiberClosure (projectiveProductInitial (k := k)) n :=
  eqToIso (congrArg
    (fun I : (projectiveContactStage (k := k) n).IdealSheafData => I.glueData.glued)
    (fiberStep_composite_ker n))

/-- The one-step projection between the strict fibres of consecutive stages. -/
def fiberStepProjection (n : ℕ) :
    liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1) ⟶
      liftedFiberClosure (projectiveProductInitial (k := k)) n :=
  SchematicImageGlued.toImage
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
        (projectiveProductInitial (k := k)).stepProjection n) ≫
    (fiberStepImageIso n).hom

/-- The projection preserves the inclusions and the blowdown. -/
@[reassoc] theorem fiberStepProjection_inclusion (n : ℕ) :
    fiberStepProjection (k := k) n ≫ fiberClosureInclusion (projectiveProductInitial (k := k)) n =
      fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
        (projectiveProductInitial (k := k)).stepProjection n := by
  rw [fiberStepProjection, Category.assoc]
  change SchematicImageGlued.toImage _ ≫
    ((fiberStepImageIso n).hom ≫
      (liftedFiberClosureIdeal (projectiveProductInitial (k := k)) n).gluedTo) = _
  rw [fiberStepImageIso, gluedTo_eqToIso_hom (fiberStep_composite_ker n)]
  exact SchematicImageGlued.toImage_inclusion _

/-- The image of the projected next strict fibre is closed, since the blowdown is proper. -/
theorem fiberStep_composite_range (n : ℕ) :
    Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) n).base =
      Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
        (projectiveProductInitial (k := k)).stepProjection n).base := by
  let g := fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
    (projectiveProductInitial (k := k)).stepProjection n
  letI : IsProper g := inferInstance
  change Set.range (liftedFiberClosureIdeal (projectiveProductInitial (k := k)) n).gluedTo.base =
    Set.range g.base
  rw [Scheme.IdealSheafData.range_gluedTo, ← fiberStep_composite_ker (k := k) n]
  change (g.ker.support : Set (projectiveContactStage (k := k) n)) = Set.range g.base
  rw [Scheme.Hom.support_ker, g.isClosedMap.isClosed_range.closure_eq]

/-- Every point of the current strict fibre is reached by the projection. -/
theorem fiberStepProjection_surjective (n : ℕ) :
    Surjective (fiberStepProjection (k := k) n) := by
  constructor
  intro y
  have hy : (fiberClosureInclusion (projectiveProductInitial (k := k)) n).base y ∈
      Set.range (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ≫
        (projectiveProductInitial (k := k)).stepProjection n).base := by
    rw [← fiberStep_composite_range n]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x,
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n).isClosedEmbedding.injective ?_⟩
  exact (congrArg (fun f => f.base x) (fiberStepProjection_inclusion n)).trans hx

/-! ### The strict fibre over the centre complement -/

/-- The current strict fibre restricted to the centre complement. -/
abbrev fiberPreviousPuncture (n : ℕ) :
    (liftedFiberClosure (projectiveProductInitial (k := k)) n).Opens :=
  fiberClosureInclusion (projectiveProductInitial (k := k)) n ⁻¹ᵁ currentPuncture n

/-- The next strict fibre restricted to the inverse-image complement. -/
abbrev fiberSuccessorPuncture (n : ℕ) :
    (liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1)).Opens :=
  fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ⁻¹ᵁ nextPuncture n

private theorem fiberStep_puncture_range (n : ℕ) :
    Set.range ((fiberSuccessorPuncture (k := k) n).ι ≫
      fiberStepProjection n).base ⊆ Set.range (fiberPreviousPuncture n).ι.base :=
  restrictSquare_range
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    ((projectiveProductInitial (k := k)).stepProjection n)
    (fiberStepProjection n) (fiberStepProjection_inclusion n) (currentPuncture n)

/-- The fibre step projection factored through the two opens. -/
def fiberStepOnPuncture (n : ℕ) :
    (fiberSuccessorPuncture (k := k) n).toScheme ⟶ (fiberPreviousPuncture (k := k) n).toScheme :=
  IsOpenImmersion.lift (fiberPreviousPuncture n).ι
    ((fiberSuccessorPuncture (k := k) n).ι ≫ fiberStepProjection n)
    (fiberStep_puncture_range n)

@[reassoc] theorem fiberStepOnPuncture_ι (n : ℕ) :
    fiberStepOnPuncture (k := k) n ≫ (fiberPreviousPuncture n).ι =
      (fiberSuccessorPuncture n).ι ≫ fiberStepProjection n :=
  IsOpenImmersion.lift_fac _ _ _

theorem fiberStepOnPuncture_square (n : ℕ) :
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n) ≫
        ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n) =
      fiberStepOnPuncture n ≫
        (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n) :=
  restrictSquare_comm
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    ((projectiveProductInitial (k := k)).stepProjection n)
    (fiberStepProjection n) (fiberStepProjection_inclusion n) (currentPuncture n)
    (fiberStepOnPuncture n) (fiberStepOnPuncture_ι n)

instance fiberPreviousPuncture_inclusion_isClosedImmersion (n : ℕ) :
    IsClosedImmersion
      (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (fiberClosureInclusion (projectiveProductInitial (k := k)) n))
    _

instance fiberSuccessorPuncture_inclusion_isClosedImmersion (n : ℕ) :
    IsClosedImmersion
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion)
    (inferInstance :
      IsClosedImmersion (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) _

instance fiberStepOnPuncture_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (fiberStepOnPuncture (k := k) n) := by
  letI : IsClosedImmersion (fiberStepOnPuncture (k := k) n ≫
      (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n)) := by
    rw [← fiberStepOnPuncture_square]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (fiberStepOnPuncture n)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n)

theorem fiberStepOnPuncture_surjective (n : ℕ) :
    Surjective (fiberStepOnPuncture (k := k) n) :=
  restrictSquare_surjective
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    ((projectiveProductInitial (k := k)).stepProjection n)
    (fiberStepProjection n) (fiberStepProjection_inclusion n) (currentPuncture n)
    (fiberStepOnPuncture n) (fiberStepOnPuncture_ι n)
    (fiberStepProjection_surjective n)

/-- Over the centre complement the fibre step projection is an isomorphism. -/
instance fiberStepOnPuncture_isIso (n : ℕ) : IsIso (fiberStepOnPuncture (k := k) n) := by
  letI : IsReduced (fiberPreviousPuncture (k := k) n).toScheme :=
    isReduced_of_isOpenImmersion (fiberPreviousPuncture n).ι
  letI := fiberStepOnPuncture_surjective (k := k) n
  exact isIso_of_isClosedImmersion_of_surjective (fiberStepOnPuncture n)

/-- The strict fibres form a pullback square over the centre complement. -/
theorem fiberStepOnPuncture_isPullback (n : ℕ) :
    IsPullback
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n)
      (fiberStepOnPuncture n)
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
      (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n) :=
  IsPullback.of_vert_isIso ⟨fiberStepOnPuncture_square n⟩

/-! ### The kernel-module identification over the centre complement -/

def fiberLocalPunctureKernelIso (n : ℕ) :
    (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).obj
        (schemeKernelIdeal
          (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n)) ≅
      schemeKernelIdeal
        (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n) :=
  (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).mapIso
    ((schemeKernelPrecompIso (asIso (fiberStepOnPuncture n))
        (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n)).symm ≪≫
      eqToIso (congrArg schemeKernelIdeal (fiberStepOnPuncture_square n).symm)) ≪≫
    schemeKernelPostcompOpenIso
      (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n)
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)

theorem fiberLocalPunctureKernelIso_inclusion (n : ℕ) :
    (fiberLocalPunctureKernelIso (k := k) n).hom ≫
        schemeKernelIdealι
          (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n) =
      (schemeModulePullback
        ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).map
          (schemeKernelIdealι
            (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n)) ≫
        (schemeModulePullbackUnitIso
          ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).hom :=
  localKernelSquareIso_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1) ∣_ nextPuncture n)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n ∣_ currentPuncture n)
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    (fiberStepOnPuncture n) (fiberStepOnPuncture_square n)

def fiberPunctureKernelIso (n : ℕ) :
    (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).obj
        ((schemeModulePullback (currentPuncture n).ι).obj
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
  (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).mapIso
      (localKernelToGlobalPullbackIso
        (fiberClosureInclusion (projectiveProductInitial (k := k)) n) (currentPuncture n)).symm ≪≫
    fiberLocalPunctureKernelIso n ≪≫
      localKernelToGlobalPullbackIso
        (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) (nextPuncture n)

theorem fiberPunctureKernelIso_inclusion (n : ℕ) :
    (fiberPunctureKernelIso (k := k) n).hom ≫
        pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
          (nextPuncture n).ι =
      (schemeModulePullback
        ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).map
          (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
            (currentPuncture n).ι) ≫
        (schemeModulePullbackUnitIso
          ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)).hom :=
  localToGlobalKernelIso_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (currentPuncture n) (nextPuncture n)
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    (fiberLocalPunctureKernelIso n) (fiberLocalPunctureKernelIso_inclusion n)

def fiberTotalPunctureKernelIso (n : ℕ) :
    (schemeModulePullback ((nextPuncture (k := k) n).ι ≫
      (projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n)) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
  (eqToIso (congrArg schemeModulePullback
    (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection n)
      (currentPuncture n)).symm)).app _ ≪≫
    ((schemeModulePullbackCompIso
      ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
      (currentPuncture n).ι).app _).symm ≪≫
    fiberPunctureKernelIso n

private theorem fiberTotalPunctureKernelIso_eq (n : ℕ) :
    fiberTotalPunctureKernelIso (k := k) n =
      (eqToIso (congrArg schemeModulePullback
        (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection n)
          (currentPuncture (k := k) n)).symm)).app
          (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n)) ≪≫
        ((schemeModulePullbackCompIso
          ((projectiveProductInitial (k := k)).stepProjection n ∣_
            currentPuncture (k := k) n)
          (currentPuncture (k := k) n).ι).app
            (schemeKernelIdeal
              (fiberClosureInclusion (projectiveProductInitial (k := k)) n))).symm ≪≫
        fiberPunctureKernelIso (k := k) n :=
  rfl

theorem fiberTotalPunctureKernelIso_inclusion (n : ℕ) :
    (fiberTotalPunctureKernelIso (k := k) n).hom ≫
        pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
          (nextPuncture n).ι =
      pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((nextPuncture n).ι ≫ (projectiveProductInitial (k := k)).stepProjection n) := by
  rw [fiberTotalPunctureKernelIso_eq]
  exact totalKernelTransport_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
    (currentPuncture n).ι (nextPuncture n).ι
    ((projectiveProductInitial (k := k)).stepProjection n ∣_ currentPuncture n)
    ((nextPuncture n).ι ≫ (projectiveProductInitial (k := k)).stepProjection n)
    (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection n)
      (currentPuncture n)).symm
    (fiberPunctureKernelIso n) (fiberPunctureKernelIso_inclusion n)

/-- The one-step pullback of the current strict-fibre ideal agrees with the next strict-fibre
ideal on the centre complement. -/
def fiberPulledPreviousPunctureIso (n : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) n).ι).obj
      ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
  (schemeModulePullbackCompIso (nextPuncture (k := k) n).ι
    ((projectiveProductInitial (k := k)).stepProjection n)).app _ ≪≫
    fiberTotalPunctureKernelIso n

theorem fiberPulledPreviousPunctureIso_inclusion (n : ℕ) :
    (fiberPulledPreviousPunctureIso (k := k) n).hom ≫
        pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
          (nextPuncture n).ι =
      (schemeModulePullback (nextPuncture n).ι).map
        (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
          ((projectiveProductInitial (k := k)).stepProjection n)) ≫
        (schemeModulePullbackUnitIso (nextPuncture n).ι).hom := by
  rw [fiberPulledPreviousPunctureIso, Iso.trans_hom, Category.assoc,
    fiberTotalPunctureKernelIso_inclusion]
  exact kernelPullbackCompIso_inclusion
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
    ((projectiveProductInitial (k := k)).stepProjection n) (nextPuncture n).ι

/-! ### The product comparison over the centre complement -/

/-- The product of the ideal inclusions of `E_n` and of the next strict fibre. -/
def fiberExceptionalProduct (n : ℕ) :
    schemeKernelIdeal (Y := projectiveContactStage (k := k) (n + 1))
        (stepExceptionalInclusion (k := k) n) ⊗
        schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) ⟶
      _root_.SheafOfModules.unit (projectiveContactStage (k := k) (n + 1)).ringCatSheaf :=
  (schemeKernelIdealι (Y := projectiveContactStage (k := k) (n + 1)) (stepExceptionalInclusion n) ⊗
    schemeKernelIdealι (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) ≫
    (schemeStructureTensorRightIso
      (_root_.SheafOfModules.unit (projectiveContactStage (k := k) (n + 1)).ringCatSheaf)).hom

/-- The tensor line `I(E_n) ⊗ I(F_{n+1})` restricts to `I(F_{n+1})` on the centre complement. -/
def fiberExceptionalPunctureIso (n : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) n).ι).obj
        (schemeKernelIdeal (Y := projectiveContactStage (k := k) (n + 1))
            (stepExceptionalInclusion (k := k) n) ⊗
          schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) ≅
      (schemeModulePullback (nextPuncture (k := k) n).ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
  schemeModulePullbackTensorIso (nextPuncture n).ι
      (schemeKernelIdeal (Y := projectiveContactStage (k := k) (n + 1)) (stepExceptionalInclusion n))
      (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) ≪≫
    tensorIso (stepExceptionalPunctureFrame n).symm (Iso.refl _) ≪≫
    structureTensorLeftIso
      ((schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))))

theorem fiberExceptionalPunctureIso_inclusion (n : ℕ) :
    (fiberExceptionalPunctureIso (k := k) n).hom ≫
      pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))
        (nextPuncture n).ι =
    (schemeModulePullback (nextPuncture n).ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (nextPuncture n).ι).hom := by
  rw [fiberExceptionalPunctureIso, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Iso.refl_hom, pulledKernelInclusion, Category.assoc, Category.assoc,
    ← structureTensorLeftIso_naturality, tensorHom_id, ← tensorHom_def_assoc,
    ← structure_mul_eq_left, stepExceptionalPunctureFrame_inv]
  exact schemeModulePullbackTensorIso_product (nextPuncture n).ι
    (schemeKernelIdealι (Y := projectiveContactStage (k := k) (n + 1)) (stepExceptionalInclusion n))
    (schemeKernelIdealι (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)))

/-- On the centre complement, the pulled ideal of `F_n` is the tensor of the ideals of `E_n`
and of `F_{n+1}`. -/
def fiberTotalProductPunctureIso (n : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) n).ι).obj
      ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) n))) ≅
      (schemeModulePullback (nextPuncture (k := k) n).ι).obj
        (schemeKernelIdeal (Y := projectiveContactStage (k := k) (n + 1))
            (stepExceptionalInclusion (k := k) n) ⊗
          schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1))) :=
  fiberPulledPreviousPunctureIso n ≪≫ (fiberExceptionalPunctureIso n).symm

/-- This isomorphism preserves both ambient ideal maps. -/
theorem fiberTotalProductPunctureIso_inclusion (n : ℕ) :
    (fiberTotalProductPunctureIso (k := k) n).hom ≫
      (schemeModulePullback (nextPuncture n).ι).map (fiberExceptionalProduct n) ≫
      (schemeModulePullbackUnitIso (nextPuncture n).ι).hom =
    (schemeModulePullback (nextPuncture n).ι).map
      (pulledKernelInclusion (fiberClosureInclusion (projectiveProductInitial (k := k)) n)
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (nextPuncture n).ι).hom := by
  rw [fiberTotalProductPunctureIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← fiberExceptionalPunctureIso_inclusion, Iso.inv_hom_id_assoc,
    fiberPulledPreviousPunctureIso_inclusion]

end KltDP.Examples.FrobeniusFiberPuncture
