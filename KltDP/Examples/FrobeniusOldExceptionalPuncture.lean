import KltDP.Examples.FrobeniusOldExceptionalSecondChartFrame
import KltDP.Examples.FrobeniusStrictTransformProductPuncture
import KltDP.Geometry.ReducedClosedImageChart
import KltDP.Geometry.SchematicImageGlued
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The older exceptional curve over the centre complement

Over the complement `nextPuncture (j+1)` of the newest exceptional curve `E_{j+1}` in stage `j+2`,
the one-step blowdown `π` is an isomorphism onto the complement `currentPuncture (j+1)` of the
centre in stage `j+1`. The accepted strict transform `C_j = previousStrictTransform (A.stage j)` is
the schematic image of the accepted lift `wholePreviousLift` of `E_j` minus the centre, so that lift
is an open immersion onto `C_j ∩ nextPuncture (j+1)` (`oldPunctureLift`), and `C_j` restricted to
the complement is the pullback of `E_j` restricted to the complement. Following the accepted
`FrobeniusStrictTransformStepPuncture` construction this gives the kernel-module identification

  `π^* I(E_j) |_{nextPuncture} ≅ I(C_j) |_{nextPuncture}`

preserving the ambient inclusions (`oldPulledPreviousPunctureIso_inclusion`), and, since `I(E_{j+1})`
is the structure sheaf there, the centre-complement member of the three-open comparison
`π^* I(E_j) ≅ I(E_{j+1}) ⊗ I(C_j)` for the product morphism `exceptionalOldProduct j`
(`oldTotalProductPunctureIso_inclusion`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalPuncture

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusExceptionalSuccessorChart
open FrobeniusGlobalExceptionalSuccessor FrobeniusStrictTransformClosure
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformStepPuncture FrobeniusStrictTransformProductPuncture
open FrobeniusOldExceptionalChartIdeals FrobeniusOldExceptionalSecondChartFrame

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance oldPunctureModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

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

local instance oldPunctureOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ### The strict transform over the centre complement -/

/-- The exceptional curve `E_j` of stage `j+1` minus the next centre, as an open of `E_j`. -/
abbrev oldFiberPuncture (j : ℕ) :
    (PointBlowupGluing.globalCenterFiber ((projectiveProductInitial (k := k)).stage j).chart
      (originPoint (k := k)) ((projectiveProductInitial (k := k)).stage j).center_closed).Opens :=
  FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j ⁻¹ᵁ
    currentPuncture (k := k) (j + 1)

/-- The restriction of `E_j` to the complement of the next centre. -/
abbrev oldFiberι (j : ℕ) :
    (oldFiberPuncture (k := k) j).toScheme ⟶ (currentPuncture (k := k) (j + 1)).toScheme :=
  FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j ∣_
    currentPuncture (k := k) (j + 1)

instance oldFiberι_isClosedImmersion (j : ℕ) : IsClosedImmersion (oldFiberι (k := k) j) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion
      (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc (k := k) j)) _

/-- The accepted open inclusion of the unchanged centre complement into stage `j+2`. -/
abbrev oldComplementι (j : ℕ) :
    (currentPuncture (k := k) (j + 1)).toScheme ⟶ projectiveContactStage (k := k) (j + 1 + 1) :=
  PointBlowupGluing.complementι ((projectiveProductInitial (k := k)).stage (j + 1)).chart
    (originPoint (k := k)) ((projectiveProductInitial (k := k)).stage (j + 1)).center_closed

theorem oldComplementι_projection (j : ℕ) :
    oldComplementι (k := k) j ≫ (projectiveProductInitial (k := k)).stepProjection (j + 1) =
      (currentPuncture (k := k) (j + 1)).ι :=
  PointBlowupGluing.complementι_projection _ _ _

/-- The strict transform `C_j` over the complement of the next centre. -/
abbrev oldStrictPuncture (j : ℕ) : (previousStrictTransform (previousStage (k := k) j)).Opens :=
  oldExceptionalStrictι j ⁻¹ᵁ nextPuncture (k := k) (j + 1)

/-- The accepted lift of `E_j` minus the centre into stage `j+2`, whose schematic image is `C_j`. -/
def oldLift (j : ℕ) :
    (oldFiberPuncture (k := k) j).toScheme ⟶ projectiveContactStage (k := k) (j + 1 + 1) :=
  wholePreviousLift (previousStage j)

theorem oldLift_eq (j : ℕ) : oldLift (k := k) j = oldFiberι j ≫ oldComplementι j := rfl

theorem oldLift_mem_puncture (j : ℕ) (y : (oldFiberPuncture (k := k) j).toScheme) :
    (oldLift (k := k) j).base y ∈ nextPuncture (k := k) (j + 1) := by
  change ((oldFiberι j ≫ oldComplementι j) ≫
    (projectiveProductInitial (k := k)).stepProjection (j + 1)).base y ∈
      currentPuncture (k := k) (j + 1)
  rw [Category.assoc, oldComplementι_projection]
  exact ((oldFiberι (k := k) j).base y).2

/-- The image of the lift lies in the strict transform. -/
theorem range_oldLift_subset (j : ℕ) :
    Set.range (oldLift (k := k) j).base ⊆ Set.range (oldExceptionalStrictι (k := k) j).base := by
  intro x hx
  have h := Scheme.Hom.range_subset_ker_support (oldLift (k := k) j) hx
  rw [← Scheme.IdealSheafData.range_gluedTo] at h
  exact h

/-- The second-chart curve lies in the closure of the lift, by density of the parameter puncture. -/
theorem range_successorCurve_subset_closure (j : ℕ) :
    Set.range (successorCurveSucc (k := k) j).base ⊆ closure (Set.range (oldLift j).base) := by
  rintro _ ⟨q, rfl⟩
  have hgen : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (Polynomial k)) ∈
      parameterPuncture (k := k) := by
    change (Polynomial.X : Polynomial k) ∉ (⊥ : Ideal (Polynomial k))
    simpa only [Ideal.mem_bot] using (Polynomial.X_ne_zero (R := k))
  have hgeneric : q ∈ closure ({(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (Polynomial k))} :
      Set (PrimeSpectrum (Polynomial k))) :=
    (PrimeSpectrum.le_iff_mem_closure (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (Polynomial k)) q).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr bot_le)
  have hq : q ∈ closure (parameterPuncture (k := k) : Set (Spec (CommRingCat.of (Polynomial k)))) :=
    closure_mono (Set.singleton_subset_iff.mpr hgen) hgeneric
  have himg := image_closure_subset_closure_image (successorCurveSucc (k := k) j).continuous
    ⟨q, hq, rfl⟩
  refine closure_mono ?_ himg
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨(parameterToPreviousPuncture (previousStage (k := k) j)).base ⟨p, hp⟩, ?_⟩
  exact congrArg (fun f => f.base ⟨p, hp⟩)
    (parameterToPreviousPuncture_wholeLift (previousStage (k := k) j))

/-- The strict transform is the closure of the lift of `E_j` minus the centre. -/
theorem range_oldStrict (j : ℕ) :
    Set.range (oldExceptionalStrictι (k := k) j).base = closure (Set.range (oldLift j).base) := by
  apply Set.Subset.antisymm
  · have h : Set.range (oldExceptionalStrictι (k := k) j).base =
        closure (Set.range (successorCurveSucc (k := k) j).base) :=
      range_previousStrictι (previousStage j)
    rw [h]
    exact closure_minimal (range_successorCurve_subset_closure j) isClosed_closure
  · exact closure_minimal (range_oldLift_subset j)
      (oldExceptionalStrictι (k := k) j).isClosedEmbedding.isClosed_range

/-- The accepted factorization of the lift through its schematic image `C_j`. -/
def oldToStrict (j : ℕ) :
    (oldFiberPuncture (k := k) j).toScheme ⟶ previousStrictTransform (previousStage (k := k) j) :=
  SchematicImageGlued.toImage (oldLift j)

@[reassoc] theorem oldToStrict_ι (j : ℕ) :
    oldToStrict (k := k) j ≫ oldExceptionalStrictι j = oldLift j :=
  SchematicImageGlued.toImage_inclusion (oldLift j)

instance oldToStrict_isOpenImmersion (j : ℕ) : IsOpenImmersion (oldToStrict (k := k) j) :=
  ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image (oldFiberι j) (oldComplementι j)
    (oldExceptionalStrictι j) (oldToStrict j) (oldToStrict_ι j) (range_oldStrict j)

theorem range_oldToStrict_subset (j : ℕ) :
    Set.range (oldToStrict (k := k) j).base ⊆ Set.range (oldStrictPuncture j).ι.base := by
  rintro _ ⟨y, rfl⟩
  refine ⟨⟨(oldToStrict j).base y, ?_⟩, rfl⟩
  change (oldToStrict (k := k) j ≫ oldExceptionalStrictι j).base y ∈ nextPuncture (k := k) (j + 1)
  rw [oldToStrict_ι]
  exact oldLift_mem_puncture j y

/-- The lift of `E_j` minus the centre, as a map onto `C_j` over the complement. -/
def oldPunctureLift (j : ℕ) :
    (oldFiberPuncture (k := k) j).toScheme ⟶ (oldStrictPuncture (k := k) j).toScheme :=
  IsOpenImmersion.lift (oldStrictPuncture j).ι (oldToStrict j) (range_oldToStrict_subset j)

@[reassoc] theorem oldPunctureLift_ι (j : ℕ) :
    oldPunctureLift (k := k) j ≫ (oldStrictPuncture j).ι = oldToStrict j :=
  IsOpenImmersion.lift_fac _ _ _

instance oldPunctureLift_isOpenImmersion (j : ℕ) : IsOpenImmersion (oldPunctureLift (k := k) j) := by
  letI : IsOpenImmersion (oldPunctureLift (k := k) j ≫ (oldStrictPuncture j).ι) := by
    rw [oldPunctureLift_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (oldStrictPuncture j).ι

theorem oldPunctureLift_surjective (j : ℕ) :
    Function.Surjective (oldPunctureLift (k := k) j).base := by
  intro z
  have hrange : Set.range (oldComplementι (k := k) j).base =
      (nextPuncture (k := k) (j + 1) : Set (projectiveContactStage (k := k) (j + 1 + 1))) :=
    PointBlowupGluing.range_complementι _ _ _
  have hz : (oldExceptionalStrictι (k := k) j).base z.1 ∈
      Set.range (oldComplementι (k := k) j).base := by
    rw [hrange]
    exact z.2
  obtain ⟨p, hp⟩ := hz
  have hp' : p ∈ Set.range (oldFiberι (k := k) j).base := by
    rw [← ReducedClosedImageChart.preimage_closure_range (oldFiberι j) (oldComplementι j)]
    change (oldComplementι (k := k) j).base p ∈
      closure (Set.range (oldLift (k := k) j).base)
    rw [hp, ← range_oldStrict]
    exact ⟨z.1, rfl⟩
  obtain ⟨y, rfl⟩ := hp'
  refine ⟨y, (oldStrictPuncture (k := k) j).ι.isOpenEmbedding.injective ?_⟩
  change (oldPunctureLift (k := k) j ≫ (oldStrictPuncture j).ι).base y = z.1
  rw [oldPunctureLift_ι]
  apply (oldExceptionalStrictι (k := k) j).isClosedEmbedding.injective
  change (oldToStrict (k := k) j ≫ oldExceptionalStrictι j).base y = _
  rw [oldToStrict_ι]
  exact hp

instance oldPunctureLift_isIso (j : ℕ) : IsIso (oldPunctureLift (k := k) j) := by
  haveI : Epi (oldPunctureLift (k := k) j).base :=
    (TopCat.epi_iff_surjective _).mpr (oldPunctureLift_surjective j)
  exact IsOpenImmersion.to_iso _

/-- The lift composed with the restricted strict inclusion and blowdown is the restricted `E_j`. -/
theorem oldPunctureLift_square (j : ℕ) :
    oldPunctureLift (k := k) j ≫ (oldExceptionalStrictι j ∣_ nextPuncture (j + 1)) ≫
        ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1)) =
      oldFiberι j := by
  apply (cancel_mono (currentPuncture (k := k) (j + 1)).ι).mp
  have hp : ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_
        currentPuncture (j + 1)) ≫ (currentPuncture (k := k) (j + 1)).ι =
      (nextPuncture (k := k) (j + 1)).ι ≫ (projectiveProductInitial (k := k)).stepProjection (j + 1) :=
    morphismRestrict_ι _ _
  have ha : (oldExceptionalStrictι (k := k) j ∣_ nextPuncture (j + 1)) ≫
        (nextPuncture (k := k) (j + 1)).ι =
      (oldStrictPuncture j).ι ≫ oldExceptionalStrictι j :=
    morphismRestrict_ι _ _
  rw [Category.assoc, Category.assoc, hp,
    ← Category.assoc (oldExceptionalStrictι (k := k) j ∣_ nextPuncture (j + 1)), ha,
    Category.assoc, oldPunctureLift_ι_assoc, oldToStrict_ι_assoc, oldLift_eq, Category.assoc,
    oldComplementι_projection]

/-- The original restricted inclusions form the accepted square over the centre complement. -/
theorem oldStrictOnPuncture_square (j : ℕ) :
    (oldExceptionalStrictι (k := k) j ∣_ nextPuncture (j + 1)) ≫
        ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1)) =
      inv (oldPunctureLift j) ≫ oldFiberι j := by
  rw [← oldPunctureLift_square, IsIso.inv_hom_id_assoc]

/-- The strict transform over the complement is the pullback of `E_j` over the complement. -/
theorem oldStrictOnPuncture_isPullback (j : ℕ) :
    IsPullback (oldExceptionalStrictι (k := k) j ∣_ nextPuncture (j + 1))
      (inv (oldPunctureLift j))
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))
      (oldFiberι j) :=
  IsPullback.of_vert_isIso ⟨oldStrictOnPuncture_square j⟩

/-! ### The kernel-module identification over the centre complement -/

/-- The local kernels compared through the lift and the restricted blowdown isomorphism. -/
def oldLocalPunctureKernelIso (j : ℕ) :
    (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))).obj
        (schemeKernelIdeal (oldFiberι j)) ≅
      schemeKernelIdeal (oldExceptionalStrictι j ∣_ nextPuncture (j + 1)) :=
  (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))).mapIso
    ((schemeKernelPrecompIso (asIso (inv (oldPunctureLift j))) (oldFiberι j)).symm ≪≫
      eqToIso (congrArg schemeKernelIdeal (oldStrictOnPuncture_square j).symm)) ≪≫
    schemeKernelPostcompOpenIso (oldExceptionalStrictι j ∣_ nextPuncture (j + 1))
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))

theorem oldLocalPunctureKernelIso_inclusion (j : ℕ) :
    (oldLocalPunctureKernelIso (k := k) j).hom ≫
        schemeKernelIdealι (oldExceptionalStrictι j ∣_ nextPuncture (j + 1)) =
      (schemeModulePullback
        ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))).map
          (schemeKernelIdealι (oldFiberι j)) ≫
        (schemeModulePullbackUnitIso
          ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_
            currentPuncture (j + 1))).hom := by
  have h := localKernelSquareIso_inclusion
    (oldExceptionalStrictι (k := k) j ∣_ nextPuncture (j + 1)) (oldFiberι j)
    ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))
    (inv (oldPunctureLift j)) (oldStrictOnPuncture_square j)
  -- `exact h` unfolds the kernel comparison through the sheaf-of-modules composition and
  -- times out; the congruence closure only needs the literal definition of the isomorphism.
  convert h using 3

/-- Both kernels are the pullbacks of the whole-stage kernels of `E_j` and `C_j`. -/
def oldPunctureKernelIso (j : ℕ) :
    (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))).obj
        ((schemeModulePullback (currentPuncture (k := k) (j + 1)).ι).obj
          (schemeKernelIdeal
            (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j))) ≅
      (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) :=
  (schemeModulePullback
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))).mapIso
      (localKernelToGlobalPullbackIso
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        (currentPuncture (j + 1))).symm ≪≫
    oldLocalPunctureKernelIso j ≪≫
      localKernelToGlobalPullbackIso (oldExceptionalStrictι j) (nextPuncture (j + 1))

theorem oldPunctureKernelIso_inclusion (j : ℕ) :
    (oldPunctureKernelIso (k := k) j).hom ≫
        pulledKernelInclusion (oldExceptionalStrictι j) (nextPuncture (j + 1)).ι =
      (schemeModulePullback
        ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))).map
          (pulledKernelInclusion
            (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
            (currentPuncture (j + 1)).ι) ≫
        (schemeModulePullbackUnitIso
          ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_
            currentPuncture (j + 1))).hom := by
  have h := localToGlobalKernelIso_inclusion
    (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc (k := k) j)
    (oldExceptionalStrictι j) (currentPuncture (j + 1)) (nextPuncture (j + 1))
    ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))
    (oldLocalPunctureKernelIso j) (oldLocalPunctureKernelIso_inclusion j)
  convert h using 3

/-- Reassociate the pullback of `I(E_j)` through the restricted-blowdown square. -/
def oldTotalPunctureKernelIso (j : ℕ) :
    (schemeModulePullback ((nextPuncture (k := k) (j + 1)).ι ≫
      (projectiveProductInitial (k := k)).stepProjection (j + 1))).obj
        (schemeKernelIdeal
          (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)) ≅
      (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) :=
  (eqToIso (congrArg schemeModulePullback
    (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection (j + 1))
      (currentPuncture (j + 1))).symm)).app _ ≪≫
    ((schemeModulePullbackCompIso
      ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))
      (currentPuncture (j + 1)).ι).app _).symm ≪≫
    oldPunctureKernelIso j

theorem oldTotalPunctureKernelIso_inclusion (j : ℕ) :
    (oldTotalPunctureKernelIso (k := k) j).hom ≫
        pulledKernelInclusion (oldExceptionalStrictι j) (nextPuncture (j + 1)).ι =
      pulledKernelInclusion
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        ((nextPuncture (j + 1)).ι ≫ (projectiveProductInitial (k := k)).stepProjection (j + 1)) := by
  have h := totalKernelTransport_inclusion
    (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc (k := k) j)
    (oldExceptionalStrictι j) (currentPuncture (j + 1)).ι (nextPuncture (j + 1)).ι
    ((projectiveProductInitial (k := k)).stepProjection (j + 1) ∣_ currentPuncture (j + 1))
    ((nextPuncture (j + 1)).ι ≫ (projectiveProductInitial (k := k)).stepProjection (j + 1))
    (morphismRestrict_ι ((projectiveProductInitial (k := k)).stepProjection (j + 1))
      (currentPuncture (j + 1))).symm
    (oldPunctureKernelIso j) (oldPunctureKernelIso_inclusion j)
  convert h using 3

/-- On the centre complement, the pullback of `I(E_j)` is the kernel module of `C_j`. -/
def oldPulledPreviousPunctureIso (j : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
      ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection (j + 1))).obj
        (schemeKernelIdeal
          (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j))) ≅
      (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) :=
  (schemeModulePullbackCompIso (Z := projectiveContactStage (k := k) (j + 1))
    (nextPuncture (k := k) (j + 1)).ι
    ((projectiveProductInitial (k := k)).stepProjection (j + 1))).app _ ≪≫
    oldTotalPunctureKernelIso j

theorem oldPulledPreviousPunctureIso_inclusion (j : ℕ) :
    (oldPulledPreviousPunctureIso (k := k) j).hom ≫
        pulledKernelInclusion (oldExceptionalStrictι j) (nextPuncture (j + 1)).ι =
      (schemeModulePullback (nextPuncture (j + 1)).ι).map
        (pulledKernelInclusion
          (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
          ((projectiveProductInitial (k := k)).stepProjection (j + 1))) ≫
        (schemeModulePullbackUnitIso (nextPuncture (j + 1)).ι).hom := by
  rw [oldPulledPreviousPunctureIso, Iso.trans_hom, Category.assoc,
    oldTotalPunctureKernelIso_inclusion, Iso.app_hom]
  -- all implicit scheme arguments are pinned to the `projectiveContactStage` forms so that
  -- the generic lemma is literally the goal
  exact kernelPullbackCompIso_inclusion (X := projectiveContactStage (k := k) (j + 1 + 1))
    (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc (k := k) j)
    ((projectiveProductInitial (k := k)).stepProjection (j + 1)) (nextPuncture (j + 1)).ι

/-! ### The product comparison over the centre complement -/

/-- The unit frame of `I(E_{j+1})` on the centre complement, in the second-chart-module form of
the inclusion of `E_{j+1}`. -/
def exceptionalNewPunctureFrame (j : ℕ) :
    _root_.SheafOfModules.unit (nextPuncture (k := k) (j + 1)).toScheme.ringCatSheaf ≅
      (schemeModulePullback (nextPuncture (j + 1)).ι).obj
        (schemeKernelIdeal
          (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc
            (k := k) (j + 1))) :=
  stepExceptionalPunctureFrame (j + 1)

theorem exceptionalNewPunctureFrame_inv (j : ℕ) :
    (exceptionalNewPunctureFrame (k := k) j).inv =
      pulledKernelInclusion
        (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc (j + 1))
        (nextPuncture (j + 1)).ι :=
  stepExceptionalPunctureFrame_inv (j + 1)

/-- The tensor line `I(E_{j+1}) ⊗ I(C_j)` restricts to `I(C_j)` on the centre complement. -/
def exceptionalOldPunctureIso (j : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
        (schemeKernelIdeal
            (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc
              (k := k) (j + 1)) ⊗
          schemeKernelIdeal (oldExceptionalStrictι (k := k) j)) ≅
      (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)) :=
  schemeModulePullbackTensorIso (nextPuncture (j + 1)).ι
      (schemeKernelIdeal
        (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc (j + 1)))
      (schemeKernelIdeal (oldExceptionalStrictι j)) ≪≫
    tensorIso (exceptionalNewPunctureFrame j).symm (Iso.refl _) ≪≫
    structureTensorLeftIso
      ((schemeModulePullback (nextPuncture (j + 1)).ι).obj
        (schemeKernelIdeal (oldExceptionalStrictι j)))

theorem exceptionalOldPunctureIso_inclusion (j : ℕ) :
    (exceptionalOldPunctureIso (k := k) j).hom ≫
      pulledKernelInclusion (oldExceptionalStrictι j) (nextPuncture (j + 1)).ι =
    (schemeModulePullback (nextPuncture (j + 1)).ι).map (exceptionalOldProduct j) ≫
      (schemeModulePullbackUnitIso (nextPuncture (j + 1)).ι).hom := by
  rw [exceptionalOldPunctureIso, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Iso.refl_hom, pulledKernelInclusion, Category.assoc, Category.assoc,
    ← structureTensorLeftIso_naturality, tensorHom_id, ← tensorHom_def_assoc,
    ← structure_mul_eq_left, exceptionalNewPunctureFrame_inv]
  exact schemeModulePullbackTensorIso_product (nextPuncture (j + 1)).ι
    (schemeKernelIdealι
      (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc (j + 1)))
    (schemeKernelIdealι (oldExceptionalStrictι j))

/-- On the centre complement, the pulled ideal of `E_j` is the tensor of the ideals of `E_{j+1}`
and of the strict transform of `E_j`. -/
def oldTotalProductPunctureIso (j : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
      ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection (j + 1))).obj
        (schemeKernelIdeal
          (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j))) ≅
      (schemeModulePullback (nextPuncture (k := k) (j + 1)).ι).obj
        (schemeKernelIdeal
            (FrobeniusStrictTransformSecondChartTensorFrame.stepExceptionalInclusionSucc
              (k := k) (j + 1)) ⊗
          schemeKernelIdeal (oldExceptionalStrictι (k := k) j)) :=
  oldPulledPreviousPunctureIso j ≪≫ (exceptionalOldPunctureIso j).symm

/-- This isomorphism preserves both original ambient ideal maps. -/
theorem oldTotalProductPunctureIso_inclusion (j : ℕ) :
    (oldTotalProductPunctureIso (k := k) j).hom ≫
      (schemeModulePullback (nextPuncture (j + 1)).ι).map (exceptionalOldProduct j) ≫
      (schemeModulePullbackUnitIso (nextPuncture (j + 1)).ι).hom =
    (schemeModulePullback (nextPuncture (j + 1)).ι).map
      (pulledKernelInclusion
        (FrobeniusStrictTransformFirstChartTensorFrame.stepExceptionalInclusionSucc j)
        ((projectiveProductInitial (k := k)).stepProjection (j + 1))) ≫
      (schemeModulePullbackUnitIso (nextPuncture (j + 1)).ι).hom := by
  rw [oldTotalProductPunctureIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← exceptionalOldPunctureIso_inclusion, Iso.inv_hom_id_assoc,
    oldPulledPreviousPunctureIso_inclusion]

end KltDP.Examples.FrobeniusOldExceptionalPuncture
