import KltDP.Geometry.KernelLinePullbackOffRange
import KltDP.Geometry.RationalTreePicardMultidegree
import KltDP.Examples.FrobeniusStrictTransformIsoProjectiveLine
import KltDP.Examples.FrobeniusMultiCentreCurveKernels

/-!
# The curves of `S_{p,n}` on the isomorphism open of the composite blowdown

On the open `U₀ = blowdownIsoOpen q n a = multiProjection ⁻¹ᵁ centersComplement` of `S_{p,n}`, over
which the composite blowdown `multiProjection : S_{p,n} ⟶ P¹ × P¹` is an isomorphism onto the
complement of the centres (`blowdownIso`, `blowdownMap = blowdownIso.hom ≫ centersComplement.ι`):

* the kernel line of the strict graph `B = graphStrictι` restricted to `U₀` is the pullback along
  `blowdownMap` of the kernel line of the graph `graphι (q+1)` (`graphKernelIsoOpenIso`; the
  closure computation `preimage_closure_graph_eq` with the accepted `graphLift_isPullback`,
  `range_graphStrictι`, and `SchemeKernelOpenBaseChange`), so that on `U₀` the class of `B` is
  `(q+1)·a + b` for the **accepted** classes `multiFirstFiberClass`, `multiSecondFiberClass`
  (`isoOpenGraphKernelLine_toPic`, from F28's `inverse_multiGraphTotalIdeal_picard`);
* the kernel line of the strict fibre `F_i` restricted to `U₀` is the pullback along `blowdownMap`
  of the kernel line of the fibre `y = a_i^{q+1}` (`fiberKernelIsoOpenIso`,
  `isoOpenFiberKernelLine_toPic`; the kernel line of any horizontal fibre `y = c` is invertible,
  `horizontalFiberKernel_isInvertible`, by transport of the stage-`0` fibre `y = 0` along the
  translation);
* every exceptional curve misses `U₀`, so its kernel line restricts to the unit and its class to `0`
  (`exceptionalKernelIsoOpenUnitIso`, `isoOpenExceptionalKernelLine_toPic`; lane A2's
  `KernelLinePullbackOffRange`), and the accepted total-transform classes `exceptionalClass`
  restrict to `0` (`exceptionalClass_restrict_isoOpen`).

With `FrobeniusMultiCentreCurveKernels` (the cluster opens) and `cluster_cover`, every class of the
table is thus identified on every member of the cover of `S_{p,n}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
  KltDP.Geometry.SchemeKernelOpenBaseChange KltDP.Geometry.SchematicImageOpenBaseChange
  KltDP.Geometry.SchematicImageToImageIso KltDP.Geometry.KernelLinePullbackOffRange
  KltDP.Geometry.RationalTreePicard
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
  FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts FrobeniusGlobalExceptionalSuccessor
  FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCurveKernels FrobeniusGraphClosed
  FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses FrobeniusProjectivePoints
  FrobeniusUnaffectedFibers FrobeniusAdaptedStrictTransform FrobeniusBlowupChartIteration
  FrobeniusStrictTransformIsoProjectiveLine FrobeniusProjectiveMorphism FrobeniusFiberClosure
  FrobeniusFiberPicard FrobeniusFiberZeroInvertible FrobeniusTowerTransportClasses
  FrobeniusGraphPicardClassZeroFiber ProjectiveProductTranslation
  ProjectiveProductTranslationFibres
open KltDP.Geometry.ProjectiveLineTranslation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The centre of a chart is a maximal ideal (the accepted witness). -/
local instance isoOpenClassesOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The isomorphism open -/

/-- `U₀ ≅` the complement of the centres, through the composite blowdown. -/
def blowdownIso :
    (blowdownIsoOpen q n a).toScheme ≅ (centersComplement (q + 1) n a).toScheme :=
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  asIso (multiProjection (q + 1) n a ∣_ centersComplement (q + 1) n a)

/-- The open immersion `U₀ ⟶ P¹ × P¹`. -/
abbrev blowdownMap : (blowdownIsoOpen q n a).toScheme ⟶ projectiveProduct k :=
  (blowdownIso q n a).hom ≫ (centersComplement (q + 1) n a).ι

theorem blowdownMap_eq :
    blowdownMap q n a = (blowdownIsoOpen q n a).ι ≫ multiProjection (q + 1) n a := by
  letI := multiProjection_restrict_centersComplement_isIso (q + 1) n a
  change (multiProjection (q + 1) n a ∣_ centersComplement (q + 1) n a) ≫ _ = _
  exact morphismRestrict_ι _ _

theorem blowdownMap_base (y : (blowdownIsoOpen q n a).toScheme) :
    (blowdownMap q n a).base y =
      (multiProjection (q + 1) n a).base ((blowdownIsoOpen q n a).ι.base y) := by
  rw [blowdownMap_eq, Scheme.comp_base_apply]

theorem projection_mem_centersComplement (y : (blowdownIsoOpen q n a).toScheme) :
    (multiProjection (q + 1) n a).base ((blowdownIsoOpen q n a).ι.base y) ∈
      centersComplement (q + 1) n a := by
  rw [Scheme.Opens.ι_base_apply]
  exact y.2

/-! ## Kernel lines of the plane curves -/

/-- The kernel line of the graph `graphι p` (the equaliser inclusion) is that of the graph
morphism from `P¹` (accepted `graphι_eq_hom_comp`). -/
def graphιKernelIso (p : ℕ) :
    schemeKernelIdeal (graphι (k := k) p) ≅ schemeKernelIdeal (projectiveGraphMorphism p) :=
  schemeKernelIdealEqIso (graphι_eq_hom_comp p) ≪≫
    schemeKernelPrecompIso (graphIsoProjectiveLine p) (projectiveGraphMorphism p)

theorem graphιKernel_isInvertible (p : ℕ) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
      (schemeKernelIdeal (graphι (k := k) p)) :=
  isInvertible_of_iso (graphIdealLine (k := k) p).property (graphιKernelIso p).symm

/-- The kernel line of the graph `graphι p`. -/
def graphιLine (p : ℕ) : InvertibleSheaf (projectiveProduct k) :=
  ⟨schemeKernelIdeal (graphι (k := k) p), graphιKernel_isInvertible p⟩

theorem graphιLine_toPic (p : ℕ) : (graphιLine (k := k) p).toPic = (graphIdealLine p).toPic :=
  toPic_eq_of_iso _ _ (graphιKernelIso p)

/-- The kernel line of the stage-`0` strict fibre `y = 0` is that of the fibre morphism
(accepted `fiberStrictIdeal_zero`). -/
def horizontalFiberZeroKernelIso :
    schemeKernelIdeal (horizontalFiberMorphism (0 : k)) ≅
      schemeKernelIdeal (fiberClosureInclusion (projectiveProductInitial (k := k)) 0) :=
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsReduced (liftedFiberClosure (projectiveProductInitial (k := k)) 0) :=
    liftedFiberClosure_isReduced _ 0
  (schemeKernelIdealEqIso (isoOfKerEq_hom (horizontalFiberMorphism (0 : k))
    (fiberClosureInclusion (projectiveProductInitial (k := k)) 0)
    ((fiberStrictIdeal_zero (k := k)).symm.trans
      (liftedFiberClosureIdeal (projectiveProductInitial (k := k)) 0).ker_gluedTo.symm))).symm ≪≫
    schemeKernelPrecompIso _ _

theorem horizontalFiberZeroKernel_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
      (schemeKernelIdeal (horizontalFiberMorphism (0 : k))) :=
  isInvertible_of_iso (fiberKernel_zero_isInvertible (k := k)) horizontalFiberZeroKernelIso.symm

theorem horizontalFiber_translation_zero (c : k) :
    (projectiveTranslationIso (0 : k)).hom ≫ horizontalFiberMorphism (0 + c) =
      horizontalFiberMorphism 0 ≫ (productTranslationIso 0 c).hom := by
  change projectiveTranslation (0 : k) ≫ horizontalFiberMorphism (0 + c) =
    horizontalFiberMorphism 0 ≫ productTranslation 0 c
  rw [horizontalFiberMorphism_productTranslation]

/-- **The kernel line of every horizontal fibre `y = c` is invertible** (transport of `y = 0` along
the translation `τ_0 × τ_c`). -/
theorem horizontalFiberKernel_isInvertible (c : k) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
      (schemeKernelIdeal (horizontalFiberMorphism c)) := by
  have h := isInvertible_schemeKernelIdeal_transport (horizontalFiberMorphism (0 : k))
    (productTranslationIso 0 c) (horizontalFiberMorphism (0 + c)) (projectiveTranslationIso 0)
    (horizontalFiber_translation_zero c) horizontalFiberZeroKernel_isInvertible
  rwa [zero_add] at h

/-- The kernel line of the horizontal fibre `y = c`. -/
def horizontalFiberLine (c : k) : InvertibleSheaf (projectiveProduct k) :=
  ⟨schemeKernelIdeal (horizontalFiberMorphism c), horizontalFiberKernel_isInvertible c⟩

/-! ## The strict fibre on `U₀` -/

/-- Points of the closure of the lifted punctured fibre project into the fibre. -/
theorem projection_mem_of_mem_closure_fiberLift (i : Fin n) (x : multiSurface (q + 1) n a)
    (hx : x ∈ closure (Set.range (fiberLift (q + 1) n a i).base)) :
    (multiProjection (q + 1) n a).base x ∈
      Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base := by
  have hsub : (multiProjection (q + 1) n a).base ''
      closure (Set.range (fiberLift (q + 1) n a i).base) ⊆
      closure ((multiProjection (q + 1) n a).base '' Set.range (fiberLift (q + 1) n a i).base) :=
    image_closure_subset_closure_image (multiProjection (q + 1) n a).continuous
  have him : (multiProjection (q + 1) n a).base '' Set.range (fiberLift (q + 1) n a i).base ⊆
      Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(fiberPuncture (q + 1) n a i).ι.base z, ?_⟩
    change (puncturedFiber (q + 1) n a i).base z =
      (fiberLift (q + 1) n a i ≫ multiProjection (q + 1) n a).base z
    rw [fiberLift_projection]
  exact closure_minimal him
    (horizontalFiberMorphism (a i ^ (q + 1))).isClosedEmbedding.isClosed_range (hsub ⟨x, hx, rfl⟩)

theorem range_fiberLift_eq (i : Fin n) :
    Set.range (fiberLift (q + 1) n a i).base =
      (multiProjection (q + 1) n a).base ⁻¹' Set.range (puncturedFiber (q + 1) n a i).base := by
  rw [← Scheme.Pullback.range_fst (multiProjection (q + 1) n a) (puncturedFiber (q + 1) n a i)]
  have h := IsPullback.isoPullback_hom_fst (fiberLift_isPullback (q + 1) n a i)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(IsPullback.isoPullback (fiberLift_isPullback (q + 1) n a i)).hom.base z,
      by rw [← Scheme.comp_base_apply, h]⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(IsPullback.isoPullback (fiberLift_isPullback (q + 1) n a i)).inv.base w, ?_⟩
    rw [← Scheme.comp_base_apply, (Iso.inv_comp_eq _).mpr h.symm]

theorem preimage_closure_fiber_eq (i : Fin n) :
    (blowdownIsoOpen q n a).ι.base ⁻¹' closure (Set.range (fiberStrictι (q + 1) n a i).base) =
      (blowdownMap q n a).base ⁻¹'
        closure (Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base) := by
  rw [range_fiberStrictι, closure_closure,
    (horizontalFiberMorphism (a i ^ (q + 1))).isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  constructor
  · intro hy
    show (blowdownMap q n a).base y ∈ Set.range (horizontalFiberMorphism (a i ^ (q + 1))).base
    rw [blowdownMap_base]
    exact projection_mem_of_mem_closure_fiberLift q n a i _ hy
  · rintro ⟨z, hz⟩
    show (blowdownIsoOpen q n a).ι.base y ∈ closure (Set.range (fiberLift (q + 1) n a i).base)
    apply subset_closure
    rw [range_fiberLift_eq]
    rw [blowdownMap_base] at hz
    have hmem : (horizontalFiberMorphism (a i ^ (q + 1))).base z ∈
        centersComplement (q + 1) n a := by
      rw [hz]
      exact projection_mem_centersComplement q n a y
    exact ⟨⟨z, hmem⟩, hz⟩

section FiberInstances

variable (i : Fin n)

local instance fiberStrict_isReduced_isoOpen : IsReduced (fiberStrict (q + 1) n a i) := by
  letI := fiberPuncture_noetherianSpace (q + 1) n a i
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  letI : IsReduced (fiberPuncture (q + 1) n a i).toScheme :=
    isReduced_of_isOpenImmersion (fiberPuncture (q + 1) n a i).ι
  exact SchematicImageDenseOpen.image_glued_isReduced (fiberLift (q + 1) n a i)

local instance projectiveSpace_isIntegral' : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance fiberRestrict_isoOpen_fst_isClosedImmersion :
    IsClosedImmersion (pullback.fst (blowdownIsoOpen q n a).ι (fiberStrictι (q + 1) n a i)) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

local instance horizontalFiberRestrict_fst_isClosedImmersion :
    IsClosedImmersion
      (pullback.fst (blowdownMap q n a) (horizontalFiberMorphism (a i ^ (q + 1)))) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

/-- **Over `U₀`, `F_i` and the fibre `y = a_i^{q+1}` have the same kernel.** -/
theorem fiberStrictι_ker_isoOpen₀ :
    (openBaseChange (fiberStrictι (q + 1) n a i) (blowdownIsoOpen q n a).ι).ker =
      (openBaseChange (horizontalFiberMorphism (a i ^ (q + 1))) (blowdownMap q n a)).ker :=
  ker_openBaseChange_eq _ _ _ _ (preimage_closure_fiber_eq q n a i)

/-- **The kernel line of `F_i` restricted to `U₀` is the pullback of the kernel line of the fibre
`y = a_i^{q+1}`.** -/
def fiberKernelIsoOpenIso :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (schemeKernelIdeal (fiberStrictι (q + 1) n a i)) ≅
      (schemeModulePullback (blowdownMap q n a)).obj
        (schemeKernelIdeal (horizontalFiberMorphism (a i ^ (q + 1)))) :=
  (kernelRestrictBaseChangeIso (fiberStrictι (q + 1) n a i) (blowdownIsoOpen q n a)).symm ≪≫
    (schemeKernelIdealEqIso (isoOfKerEq_hom _ _ (fiberStrictι_ker_isoOpen₀ q n a i))).symm ≪≫
    schemeKernelPrecompIso (isoOfKerEq _ _ (fiberStrictι_ker_isoOpen₀ q n a i)) _ ≪≫
    kernelOpenBaseChangeIso _ (blowdownIso q n a) (blowdownMap q n a) rfl

theorem fiberKernelIsoOpen_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (blowdownIsoOpen q n a).toScheme.ringCatSheaf)
      ((schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (schemeKernelIdeal (fiberStrictι (q + 1) n a i))) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible (blowdownMap q n a) _
    (horizontalFiberKernel_isInvertible (a i ^ (q + 1)))) (fiberKernelIsoOpenIso q n a i).symm

/-- The kernel line of `F_i` restricted to `U₀`. -/
def isoOpenFiberKernelLine : InvertibleSheaf (blowdownIsoOpen q n a).toScheme :=
  ⟨_, fiberKernelIsoOpen_isInvertible q n a i⟩

/-- **On `U₀` the class of `F_i` is the pullback of the class of the fibre `y = a_i^{q+1}`.** -/
theorem isoOpenFiberKernelLine_toPic :
    -Additive.ofMul (isoOpenFiberKernelLine q n a i).toPic =
      (schemePicardPullbackHom (blowdownMap q n a)).toAdditive
        (-Additive.ofMul (horizontalFiberLine (a i ^ (q + 1))).toPic) := by
  rw [map_neg, toPic_eq_pullback_of_iso (blowdownMap q n a) (horizontalFiberLine (a i ^ (q + 1)))
    (isoOpenFiberKernelLine q n a i) (fiberKernelIsoOpenIso q n a i)]
  rfl

end FiberInstances

/-! ## The strict graph on `U₀` -/

theorem projection_mem_of_mem_closure_graphLift (x : multiSurface (q + 1) n a)
    (hx : x ∈ closure (Set.range (graphLift (q + 1) n a).base)) :
    (multiProjection (q + 1) n a).base x ∈ Set.range (graphι (k := k) (q + 1)).base := by
  have hsub : (multiProjection (q + 1) n a).base ''
      closure (Set.range (graphLift (q + 1) n a).base) ⊆
      closure ((multiProjection (q + 1) n a).base '' Set.range (graphLift (q + 1) n a).base) :=
    image_closure_subset_closure_image (multiProjection (q + 1) n a).continuous
  have him : (multiProjection (q + 1) n a).base '' Set.range (graphLift (q + 1) n a).base ⊆
      Set.range (graphι (k := k) (q + 1)).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(graphPuncture (q + 1) n a).ι.base z, ?_⟩
    change (puncturedGraph (q + 1) n a).base z =
      (graphLift (q + 1) n a ≫ multiProjection (q + 1) n a).base z
    rw [graphLift_projection]
  exact closure_minimal him (graphι (k := k) (q + 1)).isClosedEmbedding.isClosed_range
    (hsub ⟨x, hx, rfl⟩)

theorem range_graphLift_eq :
    Set.range (graphLift (q + 1) n a).base =
      (multiProjection (q + 1) n a).base ⁻¹' Set.range (puncturedGraph (q + 1) n a).base := by
  rw [← Scheme.Pullback.range_fst (multiProjection (q + 1) n a) (puncturedGraph (q + 1) n a)]
  have h := IsPullback.isoPullback_hom_fst (graphLift_isPullback (q + 1) n a)
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(IsPullback.isoPullback (graphLift_isPullback (q + 1) n a)).hom.base z,
      by rw [← Scheme.comp_base_apply, h]⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(IsPullback.isoPullback (graphLift_isPullback (q + 1) n a)).inv.base w, ?_⟩
    rw [← Scheme.comp_base_apply, (Iso.inv_comp_eq _).mpr h.symm]

theorem preimage_closure_graph_eq :
    (blowdownIsoOpen q n a).ι.base ⁻¹' closure (Set.range (graphStrictι (q + 1) n a).base) =
      (blowdownMap q n a).base ⁻¹' closure (Set.range (graphι (k := k) (q + 1)).base) := by
  rw [range_graphStrictι, closure_closure,
    (graphι (k := k) (q + 1)).isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  constructor
  · intro hy
    show (blowdownMap q n a).base y ∈ Set.range (graphι (k := k) (q + 1)).base
    rw [blowdownMap_base]
    exact projection_mem_of_mem_closure_graphLift q n a _ hy
  · rintro ⟨z, hz⟩
    show (blowdownIsoOpen q n a).ι.base y ∈ closure (Set.range (graphLift (q + 1) n a).base)
    apply subset_closure
    rw [range_graphLift_eq]
    rw [blowdownMap_base] at hz
    have hmem : (graphι (k := k) (q + 1)).base z ∈ centersComplement (q + 1) n a := by
      rw [hz]
      exact projection_mem_centersComplement q n a y
    exact ⟨⟨z, hmem⟩, hz⟩

section Graph

local instance graph_isIntegral' : IsIntegral (graph (k := k) (q + 1)) :=
  graph_isIntegral (q + 1)

local instance graphStrict_isReduced_isoOpen : IsReduced (graphStrict (q + 1) n a) := by
  letI := graphPuncture_noetherianSpace (q + 1) n a
  letI : IsReduced (graphPuncture (q + 1) n a).toScheme :=
    isReduced_of_isOpenImmersion (graphPuncture (q + 1) n a).ι
  exact SchematicImageDenseOpen.image_glued_isReduced (graphLift (q + 1) n a)

local instance graphRestrict_isoOpen_fst_isClosedImmersion :
    IsClosedImmersion (pullback.fst (blowdownIsoOpen q n a).ι (graphStrictι (q + 1) n a)) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

local instance graphιRestrict_fst_isClosedImmersion :
    IsClosedImmersion (pullback.fst (blowdownMap q n a) (graphι (k := k) (q + 1))) :=
  MorphismProperty.pullback_fst (P := @IsClosedImmersion) _ _ inferInstance

/-- **Over `U₀`, `B` and the graph have the same kernel.** -/
theorem graphStrictι_ker_isoOpen₀ :
    (openBaseChange (graphStrictι (q + 1) n a) (blowdownIsoOpen q n a).ι).ker =
      (openBaseChange (graphι (k := k) (q + 1)) (blowdownMap q n a)).ker :=
  ker_openBaseChange_eq _ _ _ _ (preimage_closure_graph_eq q n a)

/-- **The kernel line of `B` restricted to `U₀` is the pullback of the kernel line of the graph.** -/
def graphKernelIsoOpenIso :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (schemeKernelIdeal (graphStrictι (q + 1) n a)) ≅
      (schemeModulePullback (blowdownMap q n a)).obj
        (schemeKernelIdeal (graphι (k := k) (q + 1))) :=
  (kernelRestrictBaseChangeIso (graphStrictι (q + 1) n a) (blowdownIsoOpen q n a)).symm ≪≫
    (schemeKernelIdealEqIso (isoOfKerEq_hom _ _ (graphStrictι_ker_isoOpen₀ q n a))).symm ≪≫
    schemeKernelPrecompIso (isoOfKerEq _ _ (graphStrictι_ker_isoOpen₀ q n a)) _ ≪≫
    kernelOpenBaseChangeIso _ (blowdownIso q n a) (blowdownMap q n a) rfl

theorem graphKernelIsoOpen_isInvertible :
    KltDP.SheafOfModules.IsInvertible (R := (blowdownIsoOpen q n a).toScheme.ringCatSheaf)
      ((schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (schemeKernelIdeal (graphStrictι (q + 1) n a))) :=
  isInvertible_of_iso (schemeModulePullback_isInvertible (blowdownMap q n a) _
    (graphιKernel_isInvertible (q + 1))) (graphKernelIsoOpenIso q n a).symm

/-- The kernel line of `B` restricted to `U₀`. -/
def isoOpenGraphKernelLine : InvertibleSheaf (blowdownIsoOpen q n a).toScheme :=
  ⟨_, graphKernelIsoOpen_isInvertible q n a⟩

/-- **On `U₀` the class of `B` is `(q+1)·a + b` for the accepted fibre classes of `S_{p,n}`.** -/
theorem isoOpenGraphKernelLine_toPic :
    -Additive.ofMul (isoOpenGraphKernelLine q n a).toPic =
      (schemePicardPullbackHom (blowdownIsoOpen q n a).ι).toAdditive
        ((q + 1) • multiFirstFiberClass (q + 1) n a + multiSecondFiberClass (q + 1) n a) := by
  rw [← inverse_multiGraphTotalIdeal_picard, map_neg]
  unfold multiGraphTotalIdealLine
  rw [toPic_eq_pullback_of_iso (blowdownMap q n a) (graphιLine (q + 1))
    (isoOpenGraphKernelLine q n a) (graphKernelIsoOpenIso q n a), graphιLine_toPic,
    blowdownMap_eq]
  change -Additive.ofMul (schemePicardPullbackHom
      ((blowdownIsoOpen q n a).ι ≫ multiProjection (q + 1) n a) (graphIdealLine (q + 1)).toPic) =
    -Additive.ofMul (schemePicardPullbackHom (blowdownIsoOpen q n a).ι
      (pullbackInvertibleSheaf (multiProjection (q + 1) n a) (graphIdealLine (q + 1))).toPic)
  rw [← schemePicardPullbackHom_toPic, ← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp]

end Graph

/-! ## The exceptional curves on `U₀` -/

theorem disjoint_isoOpen_exceptional (i : Fin n) (idx : FinalIndex.{0} q) :
    Disjoint (Set.range (blowdownIsoOpen q n a).ι.base)
      (Set.range (exceptionalCurveι q n a i idx).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ hx
  have h1 := exceptionalSupport_projection q n a i idx _ hx
  have h2 := projection_mem_centersComplement q n a y
  rw [h1] at h2
  exact not_mem_earlierComplement (q + 1) n a i h2

/-- **The kernel line of every exceptional curve restricted to `U₀` is the unit.** -/
def exceptionalKernelIsoOpenUnitIso (i : Fin n) (idx : FinalIndex.{0} q) :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (schemeKernelIdeal (exceptionalCurveι q n a i idx)) ≅
      _root_.SheafOfModules.unit (blowdownIsoOpen q n a).toScheme.ringCatSheaf :=
  kernelLine_pullback_unitIso (exceptionalCurveι q n a i idx) (blowdownIsoOpen q n a).ι
    (disjoint_isoOpen_exceptional q n a i idx)

theorem exceptionalKernelIsoOpen_isInvertible (i : Fin n) (idx : FinalIndex.{0} q) :
    KltDP.SheafOfModules.IsInvertible (R := (blowdownIsoOpen q n a).toScheme.ringCatSheaf)
      ((schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        (schemeKernelIdeal (exceptionalCurveι q n a i idx))) :=
  isInvertible_of_iso (InvertibleSheaf.trivial (blowdownIsoOpen q n a).toScheme).property
    (exceptionalKernelIsoOpenUnitIso q n a i idx).symm

/-- The kernel line of `E_{i,idx}` restricted to `U₀`. -/
def isoOpenExceptionalKernelLine (i : Fin n) (idx : FinalIndex.{0} q) :
    InvertibleSheaf (blowdownIsoOpen q n a).toScheme :=
  ⟨_, exceptionalKernelIsoOpen_isInvertible q n a i idx⟩

/-- **On `U₀` the class of every exceptional curve is `0`.** -/
theorem isoOpenExceptionalKernelLine_toPic (i : Fin n) (idx : FinalIndex.{0} q) :
    -Additive.ofMul (isoOpenExceptionalKernelLine q n a i idx).toPic = 0 := by
  rw [(toPic_eq_one_iff_iso_unit _).mpr ⟨exceptionalKernelIsoOpenUnitIso q n a i idx⟩, ofMul_one,
    neg_zero]

/-- The composite `U₀ ⟶ T_i ⟶ stage j + 1` misses the exceptional curve `E_j` of the tower. -/
theorem disjoint_isoOpen_previousFiber (i : Fin n) (j : Fin (q + 1)) :
    Disjoint (Set.range (((blowdownIsoOpen q n a).ι ≫ towerProjection (q + 1) n a i) ≫
        between (translatedInitial (q + 1) (a i)) j.isLt).base)
      (Set.range (previousFiberι ((translatedInitial (q + 1) (a i)).stage j.val)).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ ⟨z, hz⟩
  have h1 := previousFiber_projection_center (translatedInitial (q + 1) (a i)) j.val z
  rw [hz, selected_center] at h1
  have h2 : ((translatedInitial (q + 1) (a i)).toInitial (j.val + 1)).base
      ((((blowdownIsoOpen q n a).ι ≫ towerProjection (q + 1) n a i) ≫
        between (translatedInitial (q + 1) (a i)) j.isLt).base y) =
      (multiProjection (q + 1) n a).base ((blowdownIsoOpen q n a).ι.base y) := by
    rw [← Scheme.comp_base_apply, ← between_zero, Category.assoc, between_comp, between_zero,
      ← towerProjection_projection (q + 1) n a i, Scheme.comp_base_apply, Scheme.comp_base_apply,
      Scheme.comp_base_apply]
    rfl
  rw [h1] at h2
  have h3 := projection_mem_centersComplement q n a y
  rw [← h2] at h3
  exact not_mem_earlierComplement (q + 1) n a i h3

/-- **The accepted total-transform classes `E_{ij}` of `S_{p,n}` restrict to `0` on `U₀`.** -/
theorem exceptionalClass_restrict_isoOpen (i : Fin n) (j : Fin (q + 1)) :
    (schemePicardPullbackHom (blowdownIsoOpen q n a).ι).toAdditive
      (exceptionalClass (q + 1) n a i j) = 0 := by
  unfold exceptionalClass towerExceptionalLine
  rw [map_neg, ← schemePicardPullbackHom_toPic, ← schemePicardPullbackHom_toPic]
  change -Additive.ofMul (schemePicardPullbackHom (blowdownIsoOpen q n a).ι
      (schemePicardPullbackHom (towerProjection (q + 1) n a i)
        (schemePicardPullbackHom (between (translatedInitial (q + 1) (a i)) j.isLt)
          (translatedStepExceptionalIdealLine (q + 1) (a i) j).toPic))) = 0
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← schemePicardPullbackHom_comp,
    ← schemePicardPullbackHom_comp, schemePicardPullbackHom_toPic,
    (toPic_eq_one_iff_iso_unit _).mpr ⟨kernelLine_pullback_unitIso _ _
      (disjoint_isoOpen_previousFiber q n a i j)⟩, ofMul_one, neg_zero]

end KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses
