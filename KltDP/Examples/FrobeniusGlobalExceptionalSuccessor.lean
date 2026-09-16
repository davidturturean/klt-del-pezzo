import KltDP.Examples.FrobeniusExceptionalSuccessorChart
import KltDP.Examples.FrobeniusStrictTransformContact
import KltDP.Examples.FrobeniusExceptionalProjectiveLine
import KltDP.Geometry.PointBlowupCenterFiber

/-!
# The preceding exceptional curve in the whole next blowup

The original preceding exceptional curve is the actual categorical center
fiber of a whole point blowup. Its first quotient chart is an open affine
line. Remove its next center, lift the entire resulting open through the
actual unchanged-complement inclusion, and form its kernel subscheme.
The actual second Rees-chart axis has the same kernel by dense-open
invariance, and is an open chart of this whole strict transform.

The whole strict transform avoids the next contact chart. The original
new exceptional equation cuts length one at its actual parameter-zero
point. Thus this leaf treats an adjacent exceptional pair in entire
successive schemes; it does not posit a complete chain or a global
intersection-number formula.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalExceptionalSuccessor

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusExceptionalCharts FrobeniusBlowupSmooth
open FrobeniusExceptionalProjectiveLine FrobeniusExceptionalSuccessorChart
open FrobeniusStrictTransformClosure FrobeniusBlowupIncidence

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

/-- The actual chosen origin has its already proved maximal center ideal. -/
local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The actual exceptional fiber of the first whole blowup. -/
abbrev previousFiber : Scheme.{u} :=
  PointBlowupGluing.globalCenterFiber A.chart (originPoint (k := k)) A.center_closed

/-- Its original closed inclusion into the actual current whole scheme. -/
abbrev previousFiberι : previousFiber A ⟶ A.next.carrier :=
  PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k)) A.center_closed

/-- The existing original quotient and fiber comparisons give its actual P1 model. -/
def previousFiberIso : previousFiber A ≅ projectiveSpace k 1 :=
  (PointBlowupGluing.affineCenterFiberIso A.chart (originPoint (k := k))
    A.center_closed).symm ≪≫ exceptionalFiberProjectiveLineIso

instance previousFiber_nonempty : Nonempty (previousFiber A) :=
  ⟨(previousFiberIso A).inv.base (projectiveSpaceZeroPrime k 1)⟩

instance previousFiber_isIntegral : IsIntegral (previousFiber A) := by
  letI : IsIntegral (projectiveSpace k 1) := projectiveSpace_isIntegral k 1
  exact isIntegral_of_isOpenImmersion (previousFiberIso A).hom

/-- The original first exceptional quotient chart, with its affine-line parameter. -/
def previousFiberChart : Spec (CommRingCat.of (Polynomial k)) ⟶ previousFiber A :=
  (uExceptionalIso (k := k)).inv ≫ exceptionalChartToFiber centerIdeal centerU ≫
    (PointBlowupGluing.affineCenterFiberIso A.chart (originPoint (k := k))
      A.center_closed).hom

instance previousFiberChart_isOpenImmersion : IsOpenImmersion (previousFiberChart A) := by
  unfold previousFiberChart
  infer_instance

/-- This chart is the actual equation u=0 in the next selected plane. -/
@[reassoc] theorem previousFiberChart_ι :
    previousFiberChart A ≫ previousFiberι A =
      Spec.map (CommRingCat.ofHom (exceptionalPlaneEvaluation (k := k))) ≫ A.next.chart := by
  rw [previousFiberChart, Category.assoc, Category.assoc,
    PointBlowupGluing.affineCenterFiberIso_hom_ι,
    ← Category.assoc (exceptionalChartToFiber centerIdeal centerU)]
  change (uExceptionalIso (k := k)).inv ≫
    (exceptionalChartToFiber (centerIdeal (k := k)) centerU ≫
      centerFiberι (centerIdeal (k := k))) ≫ A.nextAffineBlowup = _
  rw [exceptionalChartToFiber_ι]
  change (uExceptionalIso (k := k)).inv ≫
    ((exceptionalChartInclusion centerIdeal centerU ≫ chartι centerIdeal centerU) ≫
      A.nextAffineBlowup) = _
  simp only [Category.assoc]
  rw [← Category.assoc (uExceptionalIso (k := k)).inv
    (exceptionalChartInclusion centerIdeal centerU), uExceptionalIso_inv_inclusion]
  simp only [Category.assoc, PlaneChartedScheme.next, PlaneChartedScheme.nextChart,
    coordinateChart]

/-- The original second-chart axis in the whole successor blowup. -/
def successorCurve : Spec (CommRingCat.of (Polynomial k)) ⟶ A.next.next.carrier :=
  oldCurveMorphism ≫ A.next.nextAffineBlowup

/-- Its projection is the actual first chart of the preceding exceptional fiber. -/
@[reassoc] theorem successorCurve_projection :
    successorCurve A ≫ A.next.nextProjection = previousFiberChart A ≫ previousFiberι A := by
  rw [successorCurve, Category.assoc, PlaneChartedScheme.nextAffineBlowup_projection,
    ← Category.assoc, oldCurveMorphism_toSpec, previousFiberChart_ι]

/-- The open of the entire preceding fiber with the actual next center removed. -/
def previousPuncture : (previousFiber A).Opens :=
  previousFiberι A ⁻¹ᵁ
    PointBlowupGluing.puncture A.next.chart (originPoint (k := k)) A.next.center_closed

private theorem exceptionalPlane_ne_origin (q : parameterPuncture (k := k)) :
    (Spec.map (CommRingCat.ofHom (exceptionalPlaneEvaluation (k := k)))).base q.1 ≠
      originPoint := by
  intro h
  have hv : vCoord (k := k) ∈
      ((Spec.map (CommRingCat.ofHom (exceptionalPlaneEvaluation (k := k)))).base q.1).asIdeal := by
    rw [h]
    exact centerV.property
  change exceptionalPlaneEvaluation (vCoord (k := k)) ∈ q.1.asIdeal at hv
  rw [exceptionalPlaneEvaluation_v] at hv
  exact q.2 hv

/-- The punctured parameter chart lies in the actual whole punctured fiber. -/
theorem parameter_range_previousPuncture :
    Set.range (parameterPuncture.ι ≫ previousFiberChart A).base ⊆
      Set.range (previousPuncture A).ι.base := by
  rintro _ ⟨q, rfl⟩
  refine ⟨⟨(parameterPuncture.ι ≫ previousFiberChart A).base q, ?_⟩, rfl⟩
  change (parameterPuncture.ι ≫ previousFiberChart A ≫ previousFiberι A).base q ≠
    A.next.chart.base (originPoint (k := k))
  rw [previousFiberChart_ι]
  intro h
  apply exceptionalPlane_ne_origin q
  exact A.next.chart.isOpenEmbedding.injective h

/-- The original punctured affine exceptional chart factors by an actual open immersion. -/
def parameterToPreviousPuncture : (parameterPuncture (k := k)).toScheme ⟶
    (previousPuncture A).toScheme :=
  IsOpenImmersion.lift (previousPuncture A).ι
    (parameterPuncture.ι ≫ previousFiberChart A) (parameter_range_previousPuncture A)

@[reassoc] theorem parameterToPreviousPuncture_ι :
    parameterToPreviousPuncture A ≫ (previousPuncture A).ι =
      parameterPuncture.ι ≫ previousFiberChart A := IsOpenImmersion.lift_fac _ _ _

instance parameterToPreviousPuncture_isOpenImmersion :
    IsOpenImmersion (parameterToPreviousPuncture A) := by
  letI : IsOpenImmersion (parameterToPreviousPuncture A ≫ (previousPuncture A).ι) := by
    rw [parameterToPreviousPuncture_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (previousPuncture A).ι

instance previousPuncture_nonempty : Nonempty (previousPuncture A) :=
  ⟨(parameterToPreviousPuncture A).base (Classical.choice inferInstance)⟩

instance previousPuncture_isIntegral : IsIntegral (previousPuncture A).toScheme :=
  isIntegral_of_isOpenImmersion (previousPuncture A).ι

/-- Lift the entire previous exceptional curve off the next center through
the original unchanged-complement inclusion of the actual whole blowup. -/
def wholePreviousLift : (previousPuncture A).toScheme ⟶ A.next.next.carrier :=
  (previousFiberι A ∣_ PointBlowupGluing.puncture A.next.chart
    (originPoint (k := k)) A.next.center_closed) ≫
      PointBlowupGluing.complementι A.next.chart (originPoint (k := k)) A.next.center_closed

@[reassoc] theorem wholePreviousLift_projection :
    wholePreviousLift A ≫ A.next.nextProjection = (previousPuncture A).ι ≫ previousFiberι A := by
  rw [wholePreviousLift, Category.assoc, PlaneChartedScheme.nextProjection,
    PointBlowupGluing.complementι_projection, morphismRestrict_ι]
  rfl

/-- On the punctured affine chart the whole-fiber lift is exactly the
constructed second Rees-chart curve; the complement's original inclusion
and projection determine this equality. -/
theorem parameterToPreviousPuncture_wholeLift :
    parameterToPreviousPuncture A ≫ wholePreviousLift A =
      parameterPuncture.ι ≫ successorCurve A := by
  let U := PointBlowupGluing.puncture A.next.chart (originPoint (k := k)) A.next.center_closed
  let j := PointBlowupGluing.complementι A.next.chart (originPoint (k := k)) A.next.center_closed
  let f := parameterPuncture.ι ≫ successorCurve A
  have hr : Set.range f.base ⊆ Set.range j.base := by
    rw [PointBlowupGluing.range_complementι]
    rintro _ ⟨q, rfl⟩
    change (f ≫ A.next.nextProjection).base q ≠ A.next.chart.base originPoint
    dsimp only [f]
    rw [Category.assoc, successorCurve_projection, previousFiberChart_ι]
    exact fun h => exceptionalPlane_ne_origin q (A.next.chart.isOpenEmbedding.injective h)
  let l := IsOpenImmersion.lift j f hr
  have hl : l ≫ U.ι = f ≫ A.next.nextProjection := by
    rw [← PointBlowupGluing.complementι_projection A.next.chart
      (originPoint (k := k)) A.next.center_closed, ← Category.assoc]
    change (IsOpenImmersion.lift j f hr ≫ j) ≫ A.next.nextProjection = _
    rw [IsOpenImmersion.lift_fac]
  have he : parameterToPreviousPuncture A ≫ (previousFiberι A ∣_ U) = l := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    change (parameterToPreviousPuncture A ≫ (previousPuncture A).ι) ≫
      previousFiberι A = l ≫ U.ι
    rw [parameterToPreviousPuncture_ι, Category.assoc, ← successorCurve_projection]
    simpa only [f, Category.assoc] using hl.symm
  change parameterToPreviousPuncture A ≫ ((previousFiberι A ∣_ U) ≫ j) = f
  rw [← Category.assoc, he]
  exact IsOpenImmersion.lift_fac j f hr

/-- The original whole exceptional strict-transform ideal. -/
def previousStrictIdeal : A.next.next.carrier.IdealSheafData := (wholePreviousLift A).ker

/-- The actual whole-fiber definition equals the kernel of the second
Rees-chart curve, by the two original nonempty-open comparisons. -/
theorem previousStrictIdeal_eq : previousStrictIdeal A = (successorCurve A).ker := by
  rw [previousStrictIdeal,
    ← SchematicImageOpenImmersion.ker_precompose_openImmersion
      (parameterToPreviousPuncture A) (wholePreviousLift A),
    parameterToPreviousPuncture_wholeLift]
  exact SchematicImageDenseOpen.ker_precompose_open parameterPuncture (successorCurve A)

/-- The actual kernel-glued image of the lifted whole previous fiber. -/
abbrev previousStrictTransform : Scheme.{u} := (previousStrictIdeal A).glueData.glued

abbrev previousStrictι : previousStrictTransform A ⟶ A.next.next.carrier :=
  (previousStrictIdeal A).gluedTo

instance previousStrictι_isClosedImmersion : IsClosedImmersion (previousStrictι A) :=
  (previousStrictIdeal A).gluedTo_isClosedImmersion

instance previousStrictTransform_isReduced : IsReduced (previousStrictTransform A) := by
  change IsReduced (previousStrictIdeal A).glueData.glued
  rw [previousStrictIdeal_eq]
  exact SchematicImageDenseOpen.image_glued_isReduced (successorCurve A)

theorem range_previousStrictι :
    Set.range (previousStrictι A).base = closure (Set.range (successorCurve A).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo, previousStrictIdeal_eq]
  exact Scheme.Hom.support_ker (successorCurve A)

/-- The entire actual strict transform avoids the next selected contact
chart. Taking closure preserves this fact because that chart is open. -/
theorem previousStrict_avoids_nextChart (z : previousStrictTransform A) :
    (previousStrictι A).base z ∉ Set.range A.next.nextChart.base := by
  have h : Set.range (successorCurve A).base ⊆ (Set.range A.next.nextChart.base)ᶜ := by
    rintro _ ⟨q, rfl⟩ ⟨p, hp⟩
    apply oldCurve_avoids_uChart q
    refine ⟨(coordinateChartIso (k := k)).hom.base p, ?_⟩
    exact A.next.nextAffineBlowup.isOpenEmbedding.injective hp
  have hc := closure_minimal h A.next.nextChart.isOpenEmbedding.isOpen_range.isClosed_compl
  apply hc
  rw [← range_previousStrictι]
  exact ⟨z, rfl⟩

/-- In particular, the actual next rational center is not on this whole
preceding exceptional strict transform. -/
theorem nextCenter_not_on_previousStrict :
    A.next.nextChart.base (originPoint (k := k)) ∉ Set.range (previousStrictι A).base := by
  rintro ⟨z, hz⟩
  exact previousStrict_avoids_nextChart A z ⟨originPoint, hz.symm⟩

/-- The proved whole/local kernel equality identifies the original
strict transform with the actual schematic image of the chart curve. -/
def previousStrictIsoImage :
    previousStrictTransform A ≅ SchematicImageGlued.image (successorCurve A) :=
  eqToIso (congrArg (fun I : A.next.next.carrier.IdealSheafData => I.glueData.glued)
    (previousStrictIdeal_eq A))

private theorem gluedTo_eqToHom {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

@[reassoc] theorem previousStrictIsoImage_hom_ι :
    (previousStrictIsoImage A).hom ≫ SchematicImageGlued.inclusion (successorCurve A) =
      previousStrictι A := gluedTo_eqToHom _ _ (previousStrictIdeal_eq A)

/-- The original second-chart curve factors into the original whole strict transform. -/
def successorCurveToStrict : Spec (CommRingCat.of (Polynomial k)) ⟶ previousStrictTransform A :=
  SchematicImageGlued.toImage (successorCurve A) ≫ (previousStrictIsoImage A).inv

@[reassoc] theorem successorCurveToStrict_ι :
    successorCurveToStrict A ≫ previousStrictι A = successorCurve A := by
  rw [successorCurveToStrict, Category.assoc, ← previousStrictIsoImage_hom_ι A,
    Iso.inv_hom_id_assoc, SchematicImageGlued.toImage_inclusion]

/-- The second-chart axis is an actual open chart of the whole exceptional strict transform. -/
instance successorCurveToStrict_isOpenImmersion : IsOpenImmersion (successorCurveToStrict A) := by
  apply ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image
    oldCurveChartMorphism (chartι centerIdeal centerV ≫ A.next.nextAffineBlowup)
    (previousStrictι A) (successorCurveToStrict A)
  · simpa only [successorCurve, oldCurveMorphism, Category.assoc] using successorCurveToStrict_ι A
  · simpa only [successorCurve, oldCurveMorphism, Category.assoc] using range_previousStrictι A

/-- The actual adjacent-exceptional intersection point on the whole strict transform. -/
def adjacentPoint : previousStrictTransform A := (successorCurveToStrict A).base curvePoint

private theorem exceptionalPlaneEvaluation_origin :
    (Polynomial.evalRingHom (0 : k)).comp exceptionalPlaneEvaluation =
      FrobeniusBlowupChartIteration.originEvaluation := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro r
      change Polynomial.eval 0 (exceptionalPlaneEvaluation (planeConstants r)) =
        FrobeniusBlowupChartIteration.originEvaluation (planeConstants r)
      rw [exceptionalPlaneEvaluation_constants]
      simp [FrobeniusBlowupChartIteration.originEvaluation, planeConstants]
    · change Polynomial.eval 0 (exceptionalPlaneEvaluation (uCoord (k := k))) =
        FrobeniusBlowupChartIteration.originEvaluation uCoord
      rw [exceptionalPlaneEvaluation_u]
      simp [FrobeniusBlowupChartIteration.originEvaluation, uCoord]
  · change Polynomial.eval 0 (exceptionalPlaneEvaluation (vCoord (k := k))) =
      FrobeniusBlowupChartIteration.originEvaluation vCoord
    rw [exceptionalPlaneEvaluation_v]
    simp [FrobeniusBlowupChartIteration.originEvaluation, vCoord]

private theorem exceptionalPlaneEvaluation_point :
    (Spec.map (CommRingCat.ofHom (exceptionalPlaneEvaluation (k := k)))).base curvePoint =
      originPoint := by
  apply PrimeSpectrum.ext
  change Ideal.comap exceptionalPlaneEvaluation
    (FrobeniusGraphContact.parameterPointIdeal (0 : k)) = centerIdeal
  rw [FrobeniusGraphContact.parameterPointIdeal, ← Polynomial.ker_evalRingHom,
    RingHom.comap_ker, exceptionalPlaneEvaluation_origin,
    ← FrobeniusBlowupChartIteration.centerIdeal_eq_origin_kernel]

/-- The adjacent point lies on the new actual global center fiber: its
original projection is precisely the actual current center. -/
theorem adjacentPoint_mem_newFiber :
    (previousStrictι A).base (adjacentPoint A) ∈
      Set.range (PointBlowupGluing.globalCenterFiberι A.next.chart
        (originPoint (k := k)) A.next.center_closed).base := by
  rw [PointBlowupGluing.range_globalCenterFiberι]
  change ((successorCurveToStrict A ≫ previousStrictι A) ≫
    A.next.nextProjection).base curvePoint = A.next.chart.base originPoint
  rw [successorCurveToStrict_ι, successorCurve_projection, previousFiberChart_ι]
  change A.next.chart.base
    ((Spec.map (CommRingCat.ofHom (exceptionalPlaneEvaluation (k := k)))).base curvePoint) = _
  rw [exceptionalPlaneEvaluation_point]

abbrev adjacentStalk := (previousStrictTransform A).presheaf.stalk (adjacentPoint A)

/-- The original open chart supplies the actual stalk isomorphism. -/
def adjacentStalkEquiv : adjacentStalk A ≃+* curveStalk k :=
  (asIso ((successorCurveToStrict A).stalkMap curvePoint)).commRingCatIsoToRingEquiv

/-- The original new-exceptional equation v, restricted to the actual whole old curve. -/
def newExceptionalGerm : adjacentStalk A :=
  (adjacentStalkEquiv A).symm (oldCurveIntersectionGerm vEquation)

/-- Its chart restriction is the original ambient v-chart stalk pullback. -/
theorem newExceptionalGerm_pullback :
    (successorCurveToStrict A).stalkMap curvePoint (newExceptionalGerm A) =
      (oldCurveChartMorphism (k := k)).stalkMap curvePoint
        (StructureSheaf.toStalk (reesVChartRing k)
          ((oldCurveChartMorphism (k := k)).base curvePoint) vEquation) := by
  change adjacentStalkEquiv A ((adjacentStalkEquiv A).symm
    (oldCurveIntersectionGerm vEquation)) = _
  rw [RingEquiv.apply_symm_apply, oldCurveIntersectionGerm_pullback]

/-- Adjacent exceptional curves have actual local intersection quotient length one. -/
theorem adjacent_exceptional_contact_length :
    Module.length (adjacentStalk A)
      (adjacentStalk A ⧸ Ideal.span {newExceptionalGerm A}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv (adjacentStalkEquiv A)]
  change Module.length (curveStalk k)
    (curveStalk k ⧸ Ideal.span {adjacentStalkEquiv A
      ((adjacentStalkEquiv A).symm (oldCurveIntersectionGerm vEquation))}) = 1
  rw [RingEquiv.apply_symm_apply]
  exact oldCurve_stalk_quotient_length

end KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
