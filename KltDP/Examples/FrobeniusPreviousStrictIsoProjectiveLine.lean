import KltDP.Examples.FrobeniusPreviousStrictBlowdown
import KltDP.Examples.FrobeniusTowerChartCover
import KltDP.Examples.ProjectiveLinePointAtInfinity

/-!
# The previous exceptional strict transform is `P¹`

The blowdown `strictToFiber A : C ⟶ P` (BRIEF15) is an isomorphism over the two opens covering the
previous exceptional curve `P`:

* over the puncture `P ∖ {centre}`, the lift `punctureSection = toImage (wholePreviousLift)` is an open
  immersion (accepted reduced-closed-image criterion) hitting every point of `C` over the puncture, and it is
  a section of the blowdown (`strictToFiber_restrict_puncture_isIso`);
* over the finite chart `V₁ = range previousFiberChart`, the accepted axis chart `successorCurveToStrict` composes
  to `previousFiberChart` (`successorCurveToStrict_strictToFiber`) and hits every point of `C` over `V₁`: off the
  centre through the puncture section and `parameterToPreviousPuncture_wholeLift`, over the centre through the
  two-chart cover of the second stage (BRIEF9 `stage_succ_cover`), the accepted avoidance of the first chart and
  the reduced-closed-image description of `C` in the second chart (`strictToFiber_restrict_chart_isIso`).

Open immersions are local at the target, so `strictToFiber A` is an open immersion, surjective (BRIEF15), hence
an isomorphism: **`previousStrictIsoProjectiveLine : previousStrictTransform A ≅ P¹`**, and on `S_{p,n}` every
older exceptional curve is `≅ P¹` (**`sPn_oldExceptional_iso_projectiveLine`**).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusPreviousStrictIsoProjectiveLine

open KltDP.Geometry KltDP.Geometry.AffineBlowup KltDP.Geometry.SchematicImageOpenBaseChange
  KltDP.Geometry.SchematicImageToImageIso FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusBlowupIncidence FrobeniusGraphStalkContact FrobeniusGlobalBlowupStages
  FrobeniusStrictTransformClosure FrobeniusExceptionalSuccessorChart
  FrobeniusGlobalExceptionalSuccessor FrobeniusPreviousStrictBlowdown
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusTowerSecondChart
  FrobeniusTowerSecondChart.PlaneChartedScheme FrobeniusTowerChartCover.PlaneChartedScheme
  ProjectiveLinePointAtInfinity

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originPoint_asIdeal_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## The axis chart -/

/-- On the axis chart the blowdown is the finite chart of the previous exceptional curve. -/
theorem successorCurveToStrict_strictToFiber :
    successorCurveToStrict A ≫ strictToFiber A = previousFiberChart A := by
  apply (cancel_mono (previousFiberι A)).mp
  rw [Category.assoc, strictToFiber_ι, ← Category.assoc, successorCurveToStrict_ι,
    successorCurve_projection]

theorem previousFiberChart_curvePoint :
    (previousFiberChart A).base curvePoint = (strictToFiber A).base (adjacentPoint A) := by
  change _ = (strictToFiber A).base ((successorCurveToStrict A).base curvePoint)
  rw [← Scheme.comp_base_apply, successorCurveToStrict_strictToFiber]

/-- The parameter-zero point of the finite chart is the centre point of the previous curve. -/
theorem previousFiberι_chart_curvePoint :
    (previousFiberι A).base ((previousFiberChart A).base curvePoint) =
      A.next.chart.base (originPoint (k := k)) := by
  rw [previousFiberChart_curvePoint, strictToFiber_base]
  exact strictBlowdown_adjacentPoint A

theorem range_previousStrictι_eq_closure_lift :
    Set.range (previousStrictι A).base = closure (Set.range (wholePreviousLift A).base) := by
  letI : NoetherianSpace (projectiveSpace k 1) := projectiveSpace_noetherianSpace k 1
  letI : NoetherianSpace (previousFiber A) :=
    (previousFiberIso A).hom.isOpenEmbedding.isInducing.noetherianSpace
  letI : NoetherianSpace (previousPuncture A).toScheme :=
    (previousPuncture A).ι.isOpenEmbedding.isInducing.noetherianSpace
  rw [Scheme.IdealSheafData.range_gluedTo]
  exact Scheme.Hom.support_ker (wholePreviousLift A)

/-! ## Over the puncture -/

/-- The lift of the punctured previous curve into the strict transform. -/
def punctureSection : (previousPuncture A).toScheme ⟶ previousStrictTransform A :=
  SchematicImageGlued.toImage (wholePreviousLift A)

theorem punctureSection_ι : punctureSection A ≫ previousStrictι A = wholePreviousLift A :=
  SchematicImageGlued.toImage_inclusion (wholePreviousLift A)

theorem punctureSection_strictToFiber :
    punctureSection A ≫ strictToFiber A = (previousPuncture A).ι := by
  apply (cancel_mono (previousFiberι A)).mp
  rw [Category.assoc, strictToFiber_ι, ← Category.assoc, punctureSection_ι,
    wholePreviousLift_projection]

/-- The restricted inclusion of the previous curve over the puncture of the next centre. -/
abbrev puncturedFiberι : (previousPuncture A).toScheme ⟶
    (PointBlowupGluing.puncture A.next.chart (originPoint (k := k)) A.next.center_closed).toScheme :=
  previousFiberι A ∣_ PointBlowupGluing.puncture A.next.chart (originPoint (k := k)) A.next.center_closed

instance puncturedFiberι_isClosedImmersion : IsClosedImmersion (puncturedFiberι A) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _

instance punctureSection_isOpenImmersion : IsOpenImmersion (punctureSection A) := by
  apply ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image (puncturedFiberι A)
    (PointBlowupGluing.complementι A.next.chart (originPoint (k := k)) A.next.center_closed)
    (previousStrictι A) (punctureSection A)
  · exact punctureSection_ι A
  · exact range_previousStrictι_eq_closure_lift A

/-- Every point of the strict transform over the puncture lies on the puncture section. -/
theorem mem_range_punctureSection (z : previousStrictTransform A)
    (hz : (strictToFiber A).base z ∈ previousPuncture A) :
    z ∈ Set.range (punctureSection A).base := by
  have h1 : (previousStrictι A).base z ∈ Set.range (PointBlowupGluing.complementι A.next.chart
      (originPoint (k := k)) A.next.center_closed).base := by
    rw [PointBlowupGluing.range_complementι]
    change A.next.nextProjection.base ((previousStrictι A).base z) ∈
      PointBlowupGluing.puncture A.next.chart (originPoint (k := k)) A.next.center_closed
    rw [← strictToFiber_base]
    exact hz
  obtain ⟨w, hw⟩ := h1
  have h2 : (previousStrictι A).base z ∈ closure (Set.range (wholePreviousLift A).base) := by
    rw [← range_previousStrictι_eq_closure_lift]
    exact ⟨z, rfl⟩
  have h3 : w ∈ Set.range (puncturedFiberι A).base := by
    rw [← ReducedClosedImageChart.preimage_closure_range (puncturedFiberι A)
      (PointBlowupGluing.complementι A.next.chart (originPoint (k := k)) A.next.center_closed)]
    change (PointBlowupGluing.complementι A.next.chart (originPoint (k := k))
      A.next.center_closed).base w ∈ closure (Set.range (wholePreviousLift A).base)
    rw [hw]
    exact h2
  obtain ⟨y', hy'⟩ := h3
  refine ⟨y', (previousStrictι A).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, punctureSection_ι]
  change (puncturedFiberι A ≫ PointBlowupGluing.complementι A.next.chart (originPoint (k := k))
    A.next.center_closed).base y' = _
  rw [Scheme.comp_base_apply, hy', hw]

theorem range_punctureSection_subset :
    Set.range (punctureSection A).base ⊆
      Set.range (strictToFiber A ⁻¹ᵁ previousPuncture A).ι.base := by
  rintro _ ⟨y', rfl⟩
  rw [Scheme.Opens.range_ι]
  change (strictToFiber A).base ((punctureSection A).base y') ∈ previousPuncture A
  rw [← Scheme.comp_base_apply, punctureSection_strictToFiber, Scheme.Opens.ι_base_apply]
  exact y'.2

/-- The puncture section, into the part of the strict transform over the puncture. -/
def punctureSection' : (previousPuncture A).toScheme ⟶
    (strictToFiber A ⁻¹ᵁ previousPuncture A).toScheme :=
  IsOpenImmersion.lift (strictToFiber A ⁻¹ᵁ previousPuncture A).ι (punctureSection A)
    (range_punctureSection_subset A)

theorem punctureSection'_ι :
    punctureSection' A ≫ (strictToFiber A ⁻¹ᵁ previousPuncture A).ι = punctureSection A :=
  IsOpenImmersion.lift_fac _ _ _

instance punctureSection'_isOpenImmersion : IsOpenImmersion (punctureSection' A) := by
  haveI : IsOpenImmersion (punctureSection' A ≫ (strictToFiber A ⁻¹ᵁ previousPuncture A).ι) := by
    rw [punctureSection'_ι]
    infer_instance
  exact IsOpenImmersion.of_comp (punctureSection' A) (strictToFiber A ⁻¹ᵁ previousPuncture A).ι

theorem punctureSection'_surjective : Function.Surjective (punctureSection' A).base := by
  intro w
  obtain ⟨y', hy'⟩ := mem_range_punctureSection A
    ((strictToFiber A ⁻¹ᵁ previousPuncture A).ι.base w) w.2
  refine ⟨y', (strictToFiber A ⁻¹ᵁ previousPuncture A).ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, punctureSection'_ι]
  exact hy'

/-- The puncture section is an isomorphism onto the part of the strict transform over the puncture. -/
def punctureSectionIso :
    (previousPuncture A).toScheme ≅ (strictToFiber A ⁻¹ᵁ previousPuncture A).toScheme :=
  IsOpenImmersion.isoOfRangeEq (punctureSection' A) (𝟙 _)
    ((Set.range_eq_univ.mpr (punctureSection'_surjective A)).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)

theorem punctureSectionIso_hom : (punctureSectionIso A).hom = punctureSection' A := by
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac (punctureSection' A) (𝟙 _)
    ((Set.range_eq_univ.mpr (punctureSection'_surjective A)).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)
  rwa [Category.comp_id] at h

instance punctureSection'_isIso : IsIso (punctureSection' A) := by
  rw [← punctureSectionIso_hom]
  infer_instance

theorem punctureSection'_restrict :
    punctureSection' A ≫ (strictToFiber A ∣_ previousPuncture A) = 𝟙 _ := by
  apply (cancel_mono (previousPuncture A).ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, punctureSection'_ι,
    punctureSection_strictToFiber, Category.id_comp]

/-- **The blowdown is an isomorphism over the puncture.** -/
instance strictToFiber_restrict_puncture_isIso : IsIso (strictToFiber A ∣_ previousPuncture A) := by
  have h : strictToFiber A ∣_ previousPuncture A = inv (punctureSection' A) := by
    rw [← IsIso.inv_hom_id_assoc (punctureSection' A) (strictToFiber A ∣_ previousPuncture A),
      punctureSection'_restrict, Category.comp_id]
  rw [h]
  infer_instance

/-! ## Over the finite chart -/

/-- Membership in a preimage open (stated on variables, so that the kernel never unfolds the
morphism). -/
theorem mem_preimage_iff' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x : X) :
    x ∈ f ⁻¹ᵁ U ↔ f.base x ∈ U := Iff.rfl

/-- Membership in the range open of an open immersion (stated on variables). -/
theorem mem_opensRange_iff' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (y : Y) :
    y ∈ f.opensRange ↔ y ∈ Set.range f.base := Iff.rfl

/-- The finite chart of the previous exceptional curve, as an open. -/
abbrev chartOpen₁ : (previousFiber A).Opens := (previousFiberChart A).opensRange

theorem strictToFiber_successorCurveToStrict_base (x : Spec (CommRingCat.of (Polynomial k))) :
    (strictToFiber A).base ((successorCurveToStrict A).base x) = (previousFiberChart A).base x := by
  have h := congrArg (fun f => f.base x) (successorCurveToStrict_strictToFiber A)
  simp only [Scheme.comp_base_apply] at h
  exact h

theorem successorCurveToStrict_mem_preimage (x : Spec (CommRingCat.of (Polynomial k))) :
    (successorCurveToStrict A).base x ∈ strictToFiber A ⁻¹ᵁ chartOpen₁ A := by
  rw [mem_preimage_iff', strictToFiber_successorCurveToStrict_base, mem_opensRange_iff']
  exact ⟨x, rfl⟩

theorem range_successorCurveToStrict_subset :
    Set.range (successorCurveToStrict A).base ⊆
      Set.range (strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι.base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨(successorCurveToStrict A).base x, successorCurveToStrict_mem_preimage A x⟩, rfl⟩

/-- The axis chart, into the part of the strict transform over the finite chart. -/
def chartSection' : Spec (CommRingCat.of (Polynomial k)) ⟶
    (strictToFiber A ⁻¹ᵁ chartOpen₁ A).toScheme :=
  IsOpenImmersion.lift (strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι (successorCurveToStrict A)
    (range_successorCurveToStrict_subset A)

theorem chartSection'_ι :
    chartSection' A ≫ (strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι = successorCurveToStrict A :=
  IsOpenImmersion.lift_fac _ _ _

instance chartSection'_isOpenImmersion : IsOpenImmersion (chartSection' A) := by
  haveI : IsOpenImmersion (chartSection' A ≫ (strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι) := by
    rw [chartSection'_ι]
    infer_instance
  exact IsOpenImmersion.of_comp (chartSection' A) (strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι

/-- The axis in the second Rees chart of the second stage. -/
theorem successorCurve_eq_secondChart :
    successorCurve A =
      (oldCurveChartMorphism ≫ vChartIso.inv) ≫ secondChart A.next 0 := by
  change oldCurveChartMorphism ≫ chartι centerIdeal centerV ≫ A.next.nextAffineBlowup =
    (oldCurveChartMorphism ≫ vChartIso.inv) ≫
      (vChartIso.hom ≫ chartι centerIdeal centerV ≫ A.next.nextAffineBlowup)
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- A point of the strict transform lying over the centre is on the axis chart. -/
theorem mem_range_successorCurveToStrict_of_center (z : previousStrictTransform A)
    (hz : A.next.nextProjection.base ((previousStrictι A).base z) =
      A.next.chart.base (originPoint (k := k))) :
    z ∈ Set.range (successorCurveToStrict A).base := by
  rcases stage_succ_cover A.next 0 ((previousStrictι A).base z) with h1 | h2 | h3
  · exact (previousStrict_avoids_nextChart A z h1).elim
  · have hcl : (previousStrictι A).base z ∈ closure (Set.range (successorCurve A).base) := by
      rw [← range_previousStrictι]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := h2
    have hw' : w ∈ Set.range (oldCurveChartMorphism ≫ vChartIso.inv).base := by
      rw [← ReducedClosedImageChart.preimage_closure_range (oldCurveChartMorphism ≫ vChartIso.inv)
        (secondChart A.next 0)]
      change (secondChart A.next 0).base w ∈
        closure (Set.range ((oldCurveChartMorphism ≫ vChartIso.inv) ≫ secondChart A.next 0).base)
      rw [← successorCurve_eq_secondChart, hw]
      exact hcl
    obtain ⟨x, hx⟩ := hw'
    refine ⟨x, (previousStrictι A).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.comp_base_apply, successorCurveToStrict_ι, ← hw, ← hx, ← Scheme.comp_base_apply,
      ← successorCurve_eq_secondChart]
    rfl
  · exfalso
    have h3' : A.next.nextProjection.base ((previousStrictι A).base z) ∈
        ({A.next.chart.base (originPoint (k := k))} : Set A.next.carrier)ᶜ := h3
    exact h3' hz

/-- Every point of the strict transform over the finite chart lies on the axis chart. -/
theorem mem_range_successorCurveToStrict (z : previousStrictTransform A)
    (hz : (strictToFiber A).base z ∈ chartOpen₁ A) :
    z ∈ Set.range (successorCurveToStrict A).base := by
  by_cases hp : (strictToFiber A).base z ∈ previousPuncture A
  · obtain ⟨y', hy'⟩ := mem_range_punctureSection A z hp
    obtain ⟨x, hx⟩ := (mem_opensRange_iff' _ _).mp hz
    have hxc : x ≠ curvePoint := by
      intro hxc
      have hp' : ¬ ((previousFiberι A).base ((strictToFiber A).base z) =
          A.next.chart.base (originPoint (k := k))) := hp
      apply hp'
      rw [hxc] at hx
      rw [← hx, previousFiberι_chart_curvePoint]
    have hxp : x ∈ parameterPuncture (k := k) := by
      change Polynomial.X ∉ x.asIdeal
      intro hX
      exact hxc (eq_parameterSchemePoint_zero_of_X_mem x hX)
    have hy'' : (parameterToPreviousPuncture A).base ⟨x, hxp⟩ = y' := by
      apply (previousPuncture A).ι.isOpenEmbedding.injective
      rw [← Scheme.comp_base_apply, parameterToPreviousPuncture_ι, Scheme.comp_base_apply,
        Scheme.Opens.ι_base_apply, Scheme.Opens.ι_base_apply, hx, ← hy',
        ← Scheme.comp_base_apply, punctureSection_strictToFiber, Scheme.Opens.ι_base_apply]
    refine ⟨x, (previousStrictι A).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.comp_base_apply, successorCurveToStrict_ι, ← hy', ← hy'', ← Scheme.comp_base_apply,
      punctureSection_ι, ← Scheme.comp_base_apply, parameterToPreviousPuncture_wholeLift,
      Scheme.comp_base_apply, Scheme.Opens.ι_base_apply]
  · apply mem_range_successorCurveToStrict_of_center
    rw [← strictToFiber_base]
    have hp' : ¬ ¬ ((previousFiberι A).base ((strictToFiber A).base z) =
        A.next.chart.base (originPoint (k := k))) := hp
    exact Classical.not_not.mp hp'

theorem chartSection'_surjective : Function.Surjective (chartSection' A).base := by
  intro w
  obtain ⟨x, hx⟩ := mem_range_successorCurveToStrict A
    ((strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι.base w) w.2
  refine ⟨x, (strictToFiber A ⁻¹ᵁ chartOpen₁ A).ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.comp_base_apply, chartSection'_ι]
  exact hx

/-- The axis chart is an isomorphism onto the part of the strict transform over the finite chart. -/
def chartSectionIso :
    Spec (CommRingCat.of (Polynomial k)) ≅ (strictToFiber A ⁻¹ᵁ chartOpen₁ A).toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartSection' A) (𝟙 _)
    ((Set.range_eq_univ.mpr (chartSection'_surjective A)).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)

theorem chartSectionIso_hom : (chartSectionIso A).hom = chartSection' A := by
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac (chartSection' A) (𝟙 _)
    ((Set.range_eq_univ.mpr (chartSection'_surjective A)).trans
      (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)
  rwa [Category.comp_id] at h

instance chartSection'_isIso : IsIso (chartSection' A) := by
  rw [← chartSectionIso_hom]
  infer_instance

theorem chartSection'_restrict :
    chartSection' A ≫ (strictToFiber A ∣_ chartOpen₁ A) =
      (previousFiberChart A).isoOpensRange.hom := by
  apply (cancel_mono (chartOpen₁ A).ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, chartSection'_ι,
    successorCurveToStrict_strictToFiber, Scheme.Hom.isoOpensRange_hom_ι]

/-- **The blowdown is an isomorphism over the finite chart.** -/
instance strictToFiber_restrict_chart_isIso : IsIso (strictToFiber A ∣_ chartOpen₁ A) := by
  have h : strictToFiber A ∣_ chartOpen₁ A =
      inv (chartSection' A) ≫ (previousFiberChart A).isoOpensRange.hom := by
    rw [← IsIso.inv_hom_id_assoc (chartSection' A) (strictToFiber A ∣_ chartOpen₁ A),
      chartSection'_restrict]
  rw [h]
  infer_instance

/-! ## The isomorphism -/

/-- The two-element family of opens. -/
def coverOpens : Bool → (previousFiber A).Opens
  | true => chartOpen₁ A
  | false => previousPuncture A

/-- A point of the previous curve off the puncture is the parameter-zero point of the chart. -/
theorem eq_chart_curvePoint_of_not_mem_puncture (y : previousFiber A)
    (hy : y ∉ previousPuncture A) : y = (previousFiberChart A).base curvePoint := by
  apply (previousFiberι A).isClosedEmbedding.injective
  rw [previousFiberι_chart_curvePoint]
  have hy' : ¬ ¬ ((previousFiberι A).base y = A.next.chart.base (originPoint (k := k))) := hy
  exact Classical.not_not.mp hy'

/-- The two opens cover the previous exceptional curve. -/
theorem iSup_coverOpens : iSup (coverOpens A) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  show y ∈ iSup (coverOpens A)
  rw [Opens.mem_iSup]
  by_cases hy : y ∈ previousPuncture A
  · exact ⟨false, hy⟩
  · exact ⟨true, ⟨curvePoint, (eq_chart_curvePoint_of_not_mem_puncture A y hy).symm⟩⟩

/-- **The blowdown is an open immersion.** -/
instance strictToFiber_isOpenImmersion : IsOpenImmersion (strictToFiber A) := by
  apply IsLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion) (coverOpens A) (iSup_coverOpens A)
  intro b
  cases b
  · show IsOpenImmersion (strictToFiber A ∣_ previousPuncture A)
    infer_instance
  · show IsOpenImmersion (strictToFiber A ∣_ chartOpen₁ A)
    infer_instance

theorem strictToFiber_range_eq : Set.range (strictToFiber A).base = Set.univ :=
  Set.range_eq_univ.mpr (strictToFiber_surjective A).1

/-- **The blowdown is an isomorphism.** -/
instance strictToFiber_isIso : IsIso (strictToFiber A) := by
  have h := IsOpenImmersion.isoOfRangeEq_hom_fac (strictToFiber A) (𝟙 (previousFiber A))
    ((strictToFiber_range_eq A).trans (Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)).symm)
  rw [Category.comp_id] at h
  rw [← h]
  infer_instance

/-- **The previous exceptional strict transform is the projective line.** -/
def previousStrictIsoProjectiveLine : previousStrictTransform A ≅ projectiveSpace k 1 :=
  asIso (strictToFiber A) ≪≫ previousFiberIso A

end KltDP.Examples.FrobeniusPreviousStrictIsoProjectiveLine

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor
  FrobeniusTranslatedCharts FrobeniusExceptionalFinalConfiguration FrobeniusMultiCentreExceptional
  FrobeniusPreviousStrictIsoProjectiveLine

/-- **Every older exceptional curve `C_ij` of `S_{p,n}` is isomorphic to `P¹`.** -/
theorem sPn_oldExceptional_iso_projectiveLine (k : Type u) [Field k] [IsAlgClosed k] (q n : ℕ)
    (a : Fin n → k) (ha : Function.Injective a) :
    ∀ (i : Fin n) (j : Fin q),
      Nonempty (exceptionalCurve q n a i (Sum.inl j) ≅ projectiveSpace k 1) :=
  fun i j => ⟨exceptionalCurveIso q n a ha i (Sum.inl j) ≪≫
    previousStrictIsoProjectiveLine ((translatedInitial (q + 1) (a i)).stage j.val)⟩

/-- The bundle has exactly one universe parameter. -/
theorem sPn_oldExceptional_iso_projectiveLine_universe_check (k : Type u) [Field k] [IsAlgClosed k]
    (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a) : True := by
  have _ := sPn_oldExceptional_iso_projectiveLine.{u} k q n a ha
  trivial

end KltDP.Examples
