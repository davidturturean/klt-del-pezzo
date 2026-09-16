import KltDP.Examples.FrobeniusClosureContact

/-!
# The strict fibre on an arbitrary charted plane tower

The tangent fibre through the selected centre is the line `v = 0` of the distinguished polynomial
chart. In the accepted Rees chart `v = u·w` its strict transform is again `w = 0`, so in every
selected stage chart the strict fibre is the same line `fiberCurve : Spec k[t] ⟶ Spec k[u][v]`
(`u = t, v = 0`); this is `fiberCurve_blowdown` and `fiberCurve_stageProjection`. Mirroring the
accepted generic local closure of the graph (`FrobeniusStrictTransformClosure`), the strict fibre on
the stage-`n` scheme of an arbitrary `PlaneChartedScheme A` is the schematic closure
`liftedFiberClosure A n` of the punctured line `D(t)`; it is a closed integral subscheme with the
full line as an open chart (`fiberResidualToClosure`, accepted reduced-image chart criterion).

Proved for every `A`, `n`:

* the strict fibre passes through every stage centre (`fiberContactPoint_inclusion`), and at a
  successor stage its centre point lies on the newest exceptional fibre `P`
  (`fiberClosure_terminal_mem_newestFiber`);
* every point of the strict fibre over the initial plane lies in the current chart, hence the strict
  fibre is disjoint from every exceptional component created before the last blowup
  (`fiberClosure_disjoint_finalOld`, `fiberClosure_disjoint_finalSupport`);
* in the terminal chart the strict fibre `v = 0` and the terminal graph `v = 1` are disjoint
  (`fiberCurve_curveInPlane_zero_disjoint`).

The identification of this closure with the strict transform of the whole tangent fibre of
`P¹ ×_k P¹` on a translated tower (the analogue of `FrobeniusAdaptedStrictTransform`) needs the
translation of the fibre chart and is not part of this module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusFiberClosure

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusStrictTransformStageCover
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalFinalConfiguration
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusMultiCentreExceptional
  FrobeniusBlowupIncidence

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The point of a composite rational point is the image of the point. -/
theorem fieldMorphismPoint_comp {X Y : Scheme.{u}} (f : Spec (CommRingCat.of k) ⟶ X) (g : X ⟶ Y) :
    fieldMorphismPoint (f ≫ g) = g.base (fieldMorphismPoint f) :=
  Scheme.comp_base_apply f g _

local instance parameterPuncture_noetherianSpace :
    TopologicalSpace.NoetherianSpace (parameterPuncture (k := k)).toScheme := by
  letI : TopologicalSpace.NoetherianSpace (Spec (CommRingCat.of (Polynomial k))) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum (Polynomial k)))
  exact (parameterPuncture (k := k)).ι.isOpenEmbedding.isInducing.noetherianSpace

/-! ## The fibre line of the polynomial plane -/

/-- The fibre `v = 0` of the polynomial plane, parametrised by `u = t`. -/
def fiberCurve : Spec (CommRingCat.of (Polynomial k)) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Polynomial k)))

instance fiberCurve_isClosedImmersion : IsClosedImmersion (fiberCurve (k := k)) :=
  IsClosedImmersion.spec_of_surjective _ (fun r => ⟨Polynomial.C r, by simp⟩)

/-- Under the Rees chart substitution `v ↦ u·v`, the fibre equation `v = 0` is preserved. -/
theorem fiberEvaluation_substitution :
    (Polynomial.evalRingHom (0 : Polynomial k)).comp chartSubstitution =
      Polynomial.evalRingHom 0 := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · change Polynomial.evalRingHom (0 : Polynomial k) (chartSubstitution (vCoord (k := k))) =
      Polynomial.evalRingHom 0 vCoord
    rw [chartSubstitution_v, map_mul]
    simp [uCoord, vCoord]

/-- The fibre is its own strict transform in the selected Rees chart. -/
@[reassoc] theorem fiberCurve_blowdown : fiberCurve (k := k) ≫ coordinateBlowdown = fiberCurve := by
  rw [coordinateBlowdown_eq, fiberCurve, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    fiberEvaluation_substitution]

theorem fiberCurve_stageProjection (n : ℕ) :
    fiberCurve (k := k) ≫ stageProjection n = fiberCurve := by
  induction n with
  | zero => exact Category.comp_id _
  | succ n ih => rw [stageProjection_succ, ← Category.assoc, fiberCurve_blowdown, ih]

/-- The fibre passes through the origin. -/
theorem parameterOrigin_fiberCurve :
    parameterOriginMorphism (k := k) ≫ fiberCurve = originMorphism := by
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Polynomial k))) =
      Spec.map (CommRingCat.ofHom originEvaluation)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- In the terminal chart the strict fibre `v = 0` and the terminal graph `v = 1` are disjoint. -/
theorem fiberCurve_curveInPlane_zero_disjoint :
    Disjoint (Set.range (fiberCurve (k := k)).base) (Set.range (curveInPlane (k := k) 0).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨q', hq'⟩
  have hv : vCoord (k := k) ∈ ((fiberCurve (k := k)).base q).asIdeal := by
    change (Polynomial.evalRingHom (0 : Polynomial k)) vCoord ∈ q.asIdeal
    simp [vCoord]
  have hv1 : vCoord (k := k) - 1 ∈ ((fiberCurve (k := k)).base q).asIdeal := by
    rw [← hq']
    change (Polynomial.evalRingHom (Polynomial.X ^ 0 : Polynomial k)) (vCoord - 1) ∈ q'.asIdeal
    simp [vCoord]
  have h1 : (1 : planeRing k) ∈ ((fiberCurve (k := k)).base q).asIdeal := by
    have := ((fiberCurve (k := k)).base q).asIdeal.sub_mem hv hv1
    simpa only [sub_sub_cancel] using this
  exact ((fiberCurve (k := k)).base q).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-! ## The strict fibre on a tower -/

variable (A : PlaneChartedScheme k)

/-- The strict fibre in the stage-`n` chart, as a morphism into the whole stage. -/
def fiberResidual (n : ℕ) : Spec (CommRingCat.of (Polynomial k)) ⟶ (A.stage n).carrier :=
  fiberCurve ≫ (A.stage n).chart

@[reassoc] theorem fiberResidual_toInitial (n : ℕ) :
    fiberResidual A n ≫ A.toInitial n = fiberCurve ≫ A.chart := by
  rw [fiberResidual, Category.assoc, PlaneChartedScheme.stage_chart_toInitial, ← Category.assoc,
    fiberCurve_stageProjection]

/-- The strict fibre passes through every stage centre. -/
theorem parameterOrigin_fiberResidual (n : ℕ) :
    parameterOriginMorphism (k := k) ≫ fiberResidual A n = (A.stage n).centerMorphism := by
  rw [fiberResidual, ← Category.assoc, parameterOrigin_fiberCurve]
  rfl

/-- The strict fibre restricted to the punctured parameter line. -/
def puncturedFiberResidual (n : ℕ) :
    (parameterPuncture (k := k)).toScheme ⟶ (A.stage n).carrier :=
  parameterPuncture.ι ≫ fiberResidual A n

/-- The schematic closure of the punctured strict fibre. -/
def liftedFiberClosureIdeal (n : ℕ) : (A.stage n).carrier.IdealSheafData :=
  (puncturedFiberResidual A n).ker

theorem liftedFiberClosureIdeal_eq (n : ℕ) :
    liftedFiberClosureIdeal A n = (fiberResidual A n).ker :=
  SchematicImageDenseOpen.ker_precompose_open parameterPuncture (fiberResidual A n)

/-- The strict fibre of the tower as an actual closed subscheme. -/
abbrev liftedFiberClosure (n : ℕ) : Scheme.{u} := (liftedFiberClosureIdeal A n).glueData.glued

abbrev fiberClosureInclusion (n : ℕ) : liftedFiberClosure A n ⟶ (A.stage n).carrier :=
  (liftedFiberClosureIdeal A n).gluedTo

instance fiberClosureInclusion_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (fiberClosureInclusion A n) :=
  (liftedFiberClosureIdeal A n).gluedTo_isClosedImmersion

theorem range_fiberClosureInclusion_eq_residual (n : ℕ) :
    Set.range (fiberClosureInclusion A n).base = closure (Set.range (fiberResidual A n).base) := by
  rw [Scheme.IdealSheafData.range_gluedTo, liftedFiberClosureIdeal_eq]
  exact Scheme.Hom.support_ker (fiberResidual A n)

instance liftedFiberClosure_isReduced (n : ℕ) : IsReduced (liftedFiberClosure A n) :=
  SchematicImageDenseOpen.image_glued_isReduced (puncturedFiberResidual A n)

theorem liftedFiberClosure_support_isIrreducible (n : ℕ) :
    IsIrreducible ((liftedFiberClosureIdeal A n).support : Set (A.stage n).carrier) := by
  rw [liftedFiberClosureIdeal_eq, Scheme.Hom.support_ker]
  have h := (IrreducibleSpace.isIrreducible_univ
    (Spec (CommRingCat.of (Polynomial k)))).image (fiberResidual A n).base
      (fiberResidual A n).continuous.continuousOn
  simpa only [Set.image_univ] using h.closure

instance liftedFiberClosure_irreducibleSpace (n : ℕ) :
    IrreducibleSpace (liftedFiberClosure A n) := by
  let I := liftedFiberClosureIdeal A n
  letI : IrreducibleSpace I.support :=
    Subtype.irreducibleSpace (liftedFiberClosure_support_isIrreducible A n)
  apply (irreducibleSpace_def (liftedFiberClosure A n)).mpr
  have h := (IrreducibleSpace.isIrreducible_univ I.support).image
    I.gluedSupportHomeomorph.symm I.gluedSupportHomeomorph.symm.continuous.continuousOn
  simpa only [Set.image_univ, I.gluedSupportHomeomorph.symm.surjective.range_eq] using h

/-- The strict fibre is an integral curve. -/
instance liftedFiberClosure_isIntegral (n : ℕ) : IsIntegral (liftedFiberClosure A n) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### The line as an open chart of the strict fibre -/

def fiberClosureIsoImage (n : ℕ) :
    liftedFiberClosure A n ≅ SchematicImageGlued.image (fiberResidual A n) :=
  eqToIso (congrArg (fun I : (A.stage n).carrier.IdealSheafData => I.glueData.glued)
    (liftedFiberClosureIdeal_eq A n))

private theorem gluedTo_eqToHom {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg (fun K : X.IdealSheafData => K.glueData.glued) h) ≫ J.gluedTo =
      I.gluedTo := by
  subst J
  exact Category.id_comp _

@[reassoc] theorem fiberClosureIsoImage_hom_inclusion (n : ℕ) :
    (fiberClosureIsoImage A n).hom ≫ SchematicImageGlued.inclusion (fiberResidual A n) =
      fiberClosureInclusion A n :=
  gluedTo_eqToHom _ _ (liftedFiberClosureIdeal_eq A n)

/-- The full strict-fibre line factors through the closure. -/
def fiberResidualToClosure (n : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ liftedFiberClosure A n :=
  SchematicImageGlued.toImage (fiberResidual A n) ≫ (fiberClosureIsoImage A n).inv

@[reassoc] theorem fiberResidualToClosure_inclusion (n : ℕ) :
    fiberResidualToClosure A n ≫ fiberClosureInclusion A n = fiberResidual A n := by
  rw [fiberResidualToClosure, Category.assoc, ← fiberClosureIsoImage_hom_inclusion A n,
    Iso.inv_hom_id_assoc, SchematicImageGlued.toImage_inclusion]

/-- The line is an open chart of the strict fibre. -/
instance fiberResidualToClosure_isOpenImmersion (n : ℕ) :
    IsOpenImmersion (fiberResidualToClosure A n) := by
  apply ReducedClosedImageChart.isOpenImmersion_of_reduced_closed_image
    fiberCurve (A.stage n).chart (fiberClosureInclusion A n) (fiberResidualToClosure A n)
  · exact fiberResidualToClosure_inclusion A n
  · exact range_fiberClosureInclusion_eq_residual A n

/-- The centre point of the strict fibre. -/
def fiberContactPoint (n : ℕ) : liftedFiberClosure A n :=
  (fiberResidualToClosure A n).base (curvePoint (k := k))

/-- The strict fibre passes through the stage centre. -/
theorem fiberContactPoint_inclusion (n : ℕ) :
    (fiberClosureInclusion A n).base (fiberContactPoint A n) =
      (A.stage n).chart.base (originPoint (k := k)) := by
  change (fiberResidualToClosure A n ≫ fiberClosureInclusion A n).base curvePoint = _
  rw [fiberResidualToClosure_inclusion]
  have he : fieldMorphismPoint (parameterOriginMorphism (k := k) ≫ fiberResidual A n) =
      (A.stage n).chart.base (originPoint (k := k)) :=
    (congrArg fieldMorphismPoint (parameterOrigin_fiberResidual A n)).trans
      (PlaneChartedScheme.centerMorphism_point (A.stage n))
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  rw [fieldMorphismPoint_comp, hp] at he
  exact he

/-- The blowdown fixes the origin of the chart. -/
theorem coordinateBlowdown_originPoint :
    (coordinateBlowdown (k := k)).base originPoint = originPoint := by
  rw [coordinateBlowdown_eq]
  apply PrimeSpectrum.ext
  change Ideal.comap chartSubstitution centerIdeal = centerIdeal
  rw [centerIdeal_eq_origin_kernel, RingHom.comap_ker,
    FrobeniusStageComplement.originEvaluation_chartSubstitution]

/-- At a successor stage the centre point of the strict fibre lies on the newest exceptional fibre. -/
theorem fiberClosure_terminal_mem_newestFiber (n : ℕ) :
    (fiberClosureInclusion A (n + 1)).base (fiberContactPoint A (n + 1)) ∈
      Set.range (previousFiberι (A.stage n)).base := by
  change _ ∈ Set.range (PointBlowupGluing.globalCenterFiberι
    (A.stage n).chart (originPoint (k := k)) (A.stage n).center_closed).base
  rw [PointBlowupGluing.range_globalCenterFiberι]
  change (A.stepProjection n).base
    ((fiberClosureInclusion A (n + 1)).base (fiberContactPoint A (n + 1))) =
      (A.stage n).chart.base (originPoint (k := k))
  rw [fiberContactPoint_inclusion]
  have h2 : (A.stage (n + 1)).chart ≫ A.stepProjection n =
      coordinateBlowdown ≫ (A.stage n).chart :=
    PlaneChartedScheme.nextChart_projection (A.stage n)
  rw [← Scheme.comp_base_apply, h2, Scheme.comp_base_apply, coordinateBlowdown_originPoint]

/-! ### Separation from the earlier exceptional components -/

private theorem fiberResidual_range_initialPlane (n : ℕ) :
    Set.range (fiberResidual A n).base ⊆ Set.range (initialPlaneOpen A n).ι.base := by
  rintro _ ⟨t, rfl⟩
  refine ⟨⟨(fiberResidual A n).base t, ?_⟩, rfl⟩
  change (fiberResidual A n ≫ A.toInitial n).base t ∈ A.chart.opensRange
  rw [fiberResidual_toInitial]
  exact ⟨(fiberCurve (k := k)).base t, rfl⟩

/-- The strict fibre factored through the inverse image of the initial plane. -/
def initialPlaneFiberResidual (n : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ (initialPlaneOpen A n).toScheme :=
  IsOpenImmersion.lift (initialPlaneOpen A n).ι (fiberResidual A n)
    (fiberResidual_range_initialPlane A n)

@[reassoc] theorem initialPlaneFiberResidual_ι (n : ℕ) :
    initialPlaneFiberResidual A n ≫ (initialPlaneOpen A n).ι = fiberResidual A n :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem initialPlaneFiberResidual_projection (n : ℕ) :
    initialPlaneFiberResidual A n ≫ initialPlaneProjection A n = fiberCurve := by
  apply (cancel_mono A.chart).mp
  rw [Category.assoc, initialPlaneProjection_chart, ← Category.assoc,
    initialPlaneFiberResidual_ι, fiberResidual_toInitial]

instance initialPlaneFiberResidual_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (initialPlaneFiberResidual A n) := by
  letI : IsClosedImmersion (initialPlaneFiberResidual A n ≫ initialPlaneProjection A n) := by
    rw [initialPlaneFiberResidual_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (initialPlaneFiberResidual A n) (initialPlaneProjection A n)

/-- Every point of the strict fibre over the initial plane lies in the current chart. -/
theorem fiberClosure_initialPlane_mem_chart (n : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (fiberClosureInclusion A n).base) (hplane : x ∈ initialPlaneOpen A n) :
    x ∈ (A.stage n).chart.opensRange := by
  let z : (initialPlaneOpen A n).toScheme := ⟨x, hplane⟩
  have hz : z ∈ (initialPlaneOpen A n).ι.base ⁻¹'
      closure (Set.range (initialPlaneFiberResidual A n ≫ (initialPlaneOpen A n).ι).base) := by
    change x ∈ closure
      (Set.range (initialPlaneFiberResidual A n ≫ (initialPlaneOpen A n).ι).base)
    rw [initialPlaneFiberResidual_ι, ← range_fiberClosureInclusion_eq_residual]
    exact hx
  rw [ReducedClosedImageChart.preimage_closure_range] at hz
  obtain ⟨t, ht⟩ := hz
  refine ⟨(fiberCurve (k := k)).base t, ?_⟩
  change (fiberResidual A n).base t = x
  rw [← initialPlaneFiberResidual_ι A n]
  exact congrArg (initialPlaneOpen A n).ι.base ht

theorem fiberClosure_chart_or_puncture (n : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (fiberClosureInclusion A n).base) :
    x ∈ (A.stage n).chart.opensRange ∨ x ∈ stagePuncture A n := by
  by_cases hplane : x ∈ initialPlaneOpen A n
  · exact Or.inl (fiberClosure_initialPlane_mem_chart A n x hx hplane)
  · right
    change (A.toInitial n).base x ≠ A.chart.base originPoint
    intro heq
    apply hplane
    change (A.toInitial n).base x ∈ A.chart.opensRange
    exact ⟨originPoint, heq.symm⟩

/-- The strict fibre misses every exceptional component created before the last blowup. -/
theorem fiberClosure_disjoint_finalOld (N j : ℕ) (h : j + 2 ≤ N) :
    Disjoint (Set.range (fiberClosureInclusion A N).base)
      (Set.range (finalOldMap A N j h).base) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨z, hz⟩
  have hchart : x ∉ Set.range (A.stage N).chart.base := by
    rw [← hz]
    exact finalOldMap_avoids_chart A N j h z
  rcases fiberClosure_chart_or_puncture A N x hx with hc | hp
  · exact (hchart hc).elim
  · have hp' : (A.toInitial N).base x ≠ A.chart.base (originPoint (k := k)) := hp
    apply hp'
    rw [← hz]
    exact finalOldMap_projection_center A N j h z

theorem fiberClosure_disjoint_finalSupport (q : ℕ) (j : Fin q) :
    Disjoint (Set.range (fiberClosureInclusion A (q + 1)).base)
      (finalSupport A q (Sum.inl j : FinalIndex.{0} q)) :=
  fiberClosure_disjoint_finalOld A (q + 1) j.val (by omega)

end KltDP.Examples.FrobeniusFiberClosure
