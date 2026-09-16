import KltDP.Examples.FrobeniusFiberClosure

/-!
# The closures meet the newest exceptional fibre in exactly their contact point

On an arbitrary charted plane `A`, every point of the newest exceptional fibre `P` of stage `n + 1` lies
over the current centre, hence over the initial plane (`previousFiber_mem_initialPlane`), and over the
initial plane the local closure of the graph and the strict fibre *are* the residual curves
`v = u^m`, `v = 0` of the selected chart (`closure_initialPlane_mem_residual`,
`fiberClosure_initialPlane_mem_residual`, sharpening the accepted `…_mem_chart` statements). A residual
point `(u, v) = (t, 1)` (terminal graph) or `(t, 0)` (fibre) lies on `P` iff its blowdown is the centre,
i.e. iff `t = 0`: so the terminal closure and the strict fibre meet `P` only in their contact points
(`closure_newest_unique`, `fiberClosure_newest_unique`), and over the initial plane the terminal closure
(`v = 1`) and the strict fibre (`v = 0`) are disjoint (`closure_fiberClosure_disjoint_initialPlane`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusClosureNewestUnique

open KltDP.Geometry FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
  FrobeniusStrictTransformClosure FrobeniusStrictTransformStageCover
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusGlobalExceptionalSuccessor
  FrobeniusBlowupIncidence FrobeniusGraphStalkContact FrobeniusClosureContact FrobeniusFiberClosure

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The terminal residual curve `v = 1` passes through the origin of the plane only via the
parameter `t = 0` of the curve `v = u`: `curveInPlane 1` at parameter zero is the origin. -/
theorem curveInPlane_one_curvePoint : (curveInPlane (k := k) 1).base curvePoint = originPoint := by
  have h3 := congrArg fieldMorphismPoint (parameterOrigin_curveInPlane (k := k) 1 Nat.one_pos)
  rw [originMorphism_point] at h3
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    polynomialEvaluation_point (0 : k)
  change (curveInPlane (k := k) 1).base (fieldMorphismPoint (parameterOriginMorphism (k := k))) =
    originPoint at h3
  rw [hp] at h3
  exact h3

/-- The fibre `v = 0` at parameter zero is the origin. -/
theorem fiberCurve_curvePoint : (fiberCurve (k := k)).base curvePoint = originPoint := by
  have h3 := congrArg fieldMorphismPoint (parameterOrigin_fiberCurve (k := k))
  rw [originMorphism_point] at h3
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    polynomialEvaluation_point (0 : k)
  change (fiberCurve (k := k)).base (fieldMorphismPoint (parameterOriginMorphism (k := k))) =
    originPoint at h3
  rw [hp] at h3
  exact h3

variable (A : PlaneChartedScheme k)

/-- A point lies on the newest exceptional fibre iff it lies over the current centre. -/
theorem mem_previousFiber_iff (n : ℕ) (x : (A.stage (n + 1)).carrier) :
    x ∈ Set.range (previousFiberι (A.stage n)).base ↔
      (A.stepProjection n).base x = (A.stage n).chart.base (originPoint (k := k)) := by
  change x ∈ Set.range (PointBlowupGluing.globalCenterFiberι (A.stage n).chart
    (originPoint (k := k)) (A.stage n).center_closed).base ↔ _
  rw [PointBlowupGluing.range_globalCenterFiberι]
  exact Iff.rfl

/-- Every point of the newest exceptional fibre lies over the initial plane. -/
theorem previousFiber_mem_initialPlane (n : ℕ) (x : (A.stage (n + 1)).carrier)
    (hx : x ∈ Set.range (previousFiberι (A.stage n)).base) : x ∈ initialPlaneOpen A (n + 1) := by
  have hstep := (mem_previousFiber_iff A n x).mp hx
  change (A.toInitial (n + 1)).base x ∈ A.chart.opensRange
  refine ⟨originPoint, ?_⟩
  rw [PlaneChartedScheme.toInitial_succ, Scheme.comp_base_apply, hstep]
  exact (centerPoint_toInitial A n).symm

/-- Every closure point over the initial plane is a point of the residual curve. -/
theorem closure_initialPlane_mem_residual (n m : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (closureInclusion A n m).base) (hplane : x ∈ initialPlaneOpen A n) :
    x ∈ Set.range (A.residualCurve n m).base := by
  let z : (initialPlaneOpen A n).toScheme := ⟨x, hplane⟩
  have hz : z ∈ (initialPlaneOpen A n).ι.base ⁻¹'
      closure (Set.range (initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι).base) := by
    change x ∈ closure
      (Set.range (initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι).base)
    rw [initialPlaneResidual_ι, ← range_closureInclusion_eq_residual]
    exact hx
  rw [ReducedClosedImageChart.preimage_closure_range] at hz
  obtain ⟨t, ht⟩ := hz
  refine ⟨t, ?_⟩
  rw [← initialPlaneResidual_ι A n m]
  exact congrArg (initialPlaneOpen A n).ι.base ht

/-- Every strict-fibre point over the initial plane is a point of the fibre line. -/
theorem fiberClosure_initialPlane_mem_residual (n : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (fiberClosureInclusion A n).base) (hplane : x ∈ initialPlaneOpen A n) :
    x ∈ Set.range (fiberResidual A n).base := by
  let z : (initialPlaneOpen A n).toScheme := ⟨x, hplane⟩
  have hz : z ∈ (initialPlaneOpen A n).ι.base ⁻¹'
      closure (Set.range (initialPlaneFiberResidual A n ≫ (initialPlaneOpen A n).ι).base) := by
    change x ∈ closure
      (Set.range (initialPlaneFiberResidual A n ≫ (initialPlaneOpen A n).ι).base)
    rw [initialPlaneFiberResidual_ι, ← range_fiberClosureInclusion_eq_residual]
    exact hx
  rw [ReducedClosedImageChart.preimage_closure_range] at hz
  obtain ⟨t, ht⟩ := hz
  refine ⟨t, ?_⟩
  rw [← initialPlaneFiberResidual_ι A n]
  exact congrArg (initialPlaneOpen A n).ι.base ht

/-- The terminal residual curve of stage `n + 1` blows down to the curve `v = u` of stage `n`. -/
theorem residualCurve_zero_stepProjection (n : ℕ) :
    A.residualCurve (n + 1) 0 ≫ A.stepProjection n = curveInPlane 1 ≫ (A.stage n).chart := by
  rw [PlaneChartedScheme.residualCurve, Category.assoc]
  change curveInPlane 0 ≫ ((A.stage n).nextChart ≫ (A.stage n).nextProjection) = _
  rw [PlaneChartedScheme.nextChart_projection, ← Category.assoc, curveInPlane_blowdown]

/-- The fibre line of stage `n + 1` blows down to the fibre line of stage `n`. -/
theorem fiberResidual_stepProjection (n : ℕ) :
    fiberResidual A (n + 1) ≫ A.stepProjection n = fiberCurve ≫ (A.stage n).chart := by
  rw [fiberResidual, Category.assoc]
  change fiberCurve ≫ ((A.stage n).nextChart ≫ (A.stage n).nextProjection) = _
  rw [PlaneChartedScheme.nextChart_projection, ← Category.assoc, fiberCurve_blowdown]

/-- **Uniqueness of the graph contact**: the terminal closure meets the newest exceptional fibre only
in its contact point. -/
theorem closure_newest_unique (n : ℕ) (x : (A.stage (n + 1)).carrier)
    (hx : x ∈ Set.range (closureInclusion A (n + 1) 0).base)
    (hP : x ∈ Set.range (previousFiberι (A.stage n)).base) :
    x = (closureInclusion A (n + 1) 0).base (closureContactPoint A (n + 1) 0) := by
  obtain ⟨t, rfl⟩ := closure_initialPlane_mem_residual A (n + 1) 0 x hx
    (previousFiber_mem_initialPlane A n x hP)
  have hstep := (mem_previousFiber_iff A n _).mp hP
  have h7 : (A.residualCurve (n + 1) 0 ≫ A.stepProjection n).base t =
      (curveInPlane 1 ≫ (A.stage n).chart).base t := by
    rw [residualCurve_zero_stepProjection]
  rw [Scheme.comp_base_apply, Scheme.comp_base_apply] at h7
  have h5 : (A.stage n).chart.base ((curveInPlane (k := k) 1).base t) =
      (A.stage n).chart.base originPoint := by
    rw [← hstep]
    exact h7.symm
  have h3 : (curveInPlane (k := k) 1).base t = originPoint :=
    (A.stage n).chart.isOpenEmbedding.injective h5
  have h6 : (curveInPlane (k := k) 1).base t = (curveInPlane (k := k) 1).base curvePoint := by
    rw [h3, curveInPlane_one_curvePoint]
  have h4 : t = curvePoint := (curveInPlane (k := k) 1).isClosedEmbedding.injective h6
  subst h4
  change _ = (residualToClosure A (n + 1) 0 ≫ closureInclusion A (n + 1) 0).base curvePoint
  rw [residualToClosure_inclusion]

/-- **Uniqueness of the fibre contact**: the strict fibre meets the newest exceptional fibre only in
its centre point. -/
theorem fiberClosure_newest_unique (n : ℕ) (x : (A.stage (n + 1)).carrier)
    (hx : x ∈ Set.range (fiberClosureInclusion A (n + 1)).base)
    (hP : x ∈ Set.range (previousFiberι (A.stage n)).base) :
    x = (fiberClosureInclusion A (n + 1)).base (fiberContactPoint A (n + 1)) := by
  obtain ⟨t, rfl⟩ := fiberClosure_initialPlane_mem_residual A (n + 1) x hx
    (previousFiber_mem_initialPlane A n x hP)
  have hstep := (mem_previousFiber_iff A n _).mp hP
  have h7 : (fiberResidual A (n + 1) ≫ A.stepProjection n).base t =
      (fiberCurve ≫ (A.stage n).chart).base t := by
    rw [fiberResidual_stepProjection]
  rw [Scheme.comp_base_apply, Scheme.comp_base_apply] at h7
  have h5 : (A.stage n).chart.base ((fiberCurve (k := k)).base t) =
      (A.stage n).chart.base originPoint := by
    rw [← hstep]
    exact h7.symm
  have h3 : (fiberCurve (k := k)).base t = originPoint :=
    (A.stage n).chart.isOpenEmbedding.injective h5
  have h6 : (fiberCurve (k := k)).base t = (fiberCurve (k := k)).base curvePoint := by
    rw [h3, fiberCurve_curvePoint]
  have h4 : t = curvePoint := (fiberCurve (k := k)).isClosedEmbedding.injective h6
  subst h4
  change _ = (fiberResidualToClosure A (n + 1) ≫ fiberClosureInclusion A (n + 1)).base curvePoint
  rw [fiberResidualToClosure_inclusion]

/-- Over the initial plane the terminal closure `v = 1` and the strict fibre `v = 0` are disjoint. -/
theorem closure_fiberClosure_disjoint_initialPlane (n : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (closureInclusion A n 0).base)
    (hf : x ∈ Set.range (fiberClosureInclusion A n).base) (hplane : x ∈ initialPlaneOpen A n) :
    False := by
  obtain ⟨t, rfl⟩ := closure_initialPlane_mem_residual A n 0 x hx hplane
  obtain ⟨s, hs⟩ := fiberClosure_initialPlane_mem_residual A n _ hf hplane
  rw [fiberResidual, PlaneChartedScheme.residualCurve, Scheme.comp_base_apply,
    Scheme.comp_base_apply] at hs
  have h : (fiberCurve (k := k)).base s = (curveInPlane (k := k) 0).base t :=
    (A.stage n).chart.isOpenEmbedding.injective hs
  exact Set.disjoint_left.mp fiberCurve_curveInPlane_zero_disjoint ⟨s, rfl⟩ ⟨t, h.symm⟩

/-- Points of the selected chart lie over the initial plane. -/
theorem chart_mem_initialPlane (n : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ (A.stage n).chart.opensRange) : x ∈ initialPlaneOpen A n := by
  obtain ⟨y, rfl⟩ := hx
  change (A.toInitial n).base ((A.stage n).chart.base y) ∈ A.chart.opensRange
  refine ⟨(stageProjection n).base y, ?_⟩
  have h : ((A.stage n).chart ≫ A.toInitial n).base y = (stageProjection n ≫ A.chart).base y := by
    rw [A.stage_chart_toInitial]
  rw [Scheme.comp_base_apply, Scheme.comp_base_apply] at h
  exact h.symm

/-- A common point of the terminal closure and the strict fibre lies in the stage puncture. -/
theorem closure_fiberClosure_mem_stagePuncture (n : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (closureInclusion A n 0).base)
    (hf : x ∈ Set.range (fiberClosureInclusion A n).base) : x ∈ stagePuncture A n := by
  rcases closure_chart_or_puncture A n 0 x hx with hc | hp
  · exact (closure_fiberClosure_disjoint_initialPlane A n x hx hf
      (chart_mem_initialPlane A n x hc)).elim
  · exact hp

end KltDP.Examples.FrobeniusClosureNewestUnique
