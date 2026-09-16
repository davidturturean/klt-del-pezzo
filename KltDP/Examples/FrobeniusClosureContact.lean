import KltDP.Examples.FrobeniusStrictTransformContact
import KltDP.Examples.FrobeniusStrictTransformStageCover
import KltDP.Examples.FrobeniusMultiCentreExceptional

/-!
# Contact and separation for the local closure on an arbitrary charted plane

The accepted contact module (`FrobeniusStrictTransformContact`), stage cover
(`FrobeniusStrictTransformStageCover`) and the lane-F separation module state their results for
the whole-graph strict transform of the origin tower only. Their proofs, however, only use the
accepted *generic* local closure `liftedGraphClosure A n m` of the punctured residual curve
`v = u^m` in the stage-`n` chart of an arbitrary `PlaneChartedScheme A`, its open chart
`residualToClosure A n m` (accepted generic open immersion), and the generic Rees-chart
computations. This module reproduces those results on `liftedGraphClosure A n m` for every `A`:

* `closureContactPoint A n m` (parameter zero of the chart) is the next centre while `0 < m`;
* at every successor stage the stalk of the closure at that point is the accepted curve stalk,
  and the pulled Rees sections have the accepted lengths: exceptional `1`, strict fibre `m`, total
  fibre `m + 1`; at the terminal stage the strict-fibre germ is `1`;
* every point of the closure over the initial plane lies in the current chart, hence every point is
  in the current chart or in the stage puncture;
* the closure at stage `N` is disjoint from every exceptional component created before the last
  blowup, and its terminal contact point lies on the newest exceptional fibre.

Combined with `FrobeniusAdaptedStrictTransform` (which identifies the whole-curve strict transform
with this closure), these give the contact data for the translated towers and the tower at ∞.
Nothing is assumed: every statement is derived from the accepted generic constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusClosureContact

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusGlobalBlowupStages FrobeniusStrictTransformClosure FrobeniusStrictTransformContact
  FrobeniusBlowupIncidence FrobeniusStrictTransformStageCover
  FrobeniusGlobalExceptionalSuccessor FrobeniusExceptionalFinalConfiguration
  FrobeniusStageComplement.PlaneChartedScheme FrobeniusMultiCentreExceptional

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ## Contact lengths on the local closure -/

/-- At a successor stage the chart of the closure is the residual curve of the Rees chart followed
by its open inclusion into the whole stage. -/
@[reassoc] theorem residualToClosure_succ_inclusion (n m : ℕ) :
    residualToClosure A (n + 1) m ≫ closureInclusion A (n + 1) m =
      residualCurveChartMorphism m ≫
        AffineBlowup.chartι centerIdeal centerU ≫ (A.stage n).nextAffineBlowup := by
  rw [residualToClosure_inclusion, PlaneChartedScheme.residualCurve_succ]
  simp only [residualCurveMorphism, Category.assoc]

/-- The point of the closure selected by parameter zero. -/
def closureContactPoint (n m : ℕ) : liftedGraphClosure A n m :=
  (residualToClosure A n m).base (curvePoint (k := k))

/-- Before the contact is exhausted, this point is the next blowup centre. -/
theorem closureContactPoint_inclusion (n m : ℕ) (hm : 0 < m) :
    (closureInclusion A n m).base (closureContactPoint A n m) =
      (A.stage n).chart.base (originPoint (k := k)) := by
  change (residualToClosure A n m ≫ closureInclusion A n m).base curvePoint = _
  rw [residualToClosure_inclusion]
  have h := A.parameterOrigin_residualCurve n m hm
  have he := congrArg fieldMorphismPoint h
  rw [PlaneChartedScheme.centerMorphism_point] at he
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  change (A.residualCurve n m).base (fieldMorphismPoint (parameterOriginMorphism (k := k))) = _
    at he
  rwa [hp] at he

/-- The structure-sheaf stalk of the closure at the contact point. -/
abbrev closureContactStalk (n m : ℕ) :=
  (liftedGraphClosure A n m).presheaf.stalk (closureContactPoint A n m)

/-- The chart's stalk map identifies it with the accepted curve stalk. -/
def closureContactStalkEquiv (n m : ℕ) : closureContactStalk A n m ≃+* curveStalk k :=
  (asIso ((residualToClosure A n m).stalkMap curvePoint)).commRingCatIsoToRingEquiv

/-- The germ of a Rees-chart section on the closure. -/
def closureContactGerm (n m : ℕ) (s : reesChartRing k) : closureContactStalk A (n + 1) m :=
  (closureContactStalkEquiv A (n + 1) m).symm (intersectionGerm m s)

theorem closureContactGerm_pullback (n m : ℕ) (s : reesChartRing k) :
    (residualToClosure A (n + 1) m).stalkMap curvePoint (closureContactGerm A n m s) =
      (residualCurveChartMorphism m).stalkMap curvePoint
        (StructureSheaf.toStalk (reesChartRing k) (pointInChart m) s) := by
  change closureContactStalkEquiv A (n + 1) m
    ((closureContactStalkEquiv A (n + 1) m).symm (intersectionGerm m s)) = _
  rw [RingEquiv.apply_symm_apply, intersectionGerm_pullback]

@[simp] theorem closureContactStalkEquiv_germ (n m : ℕ) (s : reesChartRing k) :
    closureContactStalkEquiv A (n + 1) m (closureContactGerm A n m s) = intersectionGerm m s :=
  (closureContactStalkEquiv A (n + 1) m).apply_symm_apply _

/-- The exceptional equation has contact length one on the closure at every successor stage. -/
theorem closure_exceptional_contact_length (n m : ℕ) :
    Module.length (closureContactStalk A (n + 1) m)
      (closureContactStalk A (n + 1) m ⧸ Ideal.span {closureContactGerm A n m chartU}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (closureContactStalkEquiv A (n + 1) m), closureContactStalkEquiv_germ]
  exact exceptional_stalk_quotient_length m

/-- The strict-fibre equation has remaining contact length `m`. -/
theorem closure_strictFiber_contact_length (n m : ℕ) :
    Module.length (closureContactStalk A (n + 1) m)
      (closureContactStalk A (n + 1) m ⧸ Ideal.span {closureContactGerm A n m chartW}) = m := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (closureContactStalkEquiv A (n + 1) m), closureContactStalkEquiv_germ]
  exact fiber_stalk_quotient_length m

theorem closure_totalFiber_contactGerm (n m : ℕ) :
    closureContactGerm A n m (baseMap vCoord) =
      closureContactGerm A n m chartU * closureContactGerm A n m chartW := by
  apply (closureContactStalkEquiv A (n + 1) m).injective
  rw [map_mul, closureContactStalkEquiv_germ, closureContactStalkEquiv_germ,
    closureContactStalkEquiv_germ, ← chartU_mul_chartW]
  simp only [intersectionGerm, map_mul]

/-- The pulled preceding-stage fibre has contact length `m + 1`. -/
theorem closure_totalFiber_contact_length (n m : ℕ) :
    Module.length (closureContactStalk A (n + 1) m)
      (closureContactStalk A (n + 1) m ⧸
        Ideal.span {closureContactGerm A n m (baseMap vCoord)}) = m + 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv
    (closureContactStalkEquiv A (n + 1) m), closureContactStalkEquiv_germ,
    FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv curveStalkLocalEquiv]
  have h : curveStalkLocalEquiv (intersectionGerm m (baseMap (vCoord (k := k)))) =
      FrobeniusGraphContact.localParameter (0 : k) ^ (m + 1) := by
    rw [← chartU_mul_chartW]
    have hm : intersectionGerm m (chartU (k := k) * chartW) =
        intersectionGerm m chartU * intersectionGerm m chartW := by
      simp only [intersectionGerm, map_mul]
    rw [hm]
    rw [map_mul, curveStalkLocalEquiv_exceptional, curveStalkLocalEquiv_fiber,
      pow_succ, mul_comm]
  rw [h]
  simpa only [Nat.cast_add, Nat.cast_one] using
    KltDP.RingTheory.dvr_length_quotient_uniformizer_pow
      (FrobeniusGraphContact.parameterLocalRing (0 : k))
      (FrobeniusGraphContact.localParameter 0)
      (FrobeniusGraphContact.localParameter_uniformizer 0) (m + 1)

/-- At the terminal stage the strict-fibre coordinate is one on the closure. -/
theorem closure_terminal_strictFiber_germ (n : ℕ) :
    closureContactGerm A n 0 chartW = 1 := by
  apply (closureContactStalkEquiv A (n + 1) 0).injective
  rw [closureContactStalkEquiv_germ, map_one]
  simp only [intersectionGerm, residualCurveMap_w, pow_zero, map_one]

/-! ## The closure meets the current chart or the stage puncture -/

/-- Every point of the closure over the initial plane lies in the current chart. -/
theorem closure_initialPlane_mem_chart (n m : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (closureInclusion A n m).base)
    (hplane : x ∈ initialPlaneOpen A n) :
    x ∈ (A.stage n).chart.opensRange := by
  let z : (initialPlaneOpen A n).toScheme := ⟨x, hplane⟩
  have hz : z ∈ (initialPlaneOpen A n).ι.base ⁻¹'
      closure (Set.range (initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι).base) := by
    change x ∈ closure
      (Set.range (initialPlaneResidual A n m ≫ (initialPlaneOpen A n).ι).base)
    rw [initialPlaneResidual_ι, ← range_closureInclusion_eq_residual]
    exact hx
  rw [ReducedClosedImageChart.preimage_closure_range] at hz
  obtain ⟨t, ht⟩ := hz
  refine ⟨(curveInPlane m).base t, ?_⟩
  change (A.residualCurve n m).base t = x
  rw [← initialPlaneResidual_ι A n m]
  exact congrArg (initialPlaneOpen A n).ι.base ht

/-- Every point of the closure is in the current chart or in the stage puncture. -/
theorem closure_chart_or_puncture (n m : ℕ) (x : (A.stage n).carrier)
    (hx : x ∈ Set.range (closureInclusion A n m).base) :
    x ∈ (A.stage n).chart.opensRange ∨ x ∈ stagePuncture A n := by
  by_cases hplane : x ∈ initialPlaneOpen A n
  · exact Or.inl (closure_initialPlane_mem_chart A n m x hx hplane)
  · right
    change (A.toInitial n).base x ≠ A.chart.base originPoint
    intro heq
    apply hplane
    change (A.toInitial n).base x ∈ A.chart.opensRange
    exact ⟨originPoint, heq.symm⟩

/-! ## Separation from the earlier exceptional components -/

/-- A closure point outside the current chart does not lie over the original centre. -/
theorem closure_projection_ne_center (N m : ℕ) (x : (A.stage N).carrier)
    (hx : x ∈ Set.range (closureInclusion A N m).base)
    (hchart : x ∉ Set.range (A.stage N).chart.base) :
    (A.toInitial N).base x ≠ A.chart.base (originPoint (k := k)) := by
  rcases closure_chart_or_puncture A N m x hx with hc | hp
  · exact (hchart hc).elim
  · exact hp

/-- The closure at stage `N` misses every exceptional component created before the last blowup. -/
theorem closure_disjoint_finalOld (N j m : ℕ) (h : j + 2 ≤ N) :
    Disjoint (Set.range (closureInclusion A N m).base)
      (Set.range (finalOldMap A N j h).base) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨z, hz⟩
  have hchart : x ∉ Set.range (A.stage N).chart.base := by
    rw [← hz]
    exact finalOldMap_avoids_chart A N j h z
  apply closure_projection_ne_center A N m x hx hchart
  rw [← hz]
  exact finalOldMap_projection_center A N j h z

/-- Indexed form on the final configuration after `q + 1` blowups. -/
theorem closure_disjoint_finalSupport (q m : ℕ) (j : Fin q) :
    Disjoint (Set.range (closureInclusion A (q + 1) m).base)
      (finalSupport A q (Sum.inl j : FinalIndex.{0} q)) :=
  closure_disjoint_finalOld A (q + 1) j.val m (by omega)

/-- At the terminal stage the contact point of the closure lies on the newest exceptional fibre. -/
theorem closure_terminal_mem_newestFiber (n : ℕ) :
    (closureInclusion A (n + 1) 0).base (closureContactPoint A (n + 1) 0) ∈
      Set.range (previousFiberι (A.stage n)).base := by
  change _ ∈ Set.range (PointBlowupGluing.globalCenterFiberι
    (A.stage n).chart (originPoint (k := k)) (A.stage n).center_closed).base
  rw [PointBlowupGluing.range_globalCenterFiberι]
  change (A.stepProjection n).base
    ((closureInclusion A (n + 1) 0).base (closureContactPoint A (n + 1) 0)) =
      (A.stage n).chart.base (originPoint (k := k))
  have h1 : (closureInclusion A (n + 1) 0).base (closureContactPoint A (n + 1) 0) =
      (A.residualCurve (n + 1) 0).base curvePoint := by
    change (residualToClosure A (n + 1) 0 ≫ closureInclusion A (n + 1) 0).base curvePoint = _
    rw [residualToClosure_inclusion]
  rw [h1]
  have h2 : A.residualCurve (n + 1) 0 ≫ A.stepProjection n =
      curveInPlane 1 ≫ (A.stage n).chart := by
    rw [PlaneChartedScheme.residualCurve, Category.assoc]
    change curveInPlane 0 ≫ ((A.stage n).nextChart ≫ (A.stage n).nextProjection) = _
    rw [PlaneChartedScheme.nextChart_projection, ← Category.assoc, curveInPlane_blowdown]
  change (A.residualCurve (n + 1) 0 ≫ A.stepProjection n).base curvePoint = _
  rw [h2]
  change (A.stage n).chart.base ((curveInPlane (k := k) 1).base curvePoint) = _
  congr 1
  have h3 := congrArg fieldMorphismPoint (parameterOrigin_curveInPlane (k := k) 1 Nat.one_pos)
  rw [originMorphism_point] at h3
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  change (curveInPlane (k := k) 1).base (fieldMorphismPoint (parameterOriginMorphism (k := k))) =
    originPoint at h3
  rw [hp] at h3
  exact h3

end KltDP.Examples.FrobeniusClosureContact
