import KltDP.Examples.FrobeniusStrictTransformStageCover
import KltDP.Examples.FrobeniusStrictTransformContact
import KltDP.Examples.FrobeniusExceptionalFinalConfiguration

/-!
# Separation of the graph strict transform from the earlier exceptional curves

In the contact tower at the origin (`projectiveProductInitial`), the accepted modules give:
every point of the whole graph strict transform lies in the current selected chart or in the
stage puncture (`FrobeniusStrictTransformStageCover.strictTransform_chart_or_puncture`); every
earlier exceptional component, transported to the final stage, avoids the selected chart and
projects into its creation fibre, hence over the original centre
(`FrobeniusExceptionalFinalConfiguration.finalOldMap_avoids_chart`,
`finalOldMap_projection_mem_fiber`).

Combining these, the strict transform of the graph at stage `N` is disjoint from every earlier
exceptional component `finalOldMap A N j h` (`j + 2 ≤ N`), i.e. from every exceptional curve
created before the last blowup. At the terminal stage the accepted contact point of the strict
transform lies on the newest exceptional fibre, where the accepted contact length with the
exceptional equation is one (`FrobeniusStrictTransformContact.exceptional_contact_length`).

These are statements about the actual closed images inside the actual whole stage. No incidence,
intersection number, or configuration is assumed; uniqueness of the graph/exceptional intersection
point is not asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.FrobeniusGraphExceptionalSeparation

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusBlowupIncidence FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalSuccessor
  FrobeniusExceptionalLaterStages FrobeniusExceptionalFinalConfiguration
  FrobeniusGlobalStrictTransform FrobeniusStrictTransformStageCover
  FrobeniusStrictTransformContact FrobeniusStageComplement.PlaneChartedScheme

variable {k : Type u} [Field k]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- A strict-transform point outside the selected chart does not lie over the original centre. -/
theorem strictTransform_projection_ne_center (N m : ℕ) (x : projectiveContactStage (k := k) N)
    (hx : x ∈ Set.range (strictTransformι N (m + N)).base)
    (hchart : x ∉ Set.range ((projectiveProductInitial (k := k)).stage N).chart.base) :
    ((projectiveProductInitial (k := k)).toInitial N).base x ≠
      (projectiveProductInitial (k := k)).chart.base (originPoint (k := k)) := by
  rcases strictTransform_chart_or_puncture N m x hx with hc | hp
  · exact (hchart hc).elim
  · exact hp

/-- Every point of an earlier exceptional component projects to the original centre. -/
theorem finalOld_projection_center (N j : ℕ) (h : j + 2 ≤ N)
    (z : previousStrictTransform ((projectiveProductInitial (k := k)).stage j)) :
    ((projectiveProductInitial (k := k)).toInitial N).base
        ((finalOldMap (projectiveProductInitial (k := k)) N j h).base z) =
      (projectiveProductInitial (k := k)).chart.base (originPoint (k := k)) := by
  have hfib := finalOldMap_projection_mem_fiber (projectiveProductInitial (k := k)) N j h z
  change _ ∈ Set.range (PointBlowupGluing.globalCenterFiberι
    ((projectiveProductInitial (k := k)).stage j).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage j).center_closed).base at hfib
  rw [PointBlowupGluing.range_globalCenterFiberι] at hfib
  have hstep : ((projectiveProductInitial (k := k)).stepProjection j).base
      ((between (projectiveProductInitial (k := k)) (show j + 1 ≤ N by omega)).base
        ((finalOldMap (projectiveProductInitial (k := k)) N j h).base z)) =
      ((projectiveProductInitial (k := k)).stage j).chart.base (originPoint (k := k)) := hfib
  have hb : (projectiveProductInitial (k := k)).toInitial N =
      between (projectiveProductInitial (k := k)) (show j + 1 ≤ N by omega) ≫
        (projectiveProductInitial (k := k)).stepProjection j ≫
          (projectiveProductInitial (k := k)).toInitial j := by
    rw [← between_zero (projectiveProductInitial (k := k)) N,
      ← between_zero (projectiveProductInitial (k := k)) j,
      ← between_step (projectiveProductInitial (k := k)) j, between_comp, between_comp]
  rw [hb]
  change ((projectiveProductInitial (k := k)).toInitial j).base
    (((projectiveProductInitial (k := k)).stepProjection j).base
      ((between (projectiveProductInitial (k := k)) (show j + 1 ≤ N by omega)).base
        ((finalOldMap (projectiveProductInitial (k := k)) N j h).base z))) = _
  rw [hstep]
  exact centerPoint_toInitial (projectiveProductInitial (k := k)) j

/-- The whole graph strict transform at stage `N` is disjoint from every exceptional component
created before the last blowup. -/
theorem strictTransform_disjoint_finalOld (N j m : ℕ) (h : j + 2 ≤ N) :
    Disjoint (Set.range (strictTransformι (k := k) N (m + N)).base)
      (Set.range (finalOldMap (projectiveProductInitial (k := k)) N j h).base) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨z, hz⟩
  have hchart : x ∉ Set.range ((projectiveProductInitial (k := k)).stage N).chart.base := by
    rw [← hz]
    exact finalOldMap_avoids_chart (projectiveProductInitial (k := k)) N j h z
  apply strictTransform_projection_ne_center N m x hx hchart
  rw [← hz]
  exact finalOld_projection_center N j h z

/-- Indexed form: after `n + 1` blowups the graph strict transform misses all `n` earlier
exceptional components of the accepted final configuration. -/
theorem strictTransform_disjoint_finalSupport (n m : ℕ) (j : Fin n) :
    Disjoint (Set.range (strictTransformι (k := k) (n + 1) (m + (n + 1))).base)
      (finalSupport (projectiveProductInitial (k := k)) n (Sum.inl j)) :=
  strictTransform_disjoint_finalOld (n + 1) j.val m (by omega)

/-- At the terminal stage the accepted contact point of the graph strict transform lies on the
newest exceptional fibre. -/
theorem terminal_contactPoint_mem_newestFiber (n : ℕ) :
    (strictTransformι (k := k) (n + 1) (0 + (n + 1))).base (contactPoint (n + 1) 0) ∈
      Set.range (previousFiberι ((projectiveProductInitial (k := k)).stage n)).base := by
  change _ ∈ Set.range (PointBlowupGluing.globalCenterFiberι
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed).base
  rw [PointBlowupGluing.range_globalCenterFiberι]
  change ((projectiveProductInitial (k := k)).stepProjection n).base
    ((strictTransformι (n + 1) (0 + (n + 1))).base (contactPoint (n + 1) 0)) =
      ((projectiveProductInitial (k := k)).stage n).chart.base (originPoint (k := k))
  have h1 : (strictTransformι (k := k) (n + 1) (0 + (n + 1))).base (contactPoint (n + 1) 0) =
      ((projectiveProductInitial (k := k)).residualCurve (n + 1) 0).base curvePoint := by
    change (residualChart (n + 1) 0 ≫ strictTransformι (n + 1) (0 + (n + 1))).base curvePoint = _
    rw [residualChart_ι]
  rw [h1]
  have h2 : (projectiveProductInitial (k := k)).residualCurve (n + 1) 0 ≫
      (projectiveProductInitial (k := k)).stepProjection n =
        curveInPlane 1 ≫ ((projectiveProductInitial (k := k)).stage n).chart := by
    rw [PlaneChartedScheme.residualCurve, Category.assoc]
    change curveInPlane 0 ≫ (((projectiveProductInitial (k := k)).stage n).nextChart ≫
      ((projectiveProductInitial (k := k)).stage n).nextProjection) = _
    rw [PlaneChartedScheme.nextChart_projection, ← Category.assoc, curveInPlane_blowdown]
  change ((projectiveProductInitial (k := k)).residualCurve (n + 1) 0 ≫
    (projectiveProductInitial (k := k)).stepProjection n).base curvePoint = _
  rw [h2]
  change ((projectiveProductInitial (k := k)).stage n).chart.base
    ((curveInPlane (k := k) 1).base curvePoint) = _
  congr 1
  have h3 := congrArg fieldMorphismPoint (parameterOrigin_curveInPlane (k := k) 1 Nat.one_pos)
  rw [originMorphism_point] at h3
  have hp : fieldMorphismPoint (parameterOriginMorphism (k := k)) = curvePoint :=
    FrobeniusGraphStalkContact.polynomialEvaluation_point 0
  change (curveInPlane (k := k) 1).base (fieldMorphismPoint (parameterOriginMorphism (k := k))) =
    originPoint at h3
  rw [hp] at h3
  exact h3

end KltDP.Examples.FrobeniusGraphExceptionalSeparation
