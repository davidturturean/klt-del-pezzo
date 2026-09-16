import KltDP.Examples.FrobeniusSpecialFiberCharts
import KltDP.Examples.FrobeniusStrictTransformFirstChartProduct
import KltDP.Examples.FrobeniusStrictTransformSecondChartProduct
import KltDP.Geometry.GluedIdealSheafKernel

/-!
# The strict `b`-fibre on the two Rees charts of the contact tower

On the contact tower `projectiveProductInitial` the strict transform of the tangent `b`-fibre
through the selected point is the actual closed integral curve `liftedFiberClosure` of stage `n`
(the schematic closure of the punctured line `v = 0` of the current chart), with inclusion
`fiberClosureInclusion`. This module computes its ideal on the Rees charts and proves the local
pullback-ideal identities behind the manuscript's `F_{n+1} = π^* F_n - E_n`:

* on the current plane chart of every stage the strict fibre is exactly the line `v = 0`: its
  chart ideal `fiberStrictFirstChartIdeal n` is `Ideal.span {vCoord}`
  (`fiberStrictFirstChartIdeal_eq_span`);
* on the first Rees chart of the next stage the pullback of that ideal is `(u·v) = (u)·(v)`, the
  ideal of the new exceptional curve `E_n` times the ideal of the next strict fibre
  (`fiberStrict_firstChart_totalIdeal_factorization`, from `chartSubstitution_v`);
* the strict fibre of the next stage is absent from the second Rees chart
  (`fiberStrict_secondChart_isEmpty`: the two charts overlap where `w = v/u ≠ 0`, while the fibre
  line has `w = 0`), and there the pullback of the fibre ideal is the ideal of `E_n`
  (`fiberStrict_secondChart_totalIdeal`).

The gluing of these local identities into an isomorphism of ideal lines on the whole next stage
and the resulting Picard relation are not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusFiberStrictCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusExceptionalSuccessorChart
open FrobeniusGlobalExceptionalSuccessor FrobeniusFiberClosure
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformFirstChartProduct FrobeniusStrictTransformSecondChartProduct

variable {k : Type u} [Field k]

local instance fiberChartOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-! ### The strict fibre on the current plane chart -/

/-- The strict fibre line of the current chart and the chart form an actual scheme pullback. -/
theorem fiberResidual_chart_isPullback (n : ℕ) :
    IsPullback (fiberCurve (k := k)) (𝟙 _) (((projectiveProductInitial (k := k)).stage n).chart)
      (fiberResidual (projectiveProductInitial (k := k)) n) := by
  have hr : Set.range (fiberResidual (projectiveProductInitial (k := k)) n).base ⊆
      Set.range (((projectiveProductInitial (k := k)).stage n).chart).base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(fiberCurve (k := k)).base t,
      (Scheme.comp_base_apply fiberCurve (((projectiveProductInitial (k := k)).stage n).chart)
        t).symm⟩
  have hLift : IsOpenImmersion.lift (((projectiveProductInitial (k := k)).stage n).chart)
      (fiberResidual (projectiveProductInitial (k := k)) n) hr = fiberCurve :=
    (IsOpenImmersion.lift_uniq _ _ hr fiberCurve rfl).symm
  simpa only [hLift] using
    IsOpenImmersion.isPullback_lift_id (fiberResidual (projectiveProductInitial (k := k)) n)
      (((projectiveProductInitial (k := k)).stage n).chart) hr

/-- The strict fibre's kernel ideal sheaf is the kernel of its chart line. -/
theorem fiberStrict_ker (n : ℕ) :
    (fiberClosureInclusion (projectiveProductInitial (k := k)) n).ker =
      (fiberResidual (projectiveProductInitial (k := k)) n).ker :=
  (Scheme.IdealSheafData.ker_gluedTo _).trans
    (liftedFiberClosureIdeal_eq (projectiveProductInitial (k := k)) n)

/-- The ideal of the strict fibre on the current plane chart, in the actual chart coordinates. -/
def fiberStrictFirstChartIdeal (n : ℕ) : Ideal (planeRing k) :=
  Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom
    (Ideal.comap (((projectiveProductInitial (k := k)).stage n).chart.appIso ⊤).inv.hom
      ((fiberClosureInclusion (projectiveProductInitial (k := k)) n).ker.ideal
        (firstAffineOpen n)))

private theorem fiberCurve_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
        (fiberCurve (k := k)).appTop).hom) =
      Ideal.span {vCoord} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).symm.commRingCatIsoToRingEquiv.injective
  rw [fiberCurve, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom, Polynomial.ker_evalRingHom]
  simp only [vCoord, Polynomial.C_0, sub_zero]

/-- On the current plane chart the strict fibre is exactly the line `v = 0`. -/
theorem fiberStrictFirstChartIdeal_eq_span (n : ℕ) :
    fiberStrictFirstChartIdeal (k := k) n = Ideal.span {vCoord} := by
  unfold fiberStrictFirstChartIdeal firstAffineOpen
  rw [fiberStrict_ker, ← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (fiberResidual (projectiveProductInitial (k := k)) n) fiberCurve (𝟙 _)
    (((projectiveProductInitial (k := k)).stage n).chart)
    (fiberResidual_chart_isPullback n) ⟨⊤, isAffineOpen_top (plane k)⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
    (fiberCurve (k := k)).appTop).hom) = _
  exact fiberCurve_coordinateKernel

/-! ### The first Rees chart of the next stage: `π^*(v) = u·v` -/

/-- The pullback-ideal identity on the first Rees chart: the ideal of the strict fibre of stage `n`
pulls back to the ideal of `E_n` times the ideal of the strict fibre of stage `n+1`, in the actual
chart coordinates. -/
theorem fiberStrict_firstChart_totalIdeal_factorization (n : ℕ) :
    Ideal.map (firstStepSectionMap (k := k)) (fiberStrictFirstChartIdeal (k := k) n) =
      stepExceptionalFirstChartIdeal (k := k) n * fiberStrictFirstChartIdeal (n + 1) := by
  rw [fiberStrictFirstChartIdeal_eq_span, fiberStrictFirstChartIdeal_eq_span,
    stepExceptionalFirstChartIdeal_eq_span, Ideal.map_span, Set.image_singleton,
    firstStepSectionMap_eq, chartSubstitution_v, Ideal.span_singleton_mul_span_singleton]

/-! ### The second Rees chart of the next stage: the strict fibre is absent -/

/-- The strict fibre line of the next stage avoids the second Rees chart: in the first chart its
points satisfy `w = 0`, while the two charts overlap exactly where `w = v/u ≠ 0`. -/
theorem fiberResidual_avoids_secondChart (n : ℕ) (t : Spec (CommRingCat.of (Polynomial k))) :
    (fiberResidual (projectiveProductInitial (k := k)) (n + 1)).base t ∉
      Set.range (secondStageChart (k := k) n).base := by
  rintro ⟨p, hp⟩
  have hres : (fiberResidual (projectiveProductInitial (k := k)) (n + 1)).base t =
      ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup.base
        ((chartι (centerIdeal (k := k)) centerU).base
          ((coordinateChartIso (k := k)).hom.base ((fiberCurve (k := k)).base t))) := by
    change (fiberCurve ≫ ((projectiveProductInitial (k := k)).stage n).nextChart).base t = _
    rw [PlaneChartedScheme.nextChart, coordinateChart, Category.assoc, Scheme.comp_base_apply,
      Scheme.comp_base_apply, Scheme.comp_base_apply]
  have hsec : (secondStageChart (k := k) n).base p =
      ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup.base
        ((chartι (centerIdeal (k := k)) centerV).base p) :=
    Scheme.comp_base_apply (chartι (centerIdeal (k := k)) centerV)
      ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup p
  have hmem : (coordinateChartIso (k := k)).hom.base ((fiberCurve (k := k)).base t) ∈
      (chartι (centerIdeal (k := k)) centerU).base ⁻¹'
        Set.range (chartι (centerIdeal (k := k)) centerV).base := by
    refine ⟨p, ?_⟩
    apply ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup.isOpenEmbedding.injective
    exact hsec.symm.trans (hp.trans hres)
  rw [chart_preimage_chart_range] at hmem
  change chartW (k := k) ∉
    ((coordinateChartIso (k := k)).hom.base ((fiberCurve (k := k)).base t)).asIdeal at hmem
  apply hmem
  change (chartPolynomialEquiv (k := k)) chartW ∈ ((fiberCurve (k := k)).base t).asIdeal
  rw [chartPolynomialEquiv_w]
  change (Polynomial.evalRingHom (0 : Polynomial k)) vCoord ∈ t.asIdeal
  simp [vCoord]

/-- The whole strict fibre of the next stage avoids the second Rees chart (the chart is open, so
the closure of the line still avoids it). -/
theorem fiberStrict_avoids_secondChart (n : ℕ)
    (z : liftedFiberClosure (projectiveProductInitial (k := k)) (n + 1)) :
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base z ∉
      Set.range (secondStageChart (k := k) n).base := by
  have h : Set.range (fiberResidual (projectiveProductInitial (k := k)) (n + 1)).base ⊆
      (Set.range (secondStageChart (k := k) n).base)ᶜ := by
    rintro _ ⟨t, rfl⟩
    exact fiberResidual_avoids_secondChart n t
  have hc := closure_minimal h
    (secondStageChart (k := k) n).isOpenEmbedding.isOpen_range.isClosed_compl
  apply hc
  rw [← range_fiberClosureInclusion_eq_residual]
  exact ⟨z, rfl⟩

/-- The strict fibre of stage `n+1` is absent from the second Rees chart of that stage. -/
theorem fiberStrict_secondChart_isEmpty (n : ℕ) :
    IsEmpty ((fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) ⁻¹ᵁ
      (secondAffineOpen (k := k) n).1) := by
  refine ⟨fun z => ?_⟩
  have hz : (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)).base z.1 ∈
      (secondStageChart (k := k) n ''ᵁ ⊤) := z.2
  rw [Scheme.Hom.image_top_eq_opensRange] at hz
  exact fiberStrict_avoids_secondChart n z.1 hz

/-- On the second Rees chart the pullback of the fibre ideal of stage `n` is the ideal of `E_n`:
the strict fibre contributes nothing there. -/
theorem fiberStrict_secondChart_totalIdeal (n : ℕ) :
    Ideal.map (chartBaseMap (centerIdeal (k := k)) centerV) (fiberStrictFirstChartIdeal (k := k) n) =
      stepExceptionalSecondChartIdeal (k := k) n := by
  rw [fiberStrictFirstChartIdeal_eq_span, stepExceptionalSecondChartIdeal_eq_span, Ideal.map_span,
    Set.image_singleton]
  rfl

end KltDP.Examples.FrobeniusFiberStrictCharts
