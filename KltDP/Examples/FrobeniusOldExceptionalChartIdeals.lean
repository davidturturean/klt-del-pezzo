import KltDP.Examples.FrobeniusStrictTransformFirstChartProduct
import KltDP.Examples.FrobeniusStrictTransformSecondChartProduct
import KltDP.Examples.FrobeniusGlobalExceptionalSuccessor
import KltDP.Geometry.GluedIdealSheafKernel

/-!
# The older exceptional curve on the two Rees charts of the next stage

On the contact tower, the exceptional curve `E_j` created by the `(j+1)`-st blowup has an actual
strict transform under the `(j+2)`-nd blowup: the accepted `previousStrictι (A.stage j)`, glued
from the kernel of the lifted punctured fiber. This module computes its ideal on both Rees charts
of stage `j+2` and proves the local pullback-ideal identity behind the manuscript's
`C_j = E_j - E_{j+1}` (Proposition 10.1):

* on the second Rees chart the strict transform is the actual axis `u/v = 0`: its chart ideal is
  `Ideal.span {oldRatio}`, and the pullback of the first-chart ideal of `E_j` factors exactly as
  (ideal of `E_{j+1}`) times (ideal of the strict transform), from the accepted identity
  `vEquation * oldRatio = base u`;
* on the first Rees chart the strict transform is absent (the accepted avoidance theorem), and the
  pullback of the ideal of `E_j` is the ideal of `E_{j+1}`.

The global gluing of these local identities into an isomorphism of ideal lines on the whole stage,
its invariance under later blowups, and the resulting Picard relation are not proved here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusOldExceptionalChartIdeals

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusExceptionalSuccessorChart
open FrobeniusGlobalExceptionalSuccessor
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformSecondChart FrobeniusStrictTransformSecondChartFrame
open FrobeniusStrictTransformFirstChartProduct FrobeniusStrictTransformSecondChartProduct

variable {k : Type u} [Field k]

local instance oldChartOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The `j`-th stage of the contact tower as a plane-charted scheme. -/
abbrev previousStage (j : ℕ) : PlaneChartedScheme k := (projectiveProductInitial (k := k)).stage j

/-- The actual strict transform of the `(j+1)`-st exceptional curve on stage `j+2`, with its
codomain written as the stage. -/
def oldExceptionalStrictι (j : ℕ) :
    previousStrictTransform (previousStage (k := k) j) ⟶ projectiveContactStage (k := k) (j + 1 + 1) :=
  previousStrictι (previousStage j)

instance oldExceptionalStrictι_isClosedImmersion (j : ℕ) :
    IsClosedImmersion (oldExceptionalStrictι (k := k) j) :=
  inferInstanceAs (IsClosedImmersion (previousStrictι (previousStage (k := k) j)))

/-- The second-chart axis of the strict transform, with its codomain written as the stage. -/
def successorCurveSucc (j : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ projectiveContactStage (k := k) (j + 1 + 1) :=
  successorCurve (previousStage j)

/-- The axis is the old-curve chart morphism followed by the second Rees chart of the stage. -/
theorem successorCurveSucc_eq (j : ℕ) :
    successorCurveSucc (k := k) j = oldCurveChartMorphism ≫ secondStageChart (j + 1) := by
  unfold successorCurveSucc successorCurve oldCurveMorphism secondStageChart
  rw [Category.assoc]
  rfl

/-- The axis and the second Rees chart form an actual scheme pullback. -/
theorem successorCurveSucc_secondChart_isPullback (j : ℕ) :
    IsPullback (oldCurveChartMorphism (k := k)) (𝟙 _) (secondStageChart (j + 1))
      (successorCurveSucc j) := by
  have hr : Set.range (successorCurveSucc (k := k) j).base ⊆
      Set.range (secondStageChart (j + 1)).base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(oldCurveChartMorphism (k := k)).base t,
      congrArg (fun f => f.base t) (successorCurveSucc_eq j).symm⟩
  have hLift : IsOpenImmersion.lift (secondStageChart (k := k) (j + 1))
      (successorCurveSucc j) hr = oldCurveChartMorphism :=
    (IsOpenImmersion.lift_uniq (secondStageChart (j + 1)) (successorCurveSucc j) hr
      oldCurveChartMorphism (successorCurveSucc_eq j).symm).symm
  simpa only [hLift] using
    IsOpenImmersion.isPullback_lift_id (successorCurveSucc j) (secondStageChart (j + 1)) hr

/-- The strict transform's kernel ideal sheaf is the kernel of its second-chart axis. -/
theorem oldExceptionalStrictι_ker (j : ℕ) :
    (oldExceptionalStrictι (k := k) j).ker = (successorCurveSucc (k := k) j).ker :=
  (Scheme.IdealSheafData.ker_gluedTo (previousStrictIdeal (previousStage (k := k) j))).trans
    (previousStrictIdeal_eq (previousStage j))

/-- The ideal of the strict transform on the second Rees chart, in the actual chart coordinates. -/
def oldStrictSecondChartIdeal (j : ℕ) : Ideal (reesVChartRing k) :=
  Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv.hom
    (Ideal.comap ((secondStageChart (k := k) (j + 1)).appIso ⊤).inv.hom
      ((oldExceptionalStrictι (k := k) j).ker.ideal (secondAffineOpen (j + 1))))

private theorem oldCurveChart_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
        (oldCurveChartMorphism (k := k)).appTop).hom) =
      Ideal.span {oldRatio} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).symm.commRingCatIsoToRingEquiv.injective
  rw [oldCurveChartMorphism, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom, oldCurveMap_ker]

/-- On the second Rees chart the strict transform is exactly the axis `u/v = 0`. -/
theorem oldStrictSecondChartIdeal_eq_span (j : ℕ) :
    oldStrictSecondChartIdeal (k := k) j = Ideal.span {oldRatio} := by
  unfold oldStrictSecondChartIdeal secondAffineOpen
  rw [oldExceptionalStrictι_ker, ← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (successorCurveSucc (k := k) j) oldCurveChartMorphism (𝟙 _) (secondStageChart (j + 1))
    (successorCurveSucc_secondChart_isPullback j)
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
    (oldCurveChartMorphism (k := k)).appTop).hom) = _
  exact oldCurveChart_coordinateKernel

/-- The pullback-ideal identity on the second Rees chart: the ideal of `E_j` (on the first
chart of stage `j+1`) pulls back to the ideal of `E_{j+1}` times the ideal of the strict
transform of `E_j`, in the actual chart coordinates. -/
theorem oldStrict_secondChart_totalIdeal_factorization (j : ℕ) :
    Ideal.map (chartBaseMap (centerIdeal (k := k)) centerV)
        (stepExceptionalFirstChartIdeal (k := k) j) =
      stepExceptionalSecondChartIdeal (k := k) (j + 1) * oldStrictSecondChartIdeal j := by
  rw [stepExceptionalFirstChartIdeal_eq_span, stepExceptionalSecondChartIdeal_eq_span,
    oldStrictSecondChartIdeal_eq_span, Ideal.map_span, Set.image_singleton,
    ← vEquation_mul_oldRatio, Ideal.span_singleton_mul_span_singleton]

/-- The strict transform is absent from the first Rees chart of stage `j+2`. -/
theorem oldStrict_firstChart_isEmpty (j : ℕ) :
    IsEmpty ((oldExceptionalStrictι (k := k) j) ⁻¹ᵁ (firstAffineOpen (k := k) (j + 1 + 1)).1) := by
  refine ⟨fun z => ?_⟩
  have hz : (oldExceptionalStrictι (k := k) j).base z.1 ∈
      (((projectiveProductInitial (k := k)).stage (j + 1 + 1)).chart ''ᵁ ⊤) := z.2
  rw [Scheme.Hom.image_top_eq_opensRange] at hz
  exact previousStrict_avoids_nextChart (previousStage (k := k) j) z.1 hz

/-- On the first Rees chart the pullback of the ideal of `E_j` is the ideal of `E_{j+1}`. -/
theorem oldStrict_firstChart_totalIdeal (j : ℕ) :
    Ideal.map (firstStepSectionMap (k := k)) (stepExceptionalFirstChartIdeal (k := k) j) =
      stepExceptionalFirstChartIdeal (k := k) (j + 1) := by
  rw [stepExceptionalFirstChartIdeal_eq_span, stepExceptionalFirstChartIdeal_eq_span,
    Ideal.map_span, Set.image_singleton, firstStepSectionMap_eq, chartSubstitution_u]

end KltDP.Examples.FrobeniusOldExceptionalChartIdeals
