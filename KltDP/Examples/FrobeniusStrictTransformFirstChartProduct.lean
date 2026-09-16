import KltDP.Examples.FrobeniusStrictTransformProductKernel
import KltDP.Examples.FrobeniusGraphPicardClassContactIdeal
import KltDP.Examples.FrobeniusExceptionalSuccessorChart

/-!
# The original one-step ideal product on the first whole-stage chart

The original exceptional quotient chart, affine center fiber and global center
fiber give a pullback square over the literal first chart of the successor stage.
Its original global kernel therefore has exactly the exceptional coordinate ideal.

The original one-step blowdown induces the existing substitution on actual chart
sections. The actual previous strict ideal consequently pulls back to the product
of the actual global exceptional and successor strict ideals on this chart.
No ideal equality, fiber model or factorization is supplied as an input premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusStrictTransformFirstChartProduct

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalStrictTransform FrobeniusExceptionalCharts
open FrobeniusExceptionalSuccessorChart FrobeniusGraphPicardClassContactIdeal
open FrobeniusStrictTransformProductKernel

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance firstProductOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The original quotient chart of the exceptional coordinate in the polynomial plane. -/
def firstExceptionalPlaneInclusion : Spec (CommRingCat.of (Polynomial k)) ⟶ plane k :=
  Spec.map (CommRingCat.ofHom exceptionalPlaneEvaluation)

instance firstExceptionalPlaneInclusion_isClosedImmersion :
    IsClosedImmersion (firstExceptionalPlaneInclusion (k := k)) :=
  IsClosedImmersion.spec_of_surjective _ exceptionalPlaneEvaluation_surjective

/-- The same original quotient chart maps into the literal global center fiber. -/
def firstExceptionalToGlobal (n : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶
      PointBlowupGluing.globalCenterFiber
        ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
        ((projectiveProductInitial (k := k)).stage n).center_closed :=
  (uExceptionalIso (k := k)).inv ≫ exceptionalChartToFiber (centerIdeal (k := k)) centerU ≫
    (PointBlowupGluing.affineCenterFiberIso
      ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
      ((projectiveProductInitial (k := k)).stage n).center_closed).hom

private theorem affineCenterFiber_global_isPullback (n : ℕ) :
    IsPullback (centerFiberι (centerIdeal (k := k)))
      (PointBlowupGluing.affineCenterFiberIso
        ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
        ((projectiveProductInitial (k := k)).stage n).center_closed).hom
      (((projectiveProductInitial (k := k)).stage n).nextAffineBlowup)
      (stepExceptionalInclusion n) := by
  refine (PointBlowupGluing.exceptionalGlobalFiber_isPullback
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed).of_iso
      (exceptionalFiberIso (centerIdeal (k := k))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, exceptionalFiberIso_hom_ι]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id,
      PointBlowupGluing.exceptionalGlobalFiberIso, Iso.trans_hom]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The original first exceptional parameterization is an actual change of chart. -/
private theorem firstExceptionalPlane_isPullback :
    IsPullback (firstExceptionalPlaneInclusion (k := k)) (uExceptionalIso (k := k)).inv
      (coordinateChartIso (k := k)).hom (exceptionalChartInclusion (centerIdeal (k := k)) centerU) :=
  IsPullback.of_vert_isIso ⟨(uExceptionalIso_inv_inclusion (k := k)).symm⟩

/-- Pasting the three original squares identifies the literal first-chart fiber restriction. -/
theorem firstExceptionalGlobal_isPullback (n : ℕ) :
    IsPullback (firstExceptionalPlaneInclusion (k := k)) (firstExceptionalToGlobal n)
      (((projectiveProductInitial (k := k)).stage (n + 1)).chart)
      (stepExceptionalInclusion n) := by
  have h := (firstExceptionalPlane_isPullback (k := k)).paste_vert
    ((exceptionalChartToFiber_isPullback (centerIdeal (k := k)) centerU).paste_vert
      (affineCenterFiber_global_isPullback n))
  simpa only [firstExceptionalToGlobal, PlaneChartedScheme.stage,
    PlaneChartedScheme.next, PlaneChartedScheme.nextChart, coordinateChart,
    Category.assoc] using h

/-- The literal whole-stage exceptional kernel in the original first-chart coordinates. -/
def stepExceptionalFirstChartIdeal (n : ℕ) : Ideal (planeRing k) :=
  (((stepExceptionalInclusion (k := k) n).ker.ideal
    ⟨((projectiveProductInitial (k := k)).stage (n + 1)).chart ''ᵁ ⊤,
      (isAffineOpen_top (plane k)).image_of_isOpenImmersion _⟩).comap
        ((((projectiveProductInitial (k := k)).stage (n + 1)).chart.appIso ⊤).inv.hom)).comap
          (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom

private theorem firstExceptionalPlane_coordinateKernel :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
      (firstExceptionalPlaneInclusion (k := k)).appTop).hom) = Ideal.span {uCoord} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).symm.commRingCatIsoToRingEquiv.injective
  rw [firstExceptionalPlaneInclusion, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hΓ,
    CommRingCat.hom_ofHom, exceptionalPlaneEvaluation_ker]

/-- The actual global center-fiber kernel, not only the affine model, has equation `u`. -/
theorem stepExceptionalFirstChartIdeal_eq_span (n : ℕ) :
    stepExceptionalFirstChartIdeal (k := k) n = Ideal.span {uCoord} := by
  unfold stepExceptionalFirstChartIdeal
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (stepExceptionalInclusion (k := k) n) firstExceptionalPlaneInclusion
    (firstExceptionalToGlobal n) (((projectiveProductInitial (k := k)).stage (n + 1)).chart)
    (firstExceptionalGlobal_isPullback n) ⟨⊤, isAffineOpen_top (plane k)⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv ≫
    (firstExceptionalPlaneInclusion (k := k)).appTop).hom) = _
  exact firstExceptionalPlane_coordinateKernel

/-- The previously computed Rees ideal is exactly the restriction of the original global kernel. -/
theorem stepExceptionalFirstChartIdeal_eq_rees (n : ℕ) :
    stepExceptionalFirstChartIdeal (k := k) n = exceptionalChartIdeal := by
  rw [stepExceptionalFirstChartIdeal_eq_span, exceptionalChartIdeal_eq_span]

/-- The literal first chart and actual one-step projection retain the original substitution. -/
@[reassoc] theorem firstStageChart_projection (n : ℕ) :
    ((projectiveProductInitial (k := k)).stage (n + 1)).chart ≫
        (projectiveProductInitial (k := k)).stepProjection n =
      Spec.map (CommRingCat.ofHom chartSubstitution) ≫
        ((projectiveProductInitial (k := k)).stage n).chart := by
  change ((projectiveProductInitial (k := k)).stage n).nextChart ≫
    ((projectiveProductInitial (k := k)).stage n).nextProjection = _
  rw [PlaneChartedScheme.nextChart_projection, coordinateBlowdown_eq]

/-- The actual one-step morphism's map on chart sections, through the two original Gamma-Spec maps. -/
def firstStepSectionMap : planeRing k →+* planeRing k :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).hom.hom.comp
    ((coordinateBlowdown (k := k)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom)

theorem firstStepSectionMap_eq : firstStepSectionMap (k := k) = chartSubstitution := by
  apply RingHom.ext
  intro r
  change (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).hom
    ((coordinateBlowdown (k := k)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv r)) = _
  rw [coordinateBlowdown_eq]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartSubstitution (k := k)))) r
  change (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv (chartSubstitution r) =
    (Spec.map (CommRingCat.ofHom (chartSubstitution (k := k)))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv r) at h
  rw [← h]
  exact Iso.inv_hom_id_apply _ _

/-- The original one-step equation removes exactly one exceptional factor, including `m=0`. -/
theorem firstStepEquation_factorization (m : ℕ) :
    firstStepSectionMap (k := k) (vCoord - uCoord ^ (m + 1)) =
      uCoord * (vCoord - uCoord ^ m) := by
  have hs : stageSubstitution (k := k) 1 = chartSubstitution := by
    simpa only [stageSubstitution_zero, RingHom.comp_id] using
      stageSubstitution_succ (k := k) 0
  simpa only [firstStepSectionMap_eq, hs, pow_one] using
    stageTotalEquation_factorization (k := k) 1 m

/-- On the literal first whole-stage chart, pullback of the actual previous strict ideal
equals the product of the actual global exceptional kernel and actual successor strict ideal. -/
theorem strictFirstChart_totalIdeal_factorization (n m : ℕ) :
    Ideal.map (firstStepSectionMap (k := k)) (strictChartIdeal n (m + 1)) =
      stepExceptionalFirstChartIdeal n * strictChartIdeal (n + 1) m := by
  rw [strictChartIdeal_eq_span, strictChartIdeal_eq_span,
    stepExceptionalFirstChartIdeal_eq_span, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_mul_span_singleton, firstStepEquation_factorization]

end KltDP.Examples.FrobeniusStrictTransformFirstChartProduct
