import KltDP.Examples.FrobeniusStrictTransformSecondChartAlgebra
import KltDP.Examples.FrobeniusStrictTransformAffineBlowup
import KltDP.Examples.FrobeniusGraphPicardClassContactIdeal
import KltDP.Geometry.SchematicImageOpenImmersion

/-!
# The original whole strict ideal on the original second Rees chart

The actual dense parameter map factors through the original second Rees
chart by the actual homogeneous overlap square. Restricting the integral
parameter source leaves the original schematic kernel unchanged. The
resulting actual pullback computes the original whole-stage strict ideal
through both canonical section-ring isomorphisms.

The final ideal factorization therefore uses the original previous-stage
strict ideal, the original second-chart blowdown and exceptional ideal,
and the original successor-stage strict ideal. Both stage and residual
exponents range over all natural numbers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformSecondChart

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformAffineBlowup FrobeniusStrictTransformSecondChartAlgebra
open FrobeniusGraphPicardClassContactIdeal

variable {k : Type u} [Field k]

local instance puncturedParameter_domain : IsDomain (puncturedParameterRing k) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (S := puncturedParameterRing k) (Polynomial k)
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)

local instance puncturedParameter_noetherian : IsNoetherianRing (puncturedParameterRing k) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial k))
    (puncturedParameterRing k) inferInstance

local instance puncturedParameter_noetherianSpace :
    NoetherianSpace (Spec (CommRingCat.of (puncturedParameterRing k))) :=
  inferInstanceAs (NoetherianSpace (PrimeSpectrum (puncturedParameterRing k)))

/-- The original dense principal-open parameter immersion. -/
def puncturedParameterι : Spec (CommRingCat.of (puncturedParameterRing k)) ⟶
    Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom puncturedParameterMap)

instance puncturedParameterι_isOpenImmersion :
    IsOpenImmersion (puncturedParameterι (k := k)) := by
  unfold puncturedParameterι puncturedParameterMap
  infer_instance

/-- The parameter map into the original second Rees chart. -/
def secondResidualMorphism (m : ℕ) :
    Spec (CommRingCat.of (puncturedParameterRing k)) ⟶
      Spec (CommRingCat.of (reesVChartRing k)) :=
  Spec.map (CommRingCat.ofHom (secondResidualMap m))

private theorem overlap_chartι :
    Spec.map (CommRingCat.ofHom
        (conormalOverlapLeft (centerIdeal (k := k)) centerU centerV)) ≫
        chartι (centerIdeal (k := k)) centerU =
      Spec.map (CommRingCat.ofHom
        (conormalOverlapRight (centerIdeal (k := k)) centerU centerV)) ≫
        chartι (centerIdeal (k := k)) centerV := by
  apply (cancel_epi (conormalOverlapIso (centerIdeal (k := k)) centerU centerV).hom).mp
  simp only [← Category.assoc, conormalOverlapIso_hom_left, conormalOverlapIso_hom_right]
  exact pullback.condition

/-- The actual overlap square identifies the two original parameter lifts. -/
@[reassoc] theorem secondResidualMorphism_chartι (m : ℕ) :
    secondResidualMorphism (k := k) m ≫ chartι (centerIdeal (k := k)) centerV =
      puncturedParameterι ≫ residualCurveMorphism m := by
  have hl : Spec.map (CommRingCat.ofHom (residualOverlapMap (k := k) m)) ≫
      Spec.map (CommRingCat.ofHom
        (conormalOverlapLeft (centerIdeal (k := k)) centerU centerV)) =
        puncturedParameterι ≫ residualCurveChartMorphism m := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residualOverlapMap_comp_left,
      CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  calc
    _ = Spec.map (CommRingCat.ofHom (residualOverlapMap (k := k) m)) ≫
        Spec.map (CommRingCat.ofHom
          (conormalOverlapRight (centerIdeal (k := k)) centerU centerV)) ≫
          chartι (centerIdeal (k := k)) centerV := by
      simp only [secondResidualMorphism, secondResidualMap, CommRingCat.ofHom_comp,
        Spec.map_comp, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (residualOverlapMap (k := k) m)) ≫
        Spec.map (CommRingCat.ofHom
          (conormalOverlapLeft (centerIdeal (k := k)) centerU centerV)) ≫
          chartι (centerIdeal (k := k)) centerU :=
      whisker_eq _ overlap_chartι.symm
    _ = (Spec.map (CommRingCat.ofHom (residualOverlapMap (k := k) m)) ≫
        Spec.map (CommRingCat.ofHom
          (conormalOverlapLeft (centerIdeal (k := k)) centerU centerV))) ≫
          chartι (centerIdeal (k := k)) centerU :=
      (Category.assoc _ _ _).symm
    _ = (puncturedParameterι ≫ residualCurveChartMorphism m) ≫
        chartι (centerIdeal (k := k)) centerU :=
      eq_whisker hl _
    _ = puncturedParameterι ≫ residualCurveChartMorphism m ≫
        chartι (centerIdeal (k := k)) centerU :=
      Category.assoc _ _ _
    _ = _ := rfl

/-- The original second Rees chart as an open of the entire successor stage. -/
def secondStageChart (n : ℕ) : Spec (CommRingCat.of (reesVChartRing k)) ⟶
    projectiveContactStage (k := k) (n + 1) :=
  chartι (centerIdeal (k := k)) centerV ≫
    ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup

instance secondStageChart_isOpenImmersion (n : ℕ) :
    IsOpenImmersion (secondStageChart (k := k) n) := by
  unfold secondStageChart
  infer_instance

/-- This chart's original one-step projection has the original base ring map. -/
@[reassoc] theorem secondStageChart_projection (n : ℕ) :
    secondStageChart (k := k) n ≫
        ((projectiveProductInitial (k := k)).stage n).nextProjection =
      Spec.map (CommRingCat.ofHom (chartBaseMap (centerIdeal (k := k)) centerV)) ≫
        ((projectiveProductInitial (k := k)).stage n).chart := by
  rw [secondStageChart, Category.assoc, PlaneChartedScheme.nextAffineBlowup_projection,
    ← Category.assoc, chartι_toSpec]
  rfl

/-- The same original residual lift restricted to the dense parameter open. -/
def denseResidualStage (n m : ℕ) : Spec (CommRingCat.of (puncturedParameterRing k)) ⟶
    projectiveContactStage (k := k) (n + 1) :=
  puncturedParameterι ≫ residualCurveMorphism m ≫
    ((projectiveProductInitial (k := k)).stage n).nextAffineBlowup

@[reassoc] theorem secondResidualMorphism_stageChart (n m : ℕ) :
    secondResidualMorphism (k := k) m ≫ secondStageChart n = denseResidualStage n m := by
  rw [secondStageChart, ← Category.assoc, secondResidualMorphism_chartι,
    Category.assoc]
  rfl

/-- This is exactly the kernel defining the original whole-projective strict transform. -/
theorem denseResidualStage_ker (n m : ℕ) :
    (denseResidualStage (k := k) n m).ker =
      strictTransformIdeal (n + 1) (m + (n + 1)) := by
  rw [denseResidualStage, SchematicImageOpenImmersion.ker_precompose_openImmersion,
    strictTransformIdeal_succ_eq]

/-- The actual dense lift and original second chart form a scheme pullback. -/
theorem denseResidualStage_secondChart_isPullback (n m : ℕ) :
    IsPullback (secondResidualMorphism (k := k) m) (𝟙 _)
      (secondStageChart n) (denseResidualStage n m) := by
  have hr : Set.range (denseResidualStage (k := k) n m).base ⊆
      Set.range (secondStageChart n).base := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(secondResidualMorphism m).base t,
      congrArg (fun f => f.base t) (secondResidualMorphism_stageChart n m)⟩
  have hLift : IsOpenImmersion.lift (secondStageChart (k := k) n)
      (denseResidualStage n m) hr = secondResidualMorphism m :=
    (IsOpenImmersion.lift_uniq (secondStageChart n) (denseResidualStage n m) hr
      (secondResidualMorphism m) (secondResidualMorphism_stageChart n m)).symm
  simpa only [hLift] using
    IsOpenImmersion.isPullback_lift_id (denseResidualStage n m) (secondStageChart n) hr

/-- The original global strict ideal expressed through the original second-chart sections. -/
def strictSecondChartIdeal (n m : ℕ) : Ideal (reesVChartRing k) :=
  Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv.hom
    (Ideal.comap ((secondStageChart n).appIso ⊤).inv.hom
      ((strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal
        ⟨secondStageChart n ''ᵁ ⊤,
          (isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))).image_of_isOpenImmersion _⟩))

private theorem secondResidualMorphism_coordinateKernel (m : ℕ) :
    RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
        (secondResidualMorphism (k := k) m).appTop).hom) =
      Ideal.span {secondResidualEquation m} := by
  have hΓ : Function.Injective
      ((Scheme.ΓSpecIso (CommRingCat.of (puncturedParameterRing k))).inv.hom) :=
    (Scheme.ΓSpecIso
      (CommRingCat.of (puncturedParameterRing k))).symm.commRingCatIsoToRingEquiv.injective
  rw [secondResidualMorphism, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _ hΓ, CommRingCat.hom_ofHom, secondResidualMap_ker]

/-- The original whole strict ideal has this exact equation on its original second chart. -/
theorem strictSecondChartIdeal_eq_span (n m : ℕ) :
    strictSecondChartIdeal (k := k) n m = Ideal.span {secondResidualEquation m} := by
  unfold strictSecondChartIdeal
  rw [← denseResidualStage_ker]
  rw [← Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (denseResidualStage (k := k) n m) (secondResidualMorphism m) (𝟙 _)
    (secondStageChart n) (denseResidualStage_secondChart_isPullback n m)
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of (reesVChartRing k)))⟩,
    Scheme.Hom.ker_apply]
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (reesVChartRing k))).inv ≫
    (secondResidualMorphism m).appTop).hom) = _
  exact secondResidualMorphism_coordinateKernel m

/-- The actual previous strict ideal pulls back to exceptional times actual successor strict
ideal, through the original second-chart blowdown and both original chart identifications. -/
theorem strictSecondChart_totalIdeal_factorization (n m : ℕ) :
    Ideal.map (chartBaseMap (centerIdeal (k := k)) centerV)
        (strictChartIdeal (k := k) n (m + 1)) =
      chartCenterIdeal (centerIdeal (k := k)) centerV * strictSecondChartIdeal n m := by
  rw [strictChartIdeal_eq_span, strictSecondChartIdeal_eq_span, ← secondResidualMap_ker]
  exact secondTotalIdeal_factorization m

end KltDP.Examples.FrobeniusStrictTransformSecondChart
