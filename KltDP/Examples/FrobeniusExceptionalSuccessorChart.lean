import KltDP.Examples.FrobeniusExceptionalCharts
import KltDP.Examples.FrobeniusBlowupChartIteration
import KltDP.Examples.FrobeniusBlowupIncidence
import KltDP.Geometry.AffineBlowupExceptionalIntersection

/-!
# The strict transform of the old coordinate exceptional curve

In the actual second Rees chart of the origin blowup, write `v` for the
pulled base coordinate and `r=u/v` for the chart fraction. The old curve
`u=0` has strict-transform ideal `(r)`. Its parameter map sends `v` to
the polynomial parameter and `r` to zero. The full base ring map is the
original evaluation `u=0, v=t`.

The curve lies outside the first Rees chart. At parameter zero its
intersection with the new exceptional equation has length one in the
actual curve stalk. These are local statements about the original Rees
scheme; the comparison with a global previous exceptional curve is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalSuccessorChart

open KltDP.Geometry.AffineBlowup FrobeniusBlowupContact FrobeniusBlowupSmooth
  FrobeniusExceptionalCharts FrobeniusBlowupIncidence FrobeniusGraphContact

variable {k : Type u} [Field k]

/-- The original base coordinate `v` on the actual second Rees chart. -/
def vEquation : reesVChartRing k := chartBaseMap centerIdeal centerV vCoord

/-- The actual homogeneous chart fraction `u/v`. -/
def oldRatio : reesVChartRing k := chartFraction centerIdeal centerV centerU

theorem vEquation_mul_oldRatio :
    vEquation (k := k) * oldRatio = chartBaseMap centerIdeal centerV uCoord :=
  chartBaseMap_mul_chartFraction centerIdeal centerV centerU

/-- The old coordinate curve is evaluated through the proved second-chart equivalence. -/
def oldCurveMap : reesVChartRing k →+* Polynomial k :=
  (Polynomial.evalRingHom 0).comp (vChartPolynomialEquiv (k := k)).toRingHom

@[simp] theorem oldCurveMap_vEquation :
    oldCurveMap (vEquation (k := k)) = Polynomial.X := by
  change Polynomial.eval 0 (vChartPolynomialEquiv
    (chartBaseMap centerIdeal centerV (centerV (k := k) : planeRing k))) = Polynomial.X
  rw [vChart_selected_equation]
  simp [uCoord]

@[simp] theorem oldCurveMap_oldRatio : oldCurveMap (oldRatio (k := k)) = 0 := by
  change Polynomial.eval 0 (vChartPolynomialEquiv
    (chartFraction centerIdeal (centerV (k := k)) centerU)) = 0
  rw [vChartPolynomialEquiv_coordinate]
  simp [vCoord]

@[simp] theorem oldCurveMap_constants (r : k) :
    oldCurveMap (chartConstants (centerV (k := k)) r) = Polynomial.C r := by
  change Polynomial.eval 0 (vChartPolynomialEquiv (chartConstants centerV r)) = Polynomial.C r
  rw [vChartPolynomialEquiv_constants]
  simp [planeConstants]

@[simp] theorem oldCurveMap_base_u :
    oldCurveMap (chartBaseMap centerIdeal (centerV (k := k)) uCoord) = 0 := by
  rw [← vEquation_mul_oldRatio, map_mul, oldCurveMap_oldRatio, mul_zero]

/-- Equality of the entire original base ring maps, including arbitrary coefficients. -/
theorem oldCurveMap_baseMap :
    (oldCurveMap (k := k)).comp (chartBaseMap centerIdeal centerV) =
      exceptionalPlaneEvaluation := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro r
      change oldCurveMap (chartConstants centerV r) = exceptionalPlaneEvaluation (planeConstants r)
      rw [oldCurveMap_constants, exceptionalPlaneEvaluation_constants]
    · change oldCurveMap (chartBaseMap centerIdeal centerV (uCoord (k := k))) =
        exceptionalPlaneEvaluation uCoord
      rw [oldCurveMap_base_u, exceptionalPlaneEvaluation_u]
  · change oldCurveMap (vEquation (k := k)) = exceptionalPlaneEvaluation vCoord
    rw [oldCurveMap_vEquation, exceptionalPlaneEvaluation_v]

/-- The parameter map has exactly the actual principal old-curve ideal as kernel. -/
theorem oldCurveMap_ker :
    RingHom.ker (oldCurveMap (k := k)) = Ideal.span {oldRatio} := by
  have hmap : Ideal.map (vChartPolynomialEquiv (k := k)).toRingHom
      (Ideal.span {oldRatio (k := k)}) = Ideal.span {Polynomial.X} := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : planeRing k => Ideal.span {z})
      (vChartPolynomialEquiv_coordinate (k := k))
  rw [oldCurveMap, ← RingHom.comap_ker, Polynomial.ker_evalRingHom,
    Polynomial.C_0, sub_zero, ← hmap]
  exact Ideal.comap_map_of_bijective (vChartPolynomialEquiv (k := k)).toRingHom
    (vChartPolynomialEquiv (k := k)).bijective

theorem oldCurveMap_surjective : Function.Surjective (oldCurveMap (k := k)) := by
  intro p
  refine ⟨(vChartPolynomialEquiv (k := k)).symm (Polynomial.C p), ?_⟩
  simp [oldCurveMap]

/-- Removing every power of the new exceptional equation gives the old-curve ideal. -/
theorem saturation_baseU_iff (s : reesVChartRing k) :
    (∃ j : ℕ, vEquation (k := k) ^ j * s ∈
      Ideal.span {chartBaseMap (centerIdeal (k := k)) centerV uCoord}) ↔
        s ∈ Ideal.span {oldRatio} := by
  constructor
  · rintro ⟨j, hj⟩
    rw [← oldCurveMap_ker, RingHom.mem_ker]
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hj
    have h : (Polynomial.X : Polynomial k) ^ j * oldCurveMap s = 0 := by
      simpa only [map_mul, map_pow, oldCurveMap_vEquation, oldCurveMap_base_u,
        zero_mul] using congrArg (oldCurveMap (k := k)) hg
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero j Polynomial.X_ne_zero)
  · intro hs
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hs
    refine ⟨1, Ideal.mem_span_singleton.mpr ⟨g, ?_⟩⟩
    rw [pow_one, hg, ← vEquation_mul_oldRatio, mul_assoc]

theorem saturation_baseU_iff_mem_ker (s : reesVChartRing k) :
    (∃ j : ℕ, vEquation (k := k) ^ j * s ∈
      Ideal.span {chartBaseMap (centerIdeal (k := k)) centerV uCoord}) ↔
        s ∈ RingHom.ker oldCurveMap := by
  rw [oldCurveMap_ker]
  exact saturation_baseU_iff s

/-- The closed old curve in the actual second chart. -/
def oldCurveChartMorphism : Spec (CommRingCat.of (Polynomial k)) ⟶
    Spec (CommRingCat.of (reesVChartRing k)) :=
  Spec.map (CommRingCat.ofHom oldCurveMap)

instance oldCurveChartMorphism_isClosedImmersion :
    IsClosedImmersion (oldCurveChartMorphism (k := k)) :=
  IsClosedImmersion.spec_of_surjective _ oldCurveMap_surjective

/-- The original old-curve map into the whole actual Rees blowup. -/
def oldCurveMorphism :
    Spec (CommRingCat.of (Polynomial k)) ⟶ scheme (centerIdeal (k := k)) :=
  oldCurveChartMorphism ≫ chartι centerIdeal centerV

theorem oldCurveChartMorphism_toSpec :
    oldCurveChartMorphism (k := k) ≫
      Spec.map (CommRingCat.ofHom (chartBaseMap centerIdeal centerV)) =
        Spec.map (CommRingCat.ofHom exceptionalPlaneEvaluation) := by
  rw [oldCurveChartMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    oldCurveMap_baseMap]

theorem oldCurveMorphism_toSpec :
    oldCurveMorphism (k := k) ≫ toSpec centerIdeal =
      Spec.map (CommRingCat.ofHom exceptionalPlaneEvaluation) := by
  rw [oldCurveMorphism, Category.assoc, chartι_toSpec]
  exact oldCurveChartMorphism_toSpec

/-- The original first exceptional quotient chart has its stated plane parameterization. -/
theorem uExceptionalIso_inv_inclusion :
    (uExceptionalIso (k := k)).inv ≫ exceptionalChartInclusion centerIdeal centerU =
      Spec.map (CommRingCat.ofHom exceptionalPlaneEvaluation) ≫
        (FrobeniusBlowupChartIteration.coordinateChartIso (k := k)).hom := by
  change Spec.map (CommRingCat.ofHom (uExceptionalEquiv (k := k)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (chartCenterIdeal (centerIdeal (k := k)) centerU))) =
    Spec.map (CommRingCat.ofHom (exceptionalPlaneEvaluation (k := k))) ≫
      Spec.map (CommRingCat.ofHom (chartPolynomialEquiv (k := k)).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun g : reesChartRing k →+* Polynomial k =>
    Spec.map (CommRingCat.ofHom g))
  apply RingHom.ext
  intro x
  exact exceptionalChartPolynomialEquiv_mk (centerU (k := k))
    (chartPolynomialEquiv (k := k)) (uChart_selected_equation (k := k)) x

theorem oldRatio_mem_image_prime (q : Spec (CommRingCat.of (Polynomial k))) :
    oldRatio ∈ ((oldCurveChartMorphism (k := k)).base q).asIdeal := by
  change oldCurveMap oldRatio ∈ q.asIdeal
  rw [oldCurveMap_oldRatio]
  exact q.asIdeal.zero_mem

/-- Every point of the actual old curve lies outside the first Rees chart. -/
theorem oldCurve_avoids_uChart (q : Spec (CommRingCat.of (Polynomial k))) :
    (oldCurveMorphism (k := k)).base q ∉ Set.range (chartι centerIdeal centerU).base := by
  intro h
  change (oldCurveChartMorphism (k := k)).base q ∈
    (chartι centerIdeal centerV).base ⁻¹' Set.range (chartι centerIdeal centerU).base at h
  rw [chart_preimage_chart_range] at h
  change oldRatio ∉ ((oldCurveChartMorphism (k := k)).base q).asIdeal at h
  exact h (oldRatio_mem_image_prime q)

/-- The original chart section pulled to the actual parameter curve stalk at zero. -/
def oldCurveIntersectionGerm (s : reesVChartRing k) : curveStalk k :=
  StructureSheaf.toStalk (Polynomial k) curvePoint (oldCurveMap s)

theorem oldCurveIntersectionGerm_pullback (s : reesVChartRing k) :
    (oldCurveChartMorphism (k := k)).stalkMap curvePoint
      (StructureSheaf.toStalk (reesVChartRing k)
        ((oldCurveChartMorphism (k := k)).base curvePoint) s) =
          oldCurveIntersectionGerm s :=
  AlgebraicGeometry.stalkMap_toStalk_apply
    (CommRingCat.ofHom (oldCurveMap (k := k))) (curvePoint (k := k)) s

theorem curveStalkLocalEquiv_oldCurveGerm (s : reesVChartRing k) :
    curveStalkLocalEquiv (oldCurveIntersectionGerm s) =
      algebraMap (Polynomial k) (parameterLocalRing (0 : k)) (oldCurveMap s) :=
  StructureSheaf.stalkToFiberRingHom_toStalk (Polynomial k) curvePoint (oldCurveMap s)

theorem curveStalkLocalEquiv_vEquation :
    curveStalkLocalEquiv (oldCurveIntersectionGerm (vEquation (k := k))) =
      localParameter (0 : k) := by
  rw [curveStalkLocalEquiv_oldCurveGerm, oldCurveMap_vEquation]
  simp [localParameter]

/-- The new exceptional equation cuts length one on the actual old-curve stalk. -/
theorem oldCurve_stalk_quotient_length :
    Module.length (curveStalk k)
      (curveStalk k ⧸ Ideal.span {oldCurveIntersectionGerm (vEquation (k := k))}) = 1 := by
  rw [FrobeniusGraphStalkContact.quotient_span_length_eq_of_ringEquiv curveStalkLocalEquiv,
    curveStalkLocalEquiv_vEquation]
  have h := KltDP.RingTheory.dvr_length_quotient_uniformizer_pow
    (parameterLocalRing (0 : k)) (localParameter 0) (localParameter_uniformizer 0) 1
  rw [pow_one] at h
  exact h

end KltDP.Examples.FrobeniusExceptionalSuccessorChart
