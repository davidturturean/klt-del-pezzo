import KltDP.Geometry.AffineBlowupLift
import KltDP.Geometry.AffineBlowupChartCenter
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# One actual blowup chart and the decrease of monomial contact

The source plane is `k[u][v]`, with center `(u,v)`. The actual Rees chart
at `uT` is proved isomorphic to `k[u][w]`: the base coordinate `v` maps to
`u*w`, and the actual chart fraction `v/u` maps to `w`.

The curve `v=u^(m+1)` lifts to a closed immersion of the affine line into
this chart. Its kernel is the principal ideal `(w-u^m)`. Saturation of the
actual total-transform equation by powers of the exceptional coordinate is
proved to give exactly this ideal. Thus the residual curve is characterized
by actual ring maps and ideals, not by an assumed strict-transform formula.

Reuse: the existing Rees chart lift, its uniqueness, and its regular center
equation; pinned polynomial evaluation and its kernel. This is one chart
and one blowup, valid for every natural `m`, not an iterated global surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusBlowupContact

open KltDP.Geometry.AffineBlowup

variable {k : Type u} [Field k]

/-- The actual affine-plane coordinate ring, with outer variable `v`. -/
abbrev planeRing (k : Type u) [Field k] := Polynomial (Polynomial k)

def uCoord : planeRing k := Polynomial.C Polynomial.X
def vCoord : planeRing k := Polynomial.X

theorem uCoord_ne_zero : uCoord (k := k) ≠ 0 :=
  Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero

def centerIdeal : Ideal (planeRing k) := Ideal.span {uCoord, vCoord}

def centerU : centerIdeal (k := k) :=
  ⟨uCoord, Ideal.subset_span (by simp)⟩

def centerV : centerIdeal (k := k) :=
  ⟨vCoord, Ideal.subset_span (by simp)⟩

/-- The actual degree-zero Rees chart ring, not a polynomial replacement. -/
abbrev reesChartRing (k : Type u) [Field k] :=
  chartRing (centerIdeal (k := k)) centerU

abbrev baseMap : planeRing k →+* reesChartRing k := chartBaseMap centerIdeal centerU

def chartU : reesChartRing k := baseMap uCoord
def chartW : reesChartRing k := chartFraction centerIdeal centerU centerV

theorem chartU_mul_chartW : chartU (k := k) * chartW = baseMap vCoord :=
  chartBaseMap_mul_chartFraction centerIdeal centerU centerV

/-- On a polynomial model of the chart, the original coordinate `v` becomes `u*w`. -/
def chartSubstitution : planeRing k →+* planeRing k :=
  Polynomial.eval₂RingHom Polynomial.C (uCoord * vCoord)

@[simp] theorem chartSubstitution_C (r : Polynomial k) :
    chartSubstitution (Polynomial.C r) = Polynomial.C r := by
  simp [chartSubstitution]

@[simp] theorem chartSubstitution_u : chartSubstitution (uCoord (k := k)) = uCoord :=
  chartSubstitution_C Polynomial.X

@[simp] theorem chartSubstitution_v :
    chartSubstitution (vCoord (k := k)) = uCoord * vCoord := by
  simp [chartSubstitution, vCoord]

theorem chartSubstitution_regular :
    chartSubstitution (centerU (k := k) : planeRing k) ∈ nonZeroDivisors (planeRing k) := by
  change chartSubstitution (uCoord (k := k)) ∈ nonZeroDivisors (planeRing k)
  rw [chartSubstitution_u]
  exact mem_nonZeroDivisors_of_ne_zero uCoord_ne_zero

theorem chartSubstitution_center :
    Ideal.map chartSubstitution (centerIdeal (k := k)) ≤
      Ideal.span {chartSubstitution (centerU (k := k) : planeRing k)} := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  intro r hr
  change r = uCoord (k := k) ∨ r = vCoord (k := k) at hr
  rcases hr with rfl | rfl
  · change chartSubstitution (uCoord (k := k)) ∈
      Ideal.span {chartSubstitution (uCoord (k := k))}
    exact Ideal.subset_span (Set.mem_singleton _)
  · change chartSubstitution (vCoord (k := k)) ∈
      Ideal.span {chartSubstitution (uCoord (k := k))}
    rw [chartSubstitution_v, chartSubstitution_u]
    exact Ideal.mem_span_singleton.mpr ⟨vCoord, rfl⟩

/-- The canonical map from the actual Rees chart to the polynomial model. -/
def chartToPolynomial : reesChartRing k →+* planeRing k :=
  chartLift centerIdeal centerU chartSubstitution
    chartSubstitution_regular chartSubstitution_center

@[simp] theorem chartToPolynomial_baseMap (r : planeRing k) :
    chartToPolynomial (baseMap r) = chartSubstitution r :=
  chartLift_baseMap centerIdeal centerU chartSubstitution
    chartSubstitution_regular chartSubstitution_center r

@[simp] theorem chartToPolynomial_u : chartToPolynomial (chartU (k := k)) = uCoord := by
  simp [chartU]

@[simp] theorem chartToPolynomial_w : chartToPolynomial (chartW (k := k)) = vCoord := by
  have h := congrArg (chartToPolynomial (k := k)) chartU_mul_chartW
  simp only [map_mul, chartToPolynomial_u, chartToPolynomial_baseMap,
    chartSubstitution_v] at h
  exact mul_left_cancel₀ uCoord_ne_zero h

/-- Polynomial evaluation at the actual base coordinate and actual chart fraction. -/
def polynomialToChart : planeRing k →+* reesChartRing k :=
  Polynomial.eval₂RingHom (baseMap.comp Polynomial.C) chartW

@[simp] theorem polynomialToChart_C (r : Polynomial k) :
    polynomialToChart (Polynomial.C r) = baseMap (Polynomial.C r) := by
  simp [polynomialToChart]

@[simp] theorem polynomialToChart_u :
    polynomialToChart (uCoord (k := k)) = chartU :=
  polynomialToChart_C Polynomial.X

@[simp] theorem polynomialToChart_v :
    polynomialToChart (vCoord (k := k)) = chartW := by
  simp [polynomialToChart, vCoord]

theorem polynomialToChart_comp_substitution :
    (polynomialToChart (k := k)).comp chartSubstitution = baseMap := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, chartSubstitution_C, polynomialToChart_C]
  · change polynomialToChart (chartSubstitution (vCoord (k := k))) = baseMap vCoord
    rw [chartSubstitution_v, map_mul, polynomialToChart_u, polynomialToChart_v,
      chartU_mul_chartW]

theorem chartToPolynomial_comp_polynomialToChart :
    (chartToPolynomial (k := k)).comp polynomialToChart = RingHom.id (planeRing k) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polynomialToChart_C, chartToPolynomial_baseMap,
      chartSubstitution_C, RingHom.id_apply]
  · change chartToPolynomial (polynomialToChart (vCoord (k := k))) = vCoord
    rw [polynomialToChart_v, chartToPolynomial_w]

/-- The reverse composite is forced by the proved universal property of the actual Rees chart. -/
theorem polynomialToChart_comp_chartToPolynomial :
    (polynomialToChart (k := k)).comp chartToPolynomial = RingHom.id (reesChartRing k) := by
  have hreg : baseMap (centerU (k := k) : planeRing k) ∈ nonZeroDivisors (reesChartRing k) :=
    chartBaseMap_equation_mem_nonZeroDivisors (centerIdeal (k := k)) centerU
  have hI : Ideal.map baseMap (centerIdeal (k := k)) ≤
      Ideal.span {baseMap (centerU (k := k) : planeRing k)} :=
    (map_chartBaseMap_ideal (centerIdeal (k := k)) centerU).le
  have hcomp : ((polynomialToChart (k := k)).comp chartToPolynomial).comp baseMap =
      baseMap := by
    apply RingHom.ext
    intro r
    simpa only [RingHom.comp_apply, chartToPolynomial_baseMap] using
      RingHom.congr_fun (polynomialToChart_comp_substitution (k := k)) r
  exact (chartLift_unique centerIdeal centerU baseMap hreg hI
    (polynomialToChart.comp chartToPolynomial) hcomp).trans
      (chartLift_unique centerIdeal centerU baseMap hreg hI
        (RingHom.id (reesChartRing k)) (RingHom.id_comp _)).symm

/-- The actual Rees chart is the ordinary polynomial plane with coordinates `u,w`. -/
def chartPolynomialEquiv : reesChartRing k ≃+* planeRing k where
  __ := chartToPolynomial
  invFun := polynomialToChart
  left_inv x := RingHom.congr_fun polynomialToChart_comp_chartToPolynomial x
  right_inv x := RingHom.congr_fun chartToPolynomial_comp_polynomialToChart x

@[simp] theorem chartPolynomialEquiv_u :
    chartPolynomialEquiv (chartU (k := k)) = uCoord := chartToPolynomial_u

@[simp] theorem chartPolynomialEquiv_w :
    chartPolynomialEquiv (chartW (k := k)) = vCoord := chartToPolynomial_w

/-- The residual equation after one blowup of contact order `m+1`. -/
def residualEquation (m : ℕ) : reesChartRing k :=
  chartW (k := k) - chartU (k := k) ^ m

/-- The total transform of the original curve equation under the actual base map. -/
def totalEquation (m : ℕ) : reesChartRing k :=
  baseMap (vCoord (k := k) - uCoord (k := k) ^ (m + 1))

theorem totalEquation_factorization (m : ℕ) :
    totalEquation (k := k) m = chartU * residualEquation m := by
  simp only [totalEquation, map_sub, map_pow, residualEquation, ← chartU_mul_chartW]
  change chartU (k := k) * chartW - chartU (k := k) ^ (m + 1) =
    chartU (k := k) * (chartW - chartU (k := k) ^ m)
  rw [pow_succ']
  ring

/-- The actual map from the Rees chart to the parameter ring of the residual curve. -/
def residualCurveMap (m : ℕ) : reesChartRing k →+* Polynomial k :=
  (Polynomial.evalRingHom ((Polynomial.X : Polynomial k) ^ m)).comp
    (chartPolynomialEquiv (k := k)).toRingHom

@[simp] theorem residualCurveMap_u (m : ℕ) :
    residualCurveMap m (chartU (k := k)) = Polynomial.X := by
  simp [residualCurveMap, uCoord]

@[simp] theorem residualCurveMap_w (m : ℕ) :
    residualCurveMap m (chartW (k := k)) = Polynomial.X ^ m := by
  simp [residualCurveMap, vCoord]

theorem residualCurveMap_baseMap (m : ℕ) :
    (residualCurveMap (k := k) m).comp baseMap =
      Polynomial.evalRingHom (Polynomial.X ^ (m + 1)) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [residualCurveMap, RingHom.comp_apply, chartPolynomialEquiv]
  · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
    change residualCurveMap (k := k) m (baseMap vCoord) =
      (Polynomial.X : Polynomial k) ^ (m + 1)
    rw [← chartU_mul_chartW, map_mul, residualCurveMap_u, residualCurveMap_w, pow_succ']

theorem chartPolynomialEquiv_residualEquation (m : ℕ) :
    chartPolynomialEquiv (residualEquation (k := k) m) =
      Polynomial.X - Polynomial.C (Polynomial.X ^ m) := by
  rw [residualEquation, map_sub, map_pow, chartPolynomialEquiv_w,
    chartPolynomialEquiv_u, uCoord, vCoord, Polynomial.C_pow]

/-- The kernel is precisely the residual principal ideal in the actual chart ring. -/
theorem residualCurveMap_ker (m : ℕ) :
    RingHom.ker (residualCurveMap (k := k) m) = Ideal.span {residualEquation m} := by
  have hmap : Ideal.map (chartPolynomialEquiv (k := k)).toRingHom
      (Ideal.span {residualEquation (k := k) m}) =
        Ideal.span {Polynomial.X - Polynomial.C (Polynomial.X ^ m)} := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : planeRing k => Ideal.span {z})
      (chartPolynomialEquiv_residualEquation (k := k) m)
  rw [residualCurveMap, ← RingHom.comap_ker, Polynomial.ker_evalRingHom, ← hmap]
  exact Ideal.comap_map_of_bijective (chartPolynomialEquiv (k := k)).toRingHom
    (chartPolynomialEquiv (k := k)).bijective

theorem residualCurveMap_surjective (m : ℕ) :
    Function.Surjective (residualCurveMap (k := k) m) := by
  intro r
  refine ⟨chartPolynomialEquiv.symm (Polynomial.C r), ?_⟩
  simp [residualCurveMap]

@[simp] theorem residualCurveMap_residualEquation (m : ℕ) :
    residualCurveMap m (residualEquation (k := k) m) = 0 := by
  simp only [residualEquation, map_sub, map_pow, residualCurveMap_w, residualCurveMap_u, sub_self]

theorem residualCurveMap_totalEquation (m : ℕ) :
    residualCurveMap m (totalEquation (k := k) m) = 0 := by
  rw [totalEquation_factorization, map_mul, residualCurveMap_residualEquation, mul_zero]

/-- Removing all exceptional powers from the total-transform ideal gives exactly
the residual curve ideal. This is the actual ideal-membership saturation statement. -/
theorem saturation_totalEquation_iff (m : ℕ) (f : reesChartRing k) :
    (∃ j : ℕ, chartU (k := k) ^ j * f ∈ Ideal.span {totalEquation m}) ↔
      f ∈ Ideal.span {residualEquation m} := by
  constructor
  · rintro ⟨j, hj⟩
    rw [← residualCurveMap_ker, RingHom.mem_ker]
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hj
    have h : (Polynomial.X : Polynomial k) ^ j * residualCurveMap m f = 0 := by
      simpa only [map_mul, map_pow, residualCurveMap_u, residualCurveMap_totalEquation,
        zero_mul] using congrArg (residualCurveMap m) hg
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero j Polynomial.X_ne_zero)
  · intro hf
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
    refine ⟨1, Ideal.mem_span_singleton.mpr ⟨g, ?_⟩⟩
    rw [pow_one, hg, totalEquation_factorization, mul_assoc]

/-- The actual affine residual curve maps into the actual Rees chart. -/
def residualCurveChartMorphism (m : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (reesChartRing k)) :=
  Spec.map (CommRingCat.ofHom (residualCurveMap m))

instance residualCurveChartMorphism_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (residualCurveChartMorphism (k := k) m) :=
  IsClosedImmersion.spec_of_surjective _ (residualCurveMap_surjective m)

/-- Its composition with the actual blowup-chart projection recovers the original monomial curve. -/
theorem residualCurveChartMorphism_toSpec (m : ℕ) :
    residualCurveChartMorphism (k := k) m ≫ Spec.map (CommRingCat.ofHom baseMap) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ (m + 1)))) := by
  rw [residualCurveChartMorphism, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    residualCurveMap_baseMap]

/-- The same residual curve maps into the actual Rees Proj through its proved chart. -/
def residualCurveMorphism (m : ℕ) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ scheme (centerIdeal (k := k)) :=
  residualCurveChartMorphism m ≫ chartι centerIdeal centerU

/-- The lift lies over the prescribed monomial curve in the original affine plane. -/
theorem residualCurveMorphism_toSpec (m : ℕ) :
    residualCurveMorphism (k := k) m ≫ toSpec centerIdeal =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (Polynomial.X ^ (m + 1)))) := by
  rw [residualCurveMorphism, Category.assoc, chartι_toSpec]
  exact residualCurveChartMorphism_toSpec m

end KltDP.Examples.FrobeniusBlowupContact
