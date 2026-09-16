import KltDP.Examples.FrobeniusBlowupSmooth
import KltDP.Geometry.AffineBlowupConormal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual origin and exceptional quotient charts

The center `(u,v)` is the actual kernel of evaluation at the origin,
with quotient equal to the original field. The two actual exceptional
chart rings are quotients by the extended center ideal, and each is
proved isomorphic to the polynomial affine line by its actual equation.
All quotient isomorphisms retain their evaluation formulas.

These are actual local quotient schemes. Their identification with an
open cover of the global exceptional fiber, and its projective-line
gluing, are subsequent comparison steps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalCharts

open KltDP.Geometry.AffineBlowup FrobeniusBlowupContact FrobeniusBlowupSmooth

variable {k : Type u} [Field k]

/-- Evaluation at the actual origin of the original polynomial plane. -/
def originEvaluation : planeRing k →+* k :=
  (Polynomial.evalRingHom 0).comp (Polynomial.evalRingHom 0)

@[simp] theorem originEvaluation_constants (r : k) :
    originEvaluation (planeConstants r) = r := by
  simp [originEvaluation, planeConstants]

theorem originEvaluation_surjective : Function.Surjective (originEvaluation (k := k)) :=
  fun r => ⟨planeConstants r, originEvaluation_constants r⟩

/-- The existing center ideal is exactly the origin's evaluation kernel. -/
theorem originEvaluation_ker : RingHom.ker (originEvaluation (k := k)) = centerIdeal := by
  ext p
  rw [RingHom.mem_ker]
  symm
  simpa [originEvaluation, centerIdeal, uCoord, vCoord] using
    (Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero
      (a := (0 : k)) (b := (0 : Polynomial k)) (P := p))

/-- The center is an actual maximal ideal, derived from the field-valued evaluation. -/
instance centerIdeal_isMaximal : (centerIdeal (k := k)).IsMaximal := by
  rw [← originEvaluation_ker]
  exact RingHom.ker_isMaximal_of_surjective originEvaluation originEvaluation_surjective

/-- The corresponding actual closed point of the affine plane. -/
def origin : PrimeSpectrum (planeRing k) :=
  ⟨centerIdeal, inferInstance⟩

theorem origin_closed : IsClosed ({origin (k := k)} : Set (PrimeSpectrum (planeRing k))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal (origin (k := k))).mpr
    (centerIdeal_isMaximal (k := k))

/-- The origin's actual coordinate quotient is the original coefficient field. -/
def originQuotientEquiv : planeRing k ⧸ centerIdeal ≃+* k :=
  (Ideal.quotEquivOfEq originEvaluation_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := originEvaluation) originEvaluation_surjective)

@[simp] theorem originQuotientEquiv_mk (p : planeRing k) :
    originQuotientEquiv (Ideal.Quotient.mk centerIdeal p) = originEvaluation p := rfl

/-- Setting the first coordinate to zero leaves the second polynomial coordinate. -/
def exceptionalPlaneEvaluation : planeRing k →+* Polynomial k :=
  (Polynomial.evalRingHom 0).comp (coordinateSwap (k := k)).toRingHom

@[simp] theorem exceptionalPlaneEvaluation_u :
    exceptionalPlaneEvaluation (uCoord (k := k)) = 0 := by
  simp [exceptionalPlaneEvaluation, vCoord]

@[simp] theorem exceptionalPlaneEvaluation_v :
    exceptionalPlaneEvaluation (vCoord (k := k)) = Polynomial.X := by
  simp [exceptionalPlaneEvaluation, uCoord]

@[simp] theorem exceptionalPlaneEvaluation_constants (r : k) :
    exceptionalPlaneEvaluation (planeConstants r) = Polynomial.C r := by
  change Polynomial.eval 0 (coordinateSwap (planeConstants r)) = Polynomial.C r
  rw [coordinateSwap_constants]
  simp [planeConstants]

theorem exceptionalPlaneEvaluation_surjective :
    Function.Surjective (exceptionalPlaneEvaluation (k := k)) := by
  intro p
  refine ⟨coordinateSwap.symm (Polynomial.C p), ?_⟩
  simp [exceptionalPlaneEvaluation]

/-- The actual exceptional equation `u=0` is precisely the evaluation kernel. -/
theorem exceptionalPlaneEvaluation_ker :
    RingHom.ker (exceptionalPlaneEvaluation (k := k)) = Ideal.span {uCoord} := by
  have hmap : Ideal.map (coordinateSwap (k := k)).toRingHom
      (Ideal.span {uCoord}) = Ideal.span {vCoord} := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z : planeRing k => Ideal.span {z}) coordinateSwap_u
  rw [exceptionalPlaneEvaluation, ← RingHom.comap_ker, Polynomial.ker_evalRingHom,
    Polynomial.C_0, sub_zero]
  change Ideal.comap (coordinateSwap (k := k)).toRingHom (Ideal.span {vCoord}) =
    Ideal.span {uCoord}
  rw [← hmap]
  exact Ideal.comap_map_of_bijective (coordinateSwap (k := k)).toRingHom
    coordinateSwap.bijective

section Chart

variable (a : centerIdeal (k := k)) (e : chartRing centerIdeal a ≃+* planeRing k)
    (he : e (chartBaseMap centerIdeal a (a : planeRing k)) = uCoord)

include he in
/-- The actual extended center maps to the actual principal exceptional equation. -/
theorem polynomialModel_center :
    Ideal.map e.toRingHom (chartCenterIdeal centerIdeal a) = Ideal.span {uCoord} := by
  rw [chartCenterIdeal, map_chartBaseMap_ideal, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun z : planeRing k => Ideal.span {z}) he

/-- Evaluation on the actual Rees chart, through its proved polynomial presentation. -/
def exceptionalChartEvaluation : chartRing centerIdeal a →+* Polynomial k :=
  exceptionalPlaneEvaluation.comp e.toRingHom

include he in
theorem exceptionalChartEvaluation_ker :
    RingHom.ker (exceptionalChartEvaluation a e) = chartCenterIdeal centerIdeal a := by
  rw [exceptionalChartEvaluation, ← RingHom.comap_ker, exceptionalPlaneEvaluation_ker,
    ← polynomialModel_center a e he]
  exact Ideal.comap_map_of_bijective e.toRingHom e.bijective

theorem exceptionalChartEvaluation_surjective :
    Function.Surjective (exceptionalChartEvaluation a e) :=
  exceptionalPlaneEvaluation_surjective.comp e.surjective

/-- The quotient by the actual extended center is the polynomial affine line. -/
def exceptionalChartPolynomialEquiv : exceptionalChartRing centerIdeal a ≃+* Polynomial k :=
  (Ideal.quotEquivOfEq (exceptionalChartEvaluation_ker a e he).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := exceptionalChartEvaluation a e)
      (exceptionalChartEvaluation_surjective a e))

@[simp] theorem exceptionalChartPolynomialEquiv_mk (x : chartRing centerIdeal a) :
    exceptionalChartPolynomialEquiv a e he
      (Ideal.Quotient.mk (chartCenterIdeal centerIdeal a) x) =
        exceptionalPlaneEvaluation (e x) := rfl

end Chart

theorem uChart_selected_equation :
    chartPolynomialEquiv (chartBaseMap centerIdeal (centerU (k := k))
      (centerU (k := k) : planeRing k)) = uCoord :=
  chartPolynomialEquiv_u

theorem vChart_selected_equation :
    vChartPolynomialEquiv (chartBaseMap centerIdeal (centerV (k := k))
      (centerV (k := k) : planeRing k)) = uCoord := by
  change chartPolynomialEquiv
    (chartCoordinateEquiv centerIdeal centerIdeal centerV centerU
      (coordinateSwap (k := k)).toRingEquiv coordinateSwap_center coordinateSwap_v
        (chartBaseMap centerIdeal centerV vCoord)) = uCoord
  rw [chartCoordinateEquiv_baseMap]
  change chartPolynomialEquiv
    (chartBaseMap centerIdeal centerU (coordinateSwap (vCoord (k := k)))) = uCoord
  rw [coordinateSwap_v]
  exact uChart_selected_equation

/-- The first actual exceptional quotient chart has polynomial coordinate `v/u`. -/
def uExceptionalEquiv : exceptionalChartRing centerIdeal (centerU (k := k)) ≃+* Polynomial k :=
  exceptionalChartPolynomialEquiv (centerU (k := k))
    (chartPolynomialEquiv (k := k)) (uChart_selected_equation (k := k))

/-- The second actual exceptional quotient chart has polynomial coordinate `u/v`. -/
def vExceptionalEquiv : exceptionalChartRing centerIdeal (centerV (k := k)) ≃+* Polynomial k :=
  exceptionalChartPolynomialEquiv (centerV (k := k))
    (vChartPolynomialEquiv (k := k)) (vChart_selected_equation (k := k))

@[simp] theorem uExceptionalEquiv_coordinate :
    uExceptionalEquiv (k := k) (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU)
      (chartW (k := k))) = Polynomial.X := by
  change exceptionalPlaneEvaluation (chartPolynomialEquiv chartW) = Polynomial.X
  rw [chartPolynomialEquiv_w, exceptionalPlaneEvaluation_v]

/-- The actual ratio `u/v` is the free coordinate in the second chart. -/
theorem vChartPolynomialEquiv_coordinate :
    vChartPolynomialEquiv (chartFraction centerIdeal (centerV (k := k)) centerU) =
      vCoord := by
  have hu : vChartPolynomialEquiv
      (chartBaseMap centerIdeal (centerV (k := k)) (uCoord (k := k))) =
        uCoord * vCoord := by
    change chartPolynomialEquiv
      (chartCoordinateEquiv centerIdeal centerIdeal centerV centerU
        (coordinateSwap (k := k)).toRingEquiv coordinateSwap_center coordinateSwap_v
          (chartBaseMap centerIdeal centerV uCoord)) = uCoord * vCoord
    rw [chartCoordinateEquiv_baseMap]
    change chartPolynomialEquiv
      (chartBaseMap centerIdeal centerU (coordinateSwap (uCoord (k := k)))) = uCoord * vCoord
    rw [coordinateSwap_u]
    exact (chartToPolynomial_baseMap vCoord).trans chartSubstitution_v
  have h := congrArg (vChartPolynomialEquiv (k := k))
    (chartBaseMap_mul_chartFraction centerIdeal (centerV (k := k)) centerU)
  simp only [map_mul, vChart_selected_equation] at h
  change uCoord * vChartPolynomialEquiv
      (chartFraction centerIdeal (centerV (k := k)) centerU) =
    vChartPolynomialEquiv (chartBaseMap centerIdeal centerV (uCoord (k := k))) at h
  rw [hu] at h
  exact mul_left_cancel₀ uCoord_ne_zero h

@[simp] theorem vExceptionalEquiv_coordinate :
    vExceptionalEquiv (k := k) (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
      (chartFraction centerIdeal (centerV (k := k)) centerU)) = Polynomial.X := by
  change exceptionalPlaneEvaluation
    (vChartPolynomialEquiv (chartFraction centerIdeal centerV centerU)) = Polynomial.X
  rw [vChartPolynomialEquiv_coordinate, exceptionalPlaneEvaluation_v]

@[simp] theorem uExceptionalEquiv_constants (r : k) :
    uExceptionalEquiv (k := k) (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerU)
      (chartConstants centerU r)) = Polynomial.C r := by
  change exceptionalPlaneEvaluation (chartPolynomialEquiv (chartConstants centerU r)) = _
  rw [uChartPolynomialEquiv_constants, exceptionalPlaneEvaluation_constants]

@[simp] theorem vExceptionalEquiv_constants (r : k) :
    vExceptionalEquiv (k := k) (Ideal.Quotient.mk (chartCenterIdeal (centerIdeal (k := k)) centerV)
      (chartConstants centerV r)) = Polynomial.C r := by
  change exceptionalPlaneEvaluation (vChartPolynomialEquiv (chartConstants centerV r)) = _
  rw [vChartPolynomialEquiv_constants, exceptionalPlaneEvaluation_constants]

/-- The first actual exceptional closed affine scheme is an affine line. -/
def uExceptionalIso : exceptionalChart centerIdeal (centerU (k := k)) ≅
    Spec (CommRingCat.of (Polynomial k)) :=
  Scheme.Spec.mapIso (uExceptionalEquiv (k := k)).symm.toCommRingCatIso.op

/-- The second actual exceptional closed affine scheme is an affine line. -/
def vExceptionalIso : exceptionalChart centerIdeal (centerV (k := k)) ≅
    Spec (CommRingCat.of (Polynomial k)) :=
  Scheme.Spec.mapIso (vExceptionalEquiv (k := k)).symm.toCommRingCatIso.op

end KltDP.Examples.FrobeniusExceptionalCharts
