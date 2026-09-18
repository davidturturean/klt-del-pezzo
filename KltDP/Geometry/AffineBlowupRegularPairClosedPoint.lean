import KltDP.Geometry.AffineBlowupRegularPairExceptional
import KltDP.Geometry.PolynomialClosedPointEquation

/-!
# Closed exceptional points in the original regular-pair Rees chart

The actual exceptional quotient map has kernel the original extended
center ideal. Its proved polynomial presentation therefore identifies
every closed exceptional point ideal as `(a, b/a-r)`. The scalar `r` is
lifted from the original center quotient, not supplied as a coordinate
or regular-parameter premise.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup Polynomial

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
variable (ha : (a : R) ∈ nonZeroDivisors R)
variable (hb : Ideal.Quotient.mk (Ideal.span {(a : R)}) (b : R) ∈
  nonZeroDivisors (R ⧸ Ideal.span {(a : R)}))
variable (hI : I = Ideal.span {(a : R), (b : R)})

/-- The original exceptional quotient map followed by its proved,
coefficient-normalized polynomial presentation. -/
def exceptionalCoordinateMap : chartRing I a →+* Polynomial (R ⧸ I) :=
  (exceptionalChartEquiv I a b ha hb hI).toRingHom.comp
    (Ideal.Quotient.mk (chartCenterIdeal I a))

theorem exceptionalCoordinateMap_surjective :
    Function.Surjective (exceptionalCoordinateMap I a b ha hb hI) :=
  (exceptionalChartEquiv I a b ha hb hI).surjective.comp Ideal.Quotient.mk_surjective

theorem exceptionalCoordinateMap_ker :
    RingHom.ker (exceptionalCoordinateMap I a b ha hb hI) = chartCenterIdeal I a := by
  rw [exceptionalCoordinateMap,
    RingHom.ker_comp_of_injective _ (exceptionalChartEquiv I a b ha hb hI).injective,
    Ideal.mk_ker]

theorem exceptionalCoordinateMap_fraction :
    exceptionalCoordinateMap I a b ha hb hI (chartFraction I a b) = X :=
  exceptionalChartEquiv_fraction I a b ha hb hI

theorem exceptionalCoordinateMap_baseMap (r : R) :
    exceptionalCoordinateMap I a b ha hb hI (chartBaseMap I a r) =
      C (Ideal.Quotient.mk I r) :=
  exceptionalChartEquiv_baseMap I a b ha hb hI r

attribute [local instance] Ideal.Quotient.field

variable [I.IsMaximal] [IsAlgClosed (R ⧸ I)]

include ha hb hI in
/-- The ideal of an actual closed point lying on the original exceptional
divisor has the original exceptional equation and shifted fraction as generators. -/
theorem exists_closedPoint_ideal_eq (P : Ideal (chartRing I a)) [P.IsMaximal]
    (hcenter : chartCenterIdeal I a ≤ P) :
    ∃ r : R, P = Ideal.span {chartBaseMap I a (a : R),
      chartFraction I a b - chartBaseMap I a r} := by
  let φ := exceptionalCoordinateMap I a b ha hb hI
  have hφ : Function.Surjective φ := exceptionalCoordinateMap_surjective I a b ha hb hI
  have hker : RingHom.ker φ = chartCenterIdeal I a :=
    exceptionalCoordinateMap_ker I a b ha hb hI
  have hP : (Ideal.map φ P).comap φ = P := by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.mpr hcenter]
  have hnot : Ideal.map φ P ≠ ⊤ := by
    intro h
    have heq : (⊤ : Ideal (chartRing I a)) = P := by
      simpa only [h, Ideal.comap_top] using hP
    exact (inferInstance : P.IsMaximal).ne_top heq.symm
  letI : (Ideal.map φ P).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective φ hφ
      (inferInstance : P.IsMaximal)).resolve_left hnot
  obtain ⟨c, hc⟩ := PolynomialClosedPointEquation.exists_eq_span (R ⧸ I) (Ideal.map φ P)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
  have hfrac : φ (chartFraction I a b) = X :=
    exceptionalCoordinateMap_fraction I a b ha hb hI
  have hbase : φ (chartBaseMap I a r) = C (Ideal.Quotient.mk I r) :=
    exceptionalCoordinateMap_baseMap I a b ha hb hI r
  have hmap : Ideal.map φ (Ideal.span {chartFraction I a b - chartBaseMap I a r}) =
      Ideal.map φ P := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, hfrac, hbase, hr]
    exact hc.symm
  have hpre : Ideal.span {chartFraction I a b - chartBaseMap I a r} ⊔
      chartCenterIdeal I a = P := by
    calc
      _ = (Ideal.map φ (Ideal.span {chartFraction I a b - chartBaseMap I a r})).comap φ := by
        rw [Ideal.comap_map_of_surjective' φ hφ, hker]
      _ = (Ideal.map φ P).comap φ := congrArg (Ideal.comap φ) hmap
      _ = P := hP
  refine ⟨r, hpre.symm.trans ?_⟩
  rw [chartCenterIdeal, map_chartBaseMap_ideal, Ideal.span_insert, sup_comm]

end KltDP.Geometry.AffineBlowupRegularPairChart
