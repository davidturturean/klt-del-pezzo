import KltDP.Geometry.AffineBlowupConormal

/-!
# Actual reduced boundary pullbacks on the original Rees charts

On the original chart at `a`, the actual base map sends `b` to the actual
exceptional equation times `chartFraction I a b`. Pullbacks of zero, one,
or two selected principal branches therefore have the radical ideals below.
The same identities retain the actual exceptional centre ideal when that
component is also included. Swapping `a` and `b` gives the other chart.

These are identities of original chart ideals over an arbitrary base ring.
They neither assume nor assert that the residual fraction is an ambient
parameter or the ideal of a global schematic strict transform. Those local
regularity and closure comparisons must be supplied by geometric producers.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowup

variable {R : Type*} [CommRing R] (I : Ideal R) (a b : I)

/-- No boundary branch pulls back to the unit ideal on the actual chart. -/
theorem chart_boundary_unit_ideal :
    Ideal.map (chartBaseMap I a) (Ideal.span ({1} : Set R)) = ⊤ := by
  rw [Ideal.map_span, Set.image_singleton, map_one, Ideal.span_singleton_one]

/-- The selected chart-denominator branch pulls back to the actual
exceptional ideal, by the original chart centre equation. -/
theorem chart_boundary_first_ideal :
    Ideal.map (chartBaseMap I a) (Ideal.span ({(a : R)} : Set R)) = chartCenterIdeal I a := by
  rw [Ideal.map_span, Set.image_singleton]
  exact (map_chartBaseMap_ideal I a).symm

/-- The other original branch pulls back to exceptional times its
literal homogeneous Rees fraction. -/
theorem chart_boundary_second_ideal :
    Ideal.map (chartBaseMap I a) (Ideal.span ({(b : R)} : Set R)) =
      Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b} := by
  rw [Ideal.map_span, Set.image_singleton, chartBaseMap_mul_chartFraction]

/-- Removing the repeated exceptional factor from the actual two-branch
pullback preserves its exact radical ideal. -/
theorem chart_boundary_pair_radical :
    (Ideal.map (chartBaseMap I a) (Ideal.span ({(a : R) * (b : R)} : Set R))).radical =
      (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b}).radical := by
  rw [Ideal.map_span, Set.image_singleton, map_mul,
    ← chartBaseMap_mul_chartFraction I a b]
  simp only [← Ideal.span_singleton_mul_span_singleton, Ideal.radical_mul, inf_left_idem]

/-- Adding the actual exceptional divisor when no branch passes gives
precisely the original exceptional reduced ideal. -/
theorem chart_exceptional_boundary_unit_radical :
    (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span ({1} : Set R))).radical =
      (Ideal.span {chartBaseMap I a (a : R)}).radical := by
  rw [chart_boundary_unit_ideal, Ideal.mul_top, chartCenterIdeal, map_chartBaseMap_ideal]

/-- Adding the exceptional divisor to its denominator branch does not
introduce a repeated component into the reduced ideal. -/
theorem chart_exceptional_boundary_first_radical :
    (chartCenterIdeal I a *
      Ideal.map (chartBaseMap I a) (Ideal.span ({(a : R)} : Set R))).radical =
      (Ideal.span {chartBaseMap I a (a : R)}).radical := by
  rw [chart_boundary_first_ideal, Ideal.radical_mul, inf_idem,
    chartCenterIdeal, map_chartBaseMap_ideal]

/-- The exceptional divisor and the other original branch have reduced
ideal generated, up to radical, by the original exceptional equation and fraction product. -/
theorem chart_exceptional_boundary_second_radical :
    (chartCenterIdeal I a *
      Ideal.map (chartBaseMap I a) (Ideal.span ({(b : R)} : Set R))).radical =
      (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b}).radical := by
  rw [chart_boundary_second_ideal, chartCenterIdeal, map_chartBaseMap_ideal]
  simp only [← Ideal.span_singleton_mul_span_singleton, Ideal.radical_mul, inf_left_idem]

/-- The original exceptional divisor plus both original branches has
the same reduced ideal as exceptional times the actual residual fraction. -/
theorem chart_exceptional_boundary_pair_radical :
    (chartCenterIdeal I a *
      Ideal.map (chartBaseMap I a) (Ideal.span ({(a : R) * (b : R)} : Set R))).radical =
      (Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b}).radical := by
  rw [Ideal.radical_mul, chart_boundary_pair_radical, chartCenterIdeal, map_chartBaseMap_ideal]
  simp only [← Ideal.span_singleton_mul_span_singleton, Ideal.radical_mul, inf_left_idem]

end KltDP.Geometry.AffineBlowup
