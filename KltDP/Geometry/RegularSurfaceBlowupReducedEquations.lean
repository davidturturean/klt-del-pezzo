import KltDP.Geometry.RegularSurfaceBlowupReducedIdeals

/-!
# Original reduced chart equations with zero or one boundary branch

These complete the already proved two-branch reduced ideal formula.
Multiplying the original boundary equation by a unit leaves the actual
pulled ideal unchanged. The centre and residual ideals are the original
Rees-chart ideals; their radicality is derived from the original regular
surface parameters.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (I : Ideal R) (a b : I)
variable (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
variable (hI : I = Ideal.span {(a : R), (b : R)}) (hmax : I = maximalIdeal R)

/-- Original source units do not change the literal pulled boundary ideal. -/
theorem reduced_exceptional_unit_mul_ideal (c : R) (v : Rˣ) :
    (chartCenterIdeal I a * Ideal.map (chartBaseMap I a)
      (Ideal.span {(v : R) * c})).radical =
      (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span {c})).radical := by
  rw [Ideal.span_singleton_mul_left_unit v.isUnit c]

include hR hdim hI hmax in
/-- The original exceptional equation generates a radical ideal. -/
theorem exceptional_span_radical :
    (Ideal.span {chartBaseMap I a (a : R)}).radical =
      Ideal.span {chartBaseMap I a (a : R)} := by
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim (a : R) (b : R)
    (hI.symm.trans hmax)
  letI : I.IsPrime := hmax.symm ▸ (inferInstance : (maximalIdeal R).IsPrime)
  have hx := (chartCenterIdeal_isPrime I a b hpair.1 hpair.2 hI).isRadical.radical
  simpa only [chartCenterIdeal, map_chartBaseMap_ideal] using hx

include hR hdim hI hmax in
/-- Off the original boundary, the reduced enlarged boundary is exceptional. -/
theorem reduced_exceptional_unit_ideal (c : R) (hc : IsUnit c) :
    (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span {c})).radical =
      Ideal.span {chartBaseMap I a (a : R)} := by
  rw [Ideal.span_singleton_eq_top.mpr hc, Ideal.map_top, Ideal.mul_top,
    chartCenterIdeal, map_chartBaseMap_ideal]
  exact exceptional_span_radical I a b hR hdim hI hmax

include hR hdim hI hmax in
/-- The denominator branch introduces no repeated reduced exceptional factor. -/
theorem reduced_exceptional_first_ideal :
    (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span {(a : R)})).radical =
      Ideal.span {chartBaseMap I a (a : R)} :=
  (chart_exceptional_boundary_first_radical I a).trans
    (exceptional_span_radical I a b hR hdim hI hmax)

include hR hdim hI hmax in
/-- The other branch contributes exactly its original residual fraction. -/
theorem reduced_exceptional_second_ideal :
    (chartCenterIdeal I a * Ideal.map (chartBaseMap I a) (Ideal.span {(b : R)})).radical =
      Ideal.span {chartBaseMap I a (a : R) * chartFraction I a b} :=
  (chart_exceptional_boundary_second_radical I a b).trans
    (exceptional_fraction_span_radical I a b hR hdim hI hmax)

end KltDP.Geometry.AffineBlowupRegularPairChart
