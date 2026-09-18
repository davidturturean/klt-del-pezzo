import KltDP.Geometry.AffineBlowupChartBaseChangeMap
import Mathlib.RingTheory.Localization.Ideal

/-! Clearing only original base-localization denominators in an actual Rees chart. -/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartBaseChange

open AffineBlowup

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Every element of the localized Rees chart is an original chart element
divided by the image of an original localization denominator. -/
theorem exists_original_chart_denominator (I : Ideal R) (M : Submonoid R)
    [IsLocalization M S] (a : I)
    (z : chartRing (I.map (algebraMap R S)) (mappedElement I (algebraMap R S) a)) :
    ∃ (w : chartRing I a) (s : M),
      chartBaseMap (I.map (algebraMap R S)) (mappedElement I (algebraMap R S) a)
        (algebraMap R S s) * z = chartMap I (algebraMap R S) a w := by
  let J := I.map (algebraMap R S)
  let b : J := mappedElement I (algebraMap R S) a
  let χ := chartMap I (algebraMap R S) a
  obtain ⟨n, r, rfl⟩ := exists_chartMonomialFraction J b z
  have hr : (r : S) ∈ (I ^ n).map (algebraMap R S) := by
    rw [Ideal.map_pow]
    exact r.property
  obtain ⟨⟨w, s⟩, hws⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hr
  refine ⟨chartMonomialFraction I a n w, s, ?_⟩
  apply (mul_cancel_left_mem_nonZeroDivisors
    (pow_mem (chartBaseMap_equation_mem_nonZeroDivisors J b) n)).mp
  change chartBaseMap J b (b : S) ^ n *
      (chartBaseMap J b (algebraMap R S s) * chartMonomialFraction J b n r) =
    chartBaseMap J b (b : S) ^ n * χ (chartMonomialFraction I a n w)
  calc
    _ = chartBaseMap J b (algebraMap R S s) *
        (chartBaseMap J b (b : S) ^ n * chartMonomialFraction J b n r) := by ring
    _ = chartBaseMap J b (algebraMap R S s) * chartBaseMap J b (r : S) := by
      rw [chartBaseMap_pow_mul_chartMonomialFraction]
    _ = chartBaseMap J b ((r : S) * algebraMap R S s) := by rw [map_mul, mul_comm]
    _ = chartBaseMap J b (algebraMap R S (w : R)) := by rw [hws]
    _ = χ (chartBaseMap I a (w : R)) := (chartMap_baseMap I (algebraMap R S) a _).symm
    _ = χ (chartBaseMap I a (a : R) ^ n * chartMonomialFraction I a n w) := by
      rw [chartBaseMap_pow_mul_chartMonomialFraction]
    _ = χ (chartBaseMap I a (a : R)) ^ n * χ (chartMonomialFraction I a n w) := by
      rw [map_mul, map_pow]
    _ = _ := by rw [show χ (chartBaseMap I a (a : R)) = chartBaseMap J b (b : S) from
      chartMap_baseMap I (algebraMap R S) a (a : R)]

end KltDP.Geometry.AffineBlowupChartBaseChange
