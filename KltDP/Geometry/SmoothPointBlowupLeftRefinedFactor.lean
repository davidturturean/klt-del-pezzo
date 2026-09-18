import KltDP.Geometry.AffineBlowupRefinedMappedIdealCover
import KltDP.Geometry.SmoothPointBlowupIntrinsicTensor

/-!
# The original left chart refinement as a separately checked theorem

Only the relevant chart's intrinsic producer is imported in this proof leaf.
The matching original ground algebra is supplied explicitly; the abstract
mapped-ideal adapter retains the original source and all original maps.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupLeftRefinedFactor

open KltDP.Examples.FrobeniusBlowupContact
open AffineBlowupChartBaseChange AffineBlowupTopDifferential

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

/-- Equality of the original localization/point-blowup map, proved pointwise. -/
private theorem sourceMapDiagram (r : SmoothPointBlowupChartBasis.chartRing k φ) :
    (algebraMap (SmoothPointBlowupChartBasis.chartRing k φ) (Localization.Away r)).comp
      (AffineBlowup.chartBaseMap (Ideal.map φ.toRingHom centerIdeal)
        (mappedElement centerIdeal φ.toRingHom centerU)) =
      (SmoothPointBlowupLocalizedChart.localizedBaseMap k φ r).toRingHom := by
  apply RingHom.ext
  intro x
  exact (SmoothPointBlowupLocalizedChart.localizedBaseMap_apply k φ r x).symm

private def factor_proof (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  letI : Algebra k (SmoothPointBlowupChartBasis.chartRing k φ) :=
    SmoothPointBlowupChartBasis.groundAlgebra k φ
  exists_refined_factor_of_mapped_ideal k S (Ideal.map φ.toRingHom centerIdeal)
    (mappedElement centerIdeal φ.toRingHom centerU)
    (SmoothPointBlowupLocalizedChart.localizedBaseMap k φ) (sourceMapDiagram k φ) p
    (SmoothPointBlowupIntrinsicTensor.exists_intrinsic_tensor_factor k φ hφ p)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The original left chart has a normalized factor on an actual principal neighborhood. -/
theorem exists_factor (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    statementOf (factor_proof k φ hφ p) := factor_proof k φ hφ p

#print axioms exists_factor

end KltDP.Geometry.SmoothPointBlowupLeftRefinedFactor
