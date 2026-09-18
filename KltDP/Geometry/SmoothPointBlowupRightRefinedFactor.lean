import KltDP.Geometry.AffineBlowupRefinedMappedIdealCover
import KltDP.Geometry.SmoothPointBlowupRightIntrinsicTensor

/-!
# The original right chart refinement as a separately checked theorem

Only the relevant chart's intrinsic producer is imported in this proof leaf.
The matching original ground algebra is supplied explicitly; the abstract
mapped-ideal adapter retains the original source and all original maps.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupRightRefinedFactor

open KltDP.Examples.FrobeniusBlowupContact
open AffineBlowupChartBaseChange AffineBlowupTopDifferential

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

/-- Equality of the original localization/point-blowup map, proved pointwise. -/
private theorem sourceMapDiagram (r : SmoothPointBlowupRightChartBasis.chartRing k φ) :
    (algebraMap (SmoothPointBlowupRightChartBasis.chartRing k φ) (Localization.Away r)).comp
      (AffineBlowup.chartBaseMap (Ideal.map φ.toRingHom centerIdeal)
        (mappedElement centerIdeal φ.toRingHom centerV)) =
      (SmoothPointBlowupRightLocalizedChart.localizedBaseMap k φ r).toRingHom := by
  apply RingHom.ext
  intro x
  exact (SmoothPointBlowupRightLocalizedChart.localizedBaseMap_apply k φ r x).symm

private def factor_proof (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  letI : Algebra k (SmoothPointBlowupRightChartBasis.chartRing k φ) :=
    SmoothPointBlowupRightChartBasis.groundAlgebra k φ
  exists_refined_factor_of_mapped_ideal k S (Ideal.map φ.toRingHom centerIdeal)
    (mappedElement centerIdeal φ.toRingHom centerV)
    (SmoothPointBlowupRightLocalizedChart.localizedBaseMap k φ) (sourceMapDiagram k φ) p
    (SmoothPointBlowupRightIntrinsicTensor.exists_intrinsic_tensor_factor k φ hφ p)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The original right chart has a normalized factor on an actual principal neighborhood. -/
theorem exists_factor (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    statementOf (factor_proof k φ hφ p) := factor_proof k φ hφ p

#print axioms exists_factor

end KltDP.Geometry.SmoothPointBlowupRightRefinedFactor
