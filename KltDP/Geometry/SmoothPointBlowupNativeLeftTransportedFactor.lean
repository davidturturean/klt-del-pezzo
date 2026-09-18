import KltDP.Geometry.SmoothPointBlowupNativeLeftTransportedIso

/-!
# Whole original normalization of the explicit left-chart factor

The proof term applies the existing generic normalization theorem with all
arguments extracted from the original stored equality. It adds no assumption.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

private def leftTransportedFactorIso_factor_proof
    (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  native_pullback_factor_comp%[
    SmoothPointBlowupNativeRefinedFactors.leftFactorIso_factor k φ hφ p,
    leftNativeRefinementMap_eq k φ hφ p]

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

theorem leftTransportedFactorIso_factor
    (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    statementOf (leftTransportedFactorIso_factor_proof k φ hφ p) :=
  leftTransportedFactorIso_factor_proof k φ hφ p

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
