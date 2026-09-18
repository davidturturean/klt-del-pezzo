import KltDP.Geometry.SchemeModulePullbackNativeFactorTerm
import KltDP.Geometry.SmoothPointBlowupAffineCanonicalNativeRefinementMaps

/-!
# The original right transported factor with all generic arguments explicit

The stored native factor supplies every actual map and module argument.
Only the original proved map equality is used for the transport.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

def rightTransportedFactorIso (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  native_pullback_factor_iso%[
    SmoothPointBlowupNativeRefinedFactors.rightFactorIso k φ hφ p,
    rightNativeRefinementMap_eq k φ hφ p]

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
