import KltDP.Geometry.RefinedFactorWitnessChoice
import KltDP.Geometry.SmoothPointBlowupRefinedFactors

/-!
# One packaged choice from the original left-chart factor

The output type is inferred from the compiled original factor statement.
This isolated application does not rebuild its scheme or module carriers.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupNativeRefinedFactors

open KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

def leftData (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  RefinedFactorWitnessChoice.select
    (SmoothPointBlowupRefinedFactors.exists_left_factor k φ hφ p)

end KltDP.Geometry.SmoothPointBlowupNativeRefinedFactors
