import KltDP.Geometry.RefinedFactorWitnessChoice
import KltDP.Geometry.SmoothPointBlowupRefinedFactors

/-!
# One packaged choice from the original right-chart factor

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

def rightData (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  RefinedFactorWitnessChoice.select
    (SmoothPointBlowupRefinedFactors.exists_right_factor k φ hφ p)

end KltDP.Geometry.SmoothPointBlowupNativeRefinedFactors
