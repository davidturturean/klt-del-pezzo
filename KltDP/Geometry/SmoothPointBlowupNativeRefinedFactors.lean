import KltDP.Geometry.SmoothPointBlowupNativeLeftFactorChoice
import KltDP.Geometry.SmoothPointBlowupNativeRightFactorChoice

/-!
# Named choices from the compiled original chart factors

Each definition projects the single packaged original native witness.
No existential choice, Boolean chart, or sheaf map is reconstructed here.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupNativeRefinedFactors

open KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

abbrev leftRefinement (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  (leftData k φ hφ p).1

abbrev rightRefinement (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  (rightData k φ hφ p).1

theorem leftRefinement_not_mem (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    leftRefinement k φ hφ p ∉ p.asIdeal :=
  (leftData k φ hφ p).2.property.1

theorem rightRefinement_not_mem
    (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    rightRefinement k φ hφ p ∉ p.asIdeal :=
  (rightData k φ hφ p).2.property.1

def leftFactorIso (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  (leftData k φ hφ p).2.val

def rightFactorIso (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  (rightData k φ hφ p).2.val

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

private def leftFactorIso_factor_proof
    (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  (leftData k φ hφ p).2.property.2

private def rightFactorIso_factor_proof
    (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  (rightData k φ hφ p).2.property.2

theorem leftFactorIso_factor (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    statementOf (leftFactorIso_factor_proof k φ hφ p) :=
  leftFactorIso_factor_proof k φ hφ p

theorem rightFactorIso_factor
    (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    statementOf (rightFactorIso_factor_proof k φ hφ p) :=
  rightFactorIso_factor_proof k φ hφ p

end KltDP.Geometry.SmoothPointBlowupNativeRefinedFactors
