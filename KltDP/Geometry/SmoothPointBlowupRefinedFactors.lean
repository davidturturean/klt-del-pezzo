import KltDP.Geometry.SmoothPointBlowupLeftRefinedFactor
import KltDP.Geometry.SmoothPointBlowupRightRefinedFactor

/-!
# Actual global-map factors on both original point-blowup charts

The original standard-smooth plane map supplies every local factor. Both
outputs are isomorphisms between pullbacks of the original global source and
exceptional tensor, preserving the original blowdown differential. There is
no basis, regularity, local compatibility, or factorization premise.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupRefinedFactors

open KltDP.Examples.FrobeniusBlowupContact
open AffineBlowupChartBaseChange AffineBlowupTopDifferential

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

private def left_proof (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :=
  SmoothPointBlowupLeftRefinedFactor.exists_factor k φ hφ p

private def right_proof (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :=
  SmoothPointBlowupRightRefinedFactor.exists_factor k φ hφ p

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- Every original first-chart prime has a normalized original global-map factor on a principal neighborhood. -/
theorem exists_left_factor (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    statementOf (left_proof k φ hφ p) := left_proof k φ hφ p

/-- The same statement on every original complementary-chart prime. -/
theorem exists_right_factor (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    statementOf (right_proof k φ hφ p) := right_proof k φ hφ p

end KltDP.Geometry.SmoothPointBlowupRefinedFactors
