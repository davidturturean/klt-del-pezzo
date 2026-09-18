import KltDP.Geometry.SmoothPointBlowupAffineCanonicalCenter
import KltDP.Geometry.SmoothPointBlowupNativeRefinedFactors

/-!
# The original principal refinement chosen from the native chart factors

The Boolean split is confined to the original ring element and its
nonmembership property. It does not reconstruct an existential sheaf factor.
-/

noncomputable section

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open AffineBlowup KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

/-- The actual principal neighborhood supplied at each original chart prime. -/
def refinement (i : Bool) (p : PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ i))) :
    chartRing (extendedCenter k φ) (generator k φ i) := by
  cases i
  · exact SmoothPointBlowupNativeRefinedFactors.leftRefinement k φ hφ p
  · exact SmoothPointBlowupNativeRefinedFactors.rightRefinement k φ hφ p

theorem refinement_not_mem (i : Bool)
    (p : PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ i))) :
    refinement k φ hφ i p ∉ p.asIdeal := by
  cases i
  · exact SmoothPointBlowupNativeRefinedFactors.leftRefinement_not_mem k φ hφ p
  · exact SmoothPointBlowupNativeRefinedFactors.rightRefinement_not_mem k φ hφ p

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
