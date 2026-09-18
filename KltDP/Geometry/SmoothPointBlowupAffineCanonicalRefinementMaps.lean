import KltDP.Geometry.SmoothPointBlowupAffineCanonicalRefinement

/-!
# Original scheme-map equalities for the two chosen principal refinements

Only the ring elements and original localization/chart maps are normalized.
The sheaf factors will be transported by the proved equalities.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open AffineBlowup AffineBlowupChartBaseChange
open KltDP.Examples.FrobeniusBlowupContact

universe u

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

def leftRefinementMap (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    Spec (CommRingCat.of
      (Localization.Away (SmoothPointBlowupNativeRefinedFactors.leftRefinement k φ hφ p))) ⟶
        scheme (extendedCenter k φ) :=
  refinedChartMap
    (B := Localization.Away (SmoothPointBlowupNativeRefinedFactors.leftRefinement k φ hφ p))
    (extendedCenter k φ) (mappedElement centerIdeal φ.toRingHom centerU)
    (algebraMap (SmoothPointBlowupChartBasis.chartRing k φ)
      (Localization.Away (SmoothPointBlowupNativeRefinedFactors.leftRefinement k φ hφ p)))

def rightRefinementMap (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    Spec (CommRingCat.of
      (Localization.Away (SmoothPointBlowupNativeRefinedFactors.rightRefinement k φ hφ p))) ⟶
        scheme (extendedCenter k φ) :=
  refinedChartMap
    (B := Localization.Away (SmoothPointBlowupNativeRefinedFactors.rightRefinement k φ hφ p))
    (extendedCenter k φ) (mappedElement centerIdeal φ.toRingHom centerV)
    (algebraMap (SmoothPointBlowupRightChartBasis.chartRing k φ)
      (Localization.Away (SmoothPointBlowupNativeRefinedFactors.rightRefinement k φ hφ p)))

theorem leftRefinementMap_eq (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    leftRefinementMap k φ hφ p =
      principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ)
        ⟨false, p⟩ := rfl

theorem rightRefinementMap_eq
    (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    rightRefinementMap k φ hφ p =
      principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ)
        ⟨true, p⟩ := rfl

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
