import KltDP.Geometry.SmoothPointBlowupAffineCanonicalRefinementMaps

/-!
# Original refinement equalities with the measured native map carrier

The bounded native diagnostic found only three aliases: the chosen index,
the extended center, and the Rees chart ring. These equalities expose those
original expressions before a dependent sheaf-factor transport is applied.
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

theorem leftNativeRefinementMap_eq
    (p : PrimeSpectrum (SmoothPointBlowupChartBasis.chartRing k φ)) :
    refinedChartMap
      (B := Localization.Away (SmoothPointBlowupNativeRefinedFactors.leftData k φ hφ p).1)
      (Ideal.map φ.toRingHom centerIdeal)
      (mappedElement centerIdeal φ.toRingHom centerU)
      (algebraMap (AffineBlowup.chartRing (Ideal.map φ.toRingHom centerIdeal)
          (mappedElement centerIdeal φ.toRingHom centerU))
        (Localization.Away (SmoothPointBlowupNativeRefinedFactors.leftData k φ hφ p).1)) =
      principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ)
        ⟨false, p⟩ := by
  simpa only [leftRefinementMap, SmoothPointBlowupNativeRefinedFactors.leftRefinement,
    extendedCenter, SmoothPointBlowupChartBasis.chartRing] using
      leftRefinementMap_eq k φ hφ p

theorem rightNativeRefinementMap_eq
    (p : PrimeSpectrum (SmoothPointBlowupRightChartBasis.chartRing k φ)) :
    refinedChartMap
      (B := Localization.Away (SmoothPointBlowupNativeRefinedFactors.rightData k φ hφ p).1)
      (Ideal.map φ.toRingHom centerIdeal)
      (mappedElement centerIdeal φ.toRingHom centerV)
      (algebraMap (AffineBlowup.chartRing (Ideal.map φ.toRingHom centerIdeal)
          (mappedElement centerIdeal φ.toRingHom centerV))
        (Localization.Away (SmoothPointBlowupNativeRefinedFactors.rightData k φ hφ p).1)) =
      principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ)
        ⟨true, p⟩ := by
  simpa only [rightRefinementMap, SmoothPointBlowupNativeRefinedFactors.rightRefinement,
    extendedCenter, SmoothPointBlowupRightChartBasis.chartRing] using
      rightRefinementMap_eq k φ hφ p

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
