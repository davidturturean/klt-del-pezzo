import KltDP.Geometry.SmoothPointBlowupNativeLeftTransportedFactor
import KltDP.Geometry.SmoothPointBlowupNativeRightTransportedFactor
import KltDP.Geometry.SchemeModulePullbackBoolFactorTerm

/-!
# Assembly of the two compiled original chart-factor families

The actual principal-refinement schemes and maps are supplied before the
original branch isomorphisms are substituted into the proved Boolean
constructor. The result retains its inferred original pullback carriers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open AffineBlowup AffineBlowupTopDifferential AffineNativeTopDifferential
open KltDP.Examples.FrobeniusBlowupContact

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)

/-- The original chosen chart factors over the original dependent principal-refinement index. -/
def factorIso :=
  bool_pullback_factor_iso%[
    scheme (extendedCenter k φ),
    (fun b : Bool => PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ b))),
    (fun (b : Bool) (p : PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ b))) =>
      principalRefinementScheme (extendedCenter k φ) (generator k φ) (refinement k φ hφ) ⟨b, p⟩),
    (fun (b : Bool) (p : PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ b))) =>
      principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ) ⟨b, p⟩),
    (schemeModulePullback (toSpec (extendedCenter k φ))).obj (intrinsic k S 2),
    exceptionalTensor k S (extendedCenter k φ),
    leftTransportedFactorIso k φ hφ,
    rightTransportedFactorIso k φ hφ]

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
