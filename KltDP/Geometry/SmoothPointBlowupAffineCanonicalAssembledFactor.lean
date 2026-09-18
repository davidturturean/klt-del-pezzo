import KltDP.Geometry.SmoothPointBlowupAffineCanonicalAssembledIso

/-!
# The whole original normalization of the assembled chart factors

The generic Boolean normalization law receives the same original schemes,
maps and modules as the assembled isomorphism. The public proposition is
the exact inferred equation of that ordinary proved application.
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

private def factorIso_factor_proof :=
  bool_pullback_factor_comp%[
    scheme (extendedCenter k φ),
    (fun b : Bool => PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ b))),
    (fun (b : Bool) (p : PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ b))) =>
      principalRefinementScheme (extendedCenter k φ) (generator k φ) (refinement k φ hφ) ⟨b, p⟩),
    (fun (b : Bool) (p : PrimeSpectrum (chartRing (extendedCenter k φ) (generator k φ b))) =>
      principalRefinementMap (extendedCenter k φ) (generator k φ) (refinement k φ hφ) ⟨b, p⟩),
    (schemeModulePullback (toSpec (extendedCenter k φ))).obj (intrinsic k S 2),
    exceptionalTensor k S (extendedCenter k φ),
    topSheaf k S (extendedCenter k φ),
    leftTransportedFactorIso k φ hφ,
    rightTransportedFactorIso k φ hφ,
    exceptionalInclusion k S (extendedCenter k φ),
    blowdownMap k S (extendedCenter k φ),
    leftTransportedFactorIso_factor k φ hφ,
    rightTransportedFactorIso_factor k φ hφ]

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- The assembled factor preserves the original inclusion and original blowdown differential. -/
theorem factorIso_factor (t : principalRefinementIndex (extendedCenter k φ) (generator k φ)) :
    statementOf (factorIso_factor_proof k φ hφ t) :=
  factorIso_factor_proof k φ hφ t

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
