import KltDP.Geometry.CartierPullbackExceptionalModule
import KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

/-!
# The canonical Cartier module from the original affine blowup factor

The original global differential factor supplies the isomorphism used here.
The divisor is the literal signed pullback of the original representative
plus the original effective exceptional Cartier divisor, identified by its
actual ideal data. No canonical divisor formula or pushforward conclusion
is a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalCartier

open AffineBlowup AffineBlowupTopDifferential AffineNativeTopDifferential

/-- The actual affine canonical factor makes `π*K+E` a representative of the
original second exterior sheaf on the same original Rees blowup. -/
def canonicalModuleIso (k : Type u) [Field k]
    {S : Type u} [CommRing S] [Algebra k S]
    (φ : KltDP.Examples.FrobeniusBlowupContact.planeRing k →ₐ[k] S)
    (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)
    [IsIntegral (Spec (CommRingCat.of S))]
    [IsIntegral (scheme (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ))]
    [GenericPointPreserving (toSpec (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ))]
    (K : CartierDivisor (Spec (CommRingCat.of S)))
    (eK : cartierDivisorModule (Spec (CommRingCat.of S)) K ≅ intrinsic k S 2)
    (E : CartierDivisor (scheme (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)))
    (hE : HasRegularCartierEquations
      (scheme (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) E)
    (hI : effectiveCartierIdealDataOfRegularEquations
        (scheme (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) E hE =
      (exceptionalι (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)).ker) :
    cartierDivisorModule (scheme (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ))
        (DominantCartierPullback.pullbackHom
          (toSpec (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) K + E) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        (structureMap k S (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) 2 :=
  CartierPullbackExceptionalModule.ofFactorIso
    (toSpec (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) K (intrinsic k S 2)
    (topSheaf k S (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) eK E hE
    (exceptionalι (SmoothPointBlowupAffineCanonicalFactor.extendedCenter k φ)) hI
    (SmoothPointBlowupAffineCanonicalFactor.canonicalFactorIso k φ hφ)

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalCartier

#check @KltDP.Geometry.SmoothPointBlowupAffineCanonicalCartier.canonicalModuleIso
#print axioms KltDP.Geometry.SmoothPointBlowupAffineCanonicalCartier.canonicalModuleIso
