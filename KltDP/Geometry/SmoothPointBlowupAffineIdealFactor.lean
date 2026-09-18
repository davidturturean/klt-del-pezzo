import KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

/-!
# The original affine factor for an equal actual center ideal

Transport only the ideal parameter of the proved original factor. Its
normalization is proved by equality elimination before any geometric
specialization, keeping the actual blowup objects and maps unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor

open AffineBlowup AffineBlowupTopDifferential AffineNativeTopDifferential

variable (k : Type u) [Field k] {S : Type u} [CommRing S] [Algebra k S]
    (φ : KltDP.Examples.FrobeniusBlowupContact.planeRing k →ₐ[k] S)
    (hφ : φ.toRingHom.IsStandardSmoothOfRelativeDimension 0)
    (I : Ideal S) (hI : extendedCenter k φ = I)

/-- The proved factor on the same ideal under its specified original name. -/
def factorIsoOfIdealEq :
    (schemeModulePullback (toSpec I)).obj (intrinsic k S 2) ≅ exceptionalTensor k S I :=
  hI ▸ canonicalFactorIso k φ hφ

theorem factorIsoOfIdealEq_comp :
    (factorIsoOfIdealEq k φ hφ I hI).hom ≫ exceptionalInclusion k S I =
      blowdownMap k S I := by
  subst I
  exact canonicalFactorIso_comp k φ hφ

end KltDP.Geometry.SmoothPointBlowupAffineCanonicalFactor
