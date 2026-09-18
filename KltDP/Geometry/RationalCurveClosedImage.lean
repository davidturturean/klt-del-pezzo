import KltDP.Geometry.PrimeCurveClosedImage

/-!
# Rational closed-image source comparison

An original closed immersion of a rational scheme determines its actual
prime-curve image. Its reduced image scheme is isomorphic to the original
source, with the original inclusion retained. Precomposing a lifted map
by that isomorphism leaves its actual prime-curve image unchanged.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.RationalCurveClosedImage

open NormalProjectiveSurface PrimeCurveOfClosedImmersion

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)
    {C : Scheme.{u}} (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (eC : C ≅ projectiveSpace k 1)

/-- The actual rational closed-image curve scheme retains the original source. -/
def sourceIso : (primeCurveOfIsoProjectiveLine S f eC).toScheme ≅ C := by
  letI : IsIntegral C := isIntegral_of_iso_projectiveLine eC
  exact (asIso (PrimeCurveInclusionLift.lift
    (primeCurveOfIsoProjectiveLine S f eC) f rfl)).symm

/-- The source comparison recovers the original closed immersion exactly. -/
@[reassoc]
theorem sourceIso_hom_map :
    (sourceIso S f eC).hom ≫ f = (primeCurveOfIsoProjectiveLine S f eC).inclusion := by
  letI : IsIntegral C := isIntegral_of_iso_projectiveLine eC
  exact (PrimeCurveInclusionLift.inclusion_eq_inv_lift
    (primeCurveOfIsoProjectiveLine S f eC) f rfl).symm

/-- Transport of the source by an actual isomorphism preserves the actual target prime curve. -/
theorem closedImage_precomp_iso {T : NormalProjectiveSurface k}
    (P : T.PrimeCurve) (η : P.toScheme ≅ C) :
    P.closedImage (T := S) (η.hom ≫ f) = primeCurveOfIsoProjectiveLine S f eC := by
  apply PrimeCurve.ext
  change Set.range (f.base ∘ η.hom.base) = Set.range f.base
  exact η.schemeIsoToHomeo.surjective.range_comp f.base

end KltDP.Geometry.RationalCurveClosedImage

#print axioms KltDP.Geometry.RationalCurveClosedImage.sourceIso_hom_map
#print axioms KltDP.Geometry.RationalCurveClosedImage.closedImage_precomp_iso
