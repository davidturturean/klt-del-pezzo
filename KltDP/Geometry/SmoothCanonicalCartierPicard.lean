import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# The Picard class of the actual smooth canonical Cartier representative

The independently constructed Cartier representative represents the actual
top-differential line. Its Picard class is obtained from the proved sheaf
isomorphism, so the representative can be used with the existing intersection
degree maps. No dualizing-sheaf identification is asserted here.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SmoothCanonicalCartierPicard

open SmoothSurfaceKaehlerAtlas SmoothCanonicalCartierRepresentative

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsSmoothOfRelativeDimension 2 f]

/-- The actual Cartier representative has the class of the original canonical line. -/
theorem cartierPicardHom_representative :
    cartierPicardHom X (cartierRepresentative f) =
      Additive.ofMul (canonicalSheafOfSmoothSurface f).toPic :=
  congrArg Additive.ofMul (SchemeKernelIdealIsoTransport.toPic_eq_of_iso
    (cartierDivisorInvertibleSheaf X (cartierRepresentative f))
    (canonicalSheafOfSmoothSurface f) (cartierRepresentativeIso f))

end KltDP.Geometry.SmoothCanonicalCartierPicard
