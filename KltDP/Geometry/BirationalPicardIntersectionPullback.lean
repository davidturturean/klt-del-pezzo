import KltDP.Geometry.BirationalCartierIntersectionPullback
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import KltDP.Geometry.PrimeCurveClassPairing

/-!
# Original Picard intersection under birational pullback

The actual module isomorphism of signed Cartier pullback identifies its
Picard class. Cartier representatives of the original two Picard classes
then reduce the intersection formula to the already proved Cartier formula.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

namespace DominantCartierPullback

/-- The actual signed pullback module gives the original Picard pullback. -/
theorem cartierPicardClass_pullback
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [GenericPointPreserving π] (D : CartierDivisor X) :
    schemePicardPullbackHom π (cartierPicardClass X D) =
      cartierPicardClass S (pullbackHom π D) := by
  change schemePicardPullbackHom π (cartierDivisorInvertibleSheaf X D).toPic =
    (cartierDivisorInvertibleSheaf S (pullbackHom π D)).toPic
  rw [schemePicardPullbackHom_toPic]
  exact SchemeKernelIdealIsoTransport.toPic_eq_of_iso
    (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X D))
    (cartierDivisorInvertibleSheaf S (pullbackHom π D)) (modulePullbackIso π D)

end DominantCartierPullback

namespace BirationalPicardIntersectionPullback

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme π)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)

include hπ hbir

/-- Original proper birational Picard pullback is an isometry for the
original regular-surface pairings. -/
theorem picardPairing_pullback (p q : X.toScheme.Pic) :
    S.picardPairing hS (schemePicardPullbackHom π p) (schemePicardPullbackHom π q) =
      X.picardPairing hX p q := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨D, rfl⟩ := cartierPicardClass_surjective X.toScheme p
  obtain ⟨E, rfl⟩ := cartierPicardClass_surjective X.toScheme q
  rw [DominantCartierPullback.cartierPicardClass_pullback,
    DominantCartierPullback.cartierPicardClass_pullback,
    S.picardPairing_class hS, X.picardPairing_class hX]
  exact BirationalCartierIntersectionPullback.intersectionPairing_pullback
    π hπ hbir hS hX D E

/-- The same isometry in the original additive Picard notation. -/
theorem pairing_pullback (p q : Additive X.toScheme.Pic) :
    PrimeCurveClassPairing.pairing S hS
      ((schemePicardPullbackHom π).toAdditive p)
      ((schemePicardPullbackHom π).toAdditive q) =
      PrimeCurveClassPairing.pairing X hX p q :=
  picardPairing_pullback π hπ hbir hS hX p.toMul q.toMul

end BirationalPicardIntersectionPullback
end KltDP.Geometry

#check @KltDP.Geometry.BirationalPicardIntersectionPullback.picardPairing_pullback
#print axioms KltDP.Geometry.BirationalPicardIntersectionPullback.picardPairing_pullback
