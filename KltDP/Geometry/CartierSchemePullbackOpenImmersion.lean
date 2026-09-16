import KltDP.Geometry.PicardPullbackOpenImmersion
import KltDP.Geometry.CartierOpenRestrictionPicard
import KltDP.Geometry.CartierPicardHom

/-!
# Pullback of O(D) along an open immersion

For an open immersion of integral schemes, the existing Cartier
restriction is constructed from actual rational and regular units.
Its proved module restriction isomorphism, composed with the actual
restriction-to-pullback comparison, identifies the scheme-module
pullback of O(D) with O(D restricted).

The resulting equality uses the existing scheme Picard pullback and
Cartier-to-Picard maps. Cartier pullback along a general scheme morphism
is not asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- Actual scheme-module pullback of O_X(D) is isomorphic to O_Y(D|Y),
for the Cartier restriction already constructed from the unit quotient. -/
def cartierModulePullbackIso (D : CartierDivisor X) :
    (schemeModulePullback f).obj (cartierDivisorModule X D) ≅
      cartierDivisorModule Y (cartierRestrictionHom f D) :=
  ((SchemeModuleRestriction.restrictionIsoPullback f).app
    (cartierDivisorModule X D)).symm ≪≫ cartierModuleRestrictionIso f D

/-- The actual Picard pullback sends the class of O_X(D) to the class
of the actual Cartier restriction. -/
theorem schemePicardPullbackHom_cartierPicardClass (D : CartierDivisor X) :
    schemePicardPullbackHom f (cartierPicardClass X D) =
      cartierPicardClass Y (cartierRestrictionHom f D) := by
  rw [schemePicardPullbackHom_eq_picardRestrictionHom]
  exact picardRestrictionHom_cartierPicardClass f D

/-- Compatibility as equality of the existing multiplicative
Cartier-to-Picard homomorphisms. -/
theorem schemePicardPullbackHom_comp_cartierPicardMulHom :
    (schemePicardPullbackHom f).comp (cartierPicardMulHom X) =
      (cartierPicardMulHom Y).comp
        (AddMonoidHom.toMultiplicative (cartierRestrictionHom f)) := by
  apply MonoidHom.ext
  intro D
  change schemePicardPullbackHom f (cartierPicardClass X D.toAdd) =
    cartierPicardClass Y (cartierRestrictionHom f D.toAdd)
  exact schemePicardPullbackHom_cartierPicardClass f D.toAdd

end KltDP.Geometry.OpenImmersionRational
