import KltDP.Geometry.TargetOpenCartierPushforward
import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback

/-!
# The normalized canonical identification on the actual target isomorphism open

The divisor is the existing signed Cartier pullback through the inverse of
the original birational restriction. Its canonical identification uses the
original-coordinate-normalized open pullback and the literal exterior
differential. Its extended Weil divisor is the original Weil pushforward.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.TargetOpenCanonicalCoordinate

open ProperBirationalCanonicalOpen ProperBirationalCanonicalRestriction
open CartierRationalCoordinate

section Generic

variable {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (q : S ⟶ X) [IsProper q] (hbir : IsBirationalScheme q)
    {k : Type u} [CommRing k]
    (fS : S ⟶ Spec (CommRingCat.of k)) (fX : X ⟶ Spec (CommRingCat.of k))
    (hq : q ≫ fX = fS) (KS : CartierDivisor S)
    (eKS : cartierDivisorModule S KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fS 2)

local instance liftOpen : IsOpenImmersion (lift q) := lift_isOpenImmersion q

/-- This is the new normalized identification on the existing source-induced
Cartier divisor, using the actual inverse restriction and exterior differential. -/
def canonicalIso :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    cartierDivisorModule (targetIsomorphismOpen q).toScheme (divisor q hbir KS) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        ((targetIsomorphismOpen q).ι ≫ fX) 2 := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact canonicalOpenPullbackIso (lift q) fS
    ((targetIsomorphismOpen q).ι ≫ fX) (structure_eq q fS fX hq) KS eKS

/-- The literal original differential carries the source coordinate to the
coordinate of this very identification through the original rational pullback. -/
theorem canonicalIso_coordinate :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    SchemeKaehlerExteriorPullbackTransport.map fS (lift q)
        ((targetIsomorphismOpen q).ι ≫ fX) (structure_eq q fS fX hq) 2 ≫
      coordinate (targetIsomorphismOpen q).toScheme (divisor q hbir KS)
        (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          ((targetIsomorphismOpen q).ι ≫ fX) 2)
        (canonicalIso q hbir fS fX hq KS eKS) =
      (schemeModulePullback (lift q)).map
        (coordinate S KS
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior fS 2) eKS) ≫
        (OpenImmersionRational.rationalModulePullbackIso (lift q)).hom := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact map_comp_coordinate_canonicalOpenPullbackIso (lift q) fS
    ((targetIsomorphismOpen q).ι ≫ fX) (structure_eq q fS fX hq) KS eKS

end Generic

/-- On the actual target isomorphism open, the fixed source divisor has one
constructed canonical identification with both its exact Weil pushforward and
its original rational-coordinate square. No canonical-choice scalar is an input. -/
theorem exists_canonicalIso_and_pushforward
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (q : S.toScheme ⟶ X.toScheme) [IsProper q] (hbir : IsBirationalScheme q)
    (hq : q ≫ X.structureMorphism = S.structureMorphism)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI := lift_isOpenImmersion q
    ∃ eU : cartierDivisorModule (targetIsomorphismOpen q).toScheme (divisor q hbir KS) ≅
        SmoothCanonicalExteriorComparison.relativeDifferentialExterior
          ((targetIsomorphismOpen q).ι ≫ X.structureMorphism) 2,
      OpenCartierWeil.restrictedWeilHom (targetIsomorphismOpen q) (divisor q hbir KS) =
          BirationalWeilPushforward.pushforward q hbir (S.cartierToWeilHom KS) ∧
      SchemeKaehlerExteriorPullbackTransport.map S.structureMorphism (lift q)
          ((targetIsomorphismOpen q).ι ≫ X.structureMorphism)
          (structure_eq q S.structureMorphism X.structureMorphism hq) 2 ≫
        coordinate (targetIsomorphismOpen q).toScheme (divisor q hbir KS)
          (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
            ((targetIsomorphismOpen q).ι ≫ X.structureMorphism) 2) eU =
        (schemeModulePullback (lift q)).map
          (coordinate S.toScheme KS
            (SmoothCanonicalExteriorComparison.relativeDifferentialExterior
              S.structureMorphism 2) eKS) ≫
          (OpenImmersionRational.rationalModulePullbackIso (lift q)).hom := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI := lift_isOpenImmersion q
  exact ⟨canonicalIso q hbir S.structureMorphism X.structureMorphism hq KS eKS,
    TargetOpenCartierPushforward.restrictedWeilHom_eq_pushforward q hbir KS,
    canonicalIso_coordinate q hbir S.structureMorphism X.structureMorphism hq KS eKS⟩

end KltDP.Geometry.TargetOpenCanonicalCoordinate

#check @KltDP.Geometry.TargetOpenCanonicalCoordinate.canonicalIso_coordinate
#print axioms KltDP.Geometry.TargetOpenCanonicalCoordinate.canonicalIso_coordinate
#check @KltDP.Geometry.TargetOpenCanonicalCoordinate.exists_canonicalIso_and_pushforward
#print axioms KltDP.Geometry.TargetOpenCanonicalCoordinate.exists_canonicalIso_and_pushforward
