import KltDP.Geometry.ProperBirationalCanonicalOpen
import KltDP.Geometry.CanonicalCartierOpenPullback
import KltDP.Geometry.CartierOrderOpenRestriction

/-!
# Restricting a fixed canonical divisor to the original target big open

The divisor is the actual pullback of the given source divisor through
the inverse of the original restricted birational morphism. It equals
the existing Cartier restriction, represents the original target exterior
sheaf via the original differential, and preserves the original local
Cartier orders. The source divisor is never replaced by another choice.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperBirationalCanonicalRestriction

open ProperBirationalCanonicalOpen OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain

private theorem comp_hom_eq_of_iso_eq
    {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞}
    (a : A ⟶ B) (e e' : B ≅ C) (b : A ⟶ C)
    (he : e = e') (hb : a ≫ e'.hom = b) : a ≫ e.hom = b := by
  cases he
  exact hb

variable {S V : Scheme.{u}} [IsIntegral S] [IsIntegral V]
    (q : S ⟶ V) [IsProper q] (hbir : IsBirationalScheme q)

local instance liftOpen : IsOpenImmersion (lift q) := lift_isOpenImmersion q

local instance openGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (e : Y ⟶ Z) [IsOpenImmersion e] : GenericPointPreserving e :=
  ⟨genericPoint_eq_of_isOpenImmersion e⟩

include hbir

/-- The original signed Cartier pullback of the fixed source divisor. -/
def divisor (KS : CartierDivisor S) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    CartierDivisor (targetIsomorphismOpen q).toScheme := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact DominantCartierPullback.pullbackHom (lift q) KS

/-- This is literally the existing Cartier restriction of that same divisor. -/
theorem divisor_eq_restriction (KS : CartierDivisor S) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    divisor q hbir KS = cartierRestrictionHom (lift q) KS := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact congrArg (fun F => F KS)
    (DominantCartierPullback.pullbackHom_eq_cartierRestrictionHom (lift q))

section Canonical

variable {k : Type u} [CommRing k]
    (fS : S ⟶ Spec (CommRingCat.of k)) (fV : V ⟶ Spec (CommRingCat.of k))
    (hq : q ≫ fV = fS) (KS : CartierDivisor S)
    (eKS : cartierDivisorModule S KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior fS 2)

/-- The fixed source canonical identification restricts through the original
open differential to the target's original relative top exterior sheaf. -/
def canonicalIso :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    cartierDivisorModule (targetIsomorphismOpen q).toScheme (divisor q hbir KS) ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior
        ((targetIsomorphismOpen q).ι ≫ fV) 2 := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact CanonicalCartierOpenPullback.canonicalModuleIso (lift q) fS
    ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) KS eKS

private theorem canonicalIso_eq_original :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    canonicalIso q hbir fS fV hq KS eKS =
      CanonicalCartierOpenPullback.canonicalModuleIso (lift q) fS
        ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) KS eKS := rfl

private theorem original_normalization :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    (DominantCartierPullback.modulePullbackIso (lift q) KS).hom ≫
        (CanonicalCartierOpenPullback.canonicalModuleIso (lift q) fS
          ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) KS eKS).hom =
      (schemeModulePullback (lift q)).map eKS.hom ≫
        SchemeKaehlerExteriorPullbackTransport.map fS (lift q)
          ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) 2 := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact CanonicalCartierOpenPullback.canonicalModuleIso_comp (lift q) fS
    ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) KS eKS

/-- The comparison keeps the actual source canonical frame and the original
exterior differential; it is not merely an existence of some module iso. -/
theorem canonicalIso_comp :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    (DominantCartierPullback.modulePullbackIso (lift q) KS).hom ≫
        (canonicalIso q hbir fS fV hq KS eKS).hom =
      (schemeModulePullback (lift q)).map eKS.hom ≫
        SchemeKaehlerExteriorPullbackTransport.map fS (lift q)
          ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) 2 := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact comp_hom_eq_of_iso_eq
    (DominantCartierPullback.modulePullbackIso (lift q) KS).hom
    (canonicalIso q hbir fS fV hq KS eKS)
    (CanonicalCartierOpenPullback.canonicalModuleIso (lift q) fS
      ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) KS eKS)
    ((schemeModulePullback (lift q)).map eKS.hom ≫
      SchemeKaehlerExteriorPullbackTransport.map fS (lift q)
        ((targetIsomorphismOpen q).ι ≫ fV) (structure_eq q fS fV hq) 2)
    (canonicalIso_eq_original q hbir fS fV hq KS eKS)
    (original_normalization q hbir fS fV hq KS eKS)

end Canonical

/-- The constructed target divisor has the exact original source order
at corresponding points; the target DVR is derived from the original map. -/
theorem divisor_orderAt (KS : CartierDivisor S)
    (y : (targetIsomorphismOpen q).toScheme) (s : S)
    (hy : (lift q).base y = s) [IsDiscreteValuationRing (S.presheaf.stalk s)] :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI : IsDiscreteValuationRing
        ((targetIsomorphismOpen q).toScheme.presheaf.stalk y) :=
      stalk_isDiscreteValuationRing_of_isOpenImmersion (lift q) y s hy
    cartierOrderAt (targetIsomorphismOpen q).toScheme (divisor q hbir KS) y =
      cartierOrderAt S KS s := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  letI : IsDiscreteValuationRing
      ((targetIsomorphismOpen q).toScheme.presheaf.stalk y) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion (lift q) y s hy
  change cartierOrderAt (targetIsomorphismOpen q).toScheme (divisor q hbir KS) y = _
  rw [divisor_eq_restriction]
  exact cartierOrderAt_cartierRestrictionHom (lift q) KS y s hy

/-- At any original source DVR point lying over the big open, the coefficient
is transported to its original image without a new equality assumption. -/
theorem divisor_orderAt_source (KS : CartierDivisor S) (s : S)
    [IsDiscreteValuationRing (S.presheaf.stalk s)]
    (hs : q.base s ∈ targetIsomorphismOpen q) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    letI : IsDiscreteValuationRing
        ((targetIsomorphismOpen q).toScheme.presheaf.stalk ⟨q.base s, hs⟩) :=
      stalk_isDiscreteValuationRing_of_isOpenImmersion (lift q) _ s (lift_base q s hs)
    cartierOrderAt (targetIsomorphismOpen q).toScheme (divisor q hbir KS)
        ⟨q.base s, hs⟩ = cartierOrderAt S KS s := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  exact divisor_orderAt q hbir KS ⟨q.base s, hs⟩ s (lift_base q s hs)

end KltDP.Geometry.ProperBirationalCanonicalRestriction
