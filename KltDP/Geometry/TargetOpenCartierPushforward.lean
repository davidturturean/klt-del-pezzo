import KltDP.Geometry.ProperBirationalCanonicalRestriction
import KltDP.Geometry.OpenCartierIntrinsicOrder
import KltDP.Geometry.BirationalWeilPushforward

/-!
# The actual target-open Cartier extension is the original Weil pushforward

On the original target isomorphism open, the inverse restriction pulls
back the given source Cartier divisor. Its extended coefficient at each
target prime is the original source coefficient at the unique prime above
it. This identifies the two actual Weil divisors, for every Cartier divisor;
no canonical or smoothness hypothesis is required.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.TargetOpenCartierPushforward

open OpenImmersionRational BirationalPrimeCorrespondence
open ProperBirationalCanonicalOpen ProperBirationalCanonicalRestriction

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (q : S.toScheme ⟶ X.toScheme) [IsProper q] (hbir : IsBirationalScheme q)

include hbir in
/-- Every original target prime lies in the original isomorphism open. -/
theorem prime_genericPoint_mem (C : X.PrimeCurve) :
    C.genericPoint ∈ targetIsomorphismOpen q :=
  ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve X q hbir C

/-- The coefficient of the actual open Cartier extension is the original
Cartier coefficient at the actual prime above the target prime. -/
theorem restrictedWeilHom_apply_eq (KS : CartierDivisor S.toScheme) (C : X.PrimeCurve) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    OpenCartierWeil.restrictedWeilHom (targetIsomorphismOpen q) (divisor q hbir KS) C =
      S.cartierToWeilHom KS (abovePrimeCurve q hbir C) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  let D := abovePrimeCurve q hbir C
  letI : IsDiscreteValuationRing (S.toScheme.presheaf.stalk D.genericPoint) :=
    D.genericPoint_isDiscreteValuationRing
  letI : IsDiscreteValuationRing (X.toScheme.presheaf.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  have hC := prime_genericPoint_mem q hbir C
  let y : (targetIsomorphismOpen q).toScheme := ⟨C.genericPoint, hC⟩
  letI : IsDiscreteValuationRing
      ((targetIsomorphismOpen q).toScheme.presheaf.stalk y) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion
      (targetIsomorphismOpen q).ι y C.genericPoint rfl
  have hD : q.base D.genericPoint = C.genericPoint :=
    abovePrimeCurve_map_genericPoint q hbir C
  have hs : q.base D.genericPoint ∈ targetIsomorphismOpen q := by
    rw [hD]
    exact hC
  have hp : (⟨q.base D.genericPoint, hs⟩ : (targetIsomorphismOpen q).toScheme) = y :=
    Subtype.ext hD
  have hlift : (lift q).base y = D.genericPoint := by
    simpa only [hp] using lift_base q D.genericPoint hs
  rw [OpenCartierWeil.restrictedWeilHom_apply,
    OpenCartierWeil.restrictedCoefficient_eq_cartierOrderAt
      (targetIsomorphismOpen q) (divisor q hbir KS) C hC]
  exact divisor_orderAt q hbir KS y D.genericPoint hlift

/-- Extending the actual inverse-open Cartier pullback to the target Weil
divisor gives exactly the original proper birational Weil pushforward. -/
theorem restrictedWeilHom_eq_pushforward (KS : CartierDivisor S.toScheme) :
    letI := ProperBirationalCanonicalOpen.isIntegral q hbir
    OpenCartierWeil.restrictedWeilHom (targetIsomorphismOpen q) (divisor q hbir KS) =
      BirationalWeilPushforward.pushforward q hbir (S.cartierToWeilHom KS) := by
  letI := ProperBirationalCanonicalOpen.isIntegral q hbir
  apply Finsupp.ext
  intro C
  simpa only [BirationalWeilPushforward.pushforward_apply] using
    restrictedWeilHom_apply_eq q hbir KS C

end KltDP.Geometry.TargetOpenCartierPushforward
