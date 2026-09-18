import KltDP.Geometry.OpenCartierIntrinsicOrder
import KltDP.Geometry.BirationalWeilClassPushforward

/-!
# Cartier comparison on the actual birational isomorphism open

The coefficient at a target prime is computed at its proved unique source
prime. Both points belong to the original isomorphism opens. Transporting
their intrinsic Cartier orders compares the original finite Weil sums.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalCartierOnIsomorphismOpen

open OpenImmersionRational BirationalPrimeCorrespondence
attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (U : X.toScheme.Opens) [Nonempty U.toScheme] [IsIso (π ∣_ U)]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
local instance : Nonempty (π ⁻¹ᵁ U).toScheme :=
  ⟨(inv (π ∣_ U)).base (Classical.choice (inferInstance : Nonempty U.toScheme))⟩
local instance : Nonempty (π ⁻¹ᵁ U) := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral (π ⁻¹ᵁ U).toScheme :=
  isIntegral_of_isOpenImmersion (π ⁻¹ᵁ U).ι

/-- Equality of the actual Cartier restrictions gives equality of the
original coefficient at every target prime generic point in the open. -/
theorem pushforward_cartierToWeilHom_apply_of_restriction_eq
    (D : CartierDivisor S.toScheme) (E : CartierDivisor U.toScheme)
    (hDE : cartierRestrictionHom (π ⁻¹ᵁ U).ι D = cartierRestrictionHom (π ∣_ U) E)
    (C : X.PrimeCurve) (hC : C.genericPoint ∈ U) :
    BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D) C =
      OpenCartierWeil.restrictedWeilHom U E C := by
  let B := abovePrimeCurve π hbir C
  have hB : π.base B.genericPoint = C.genericPoint :=
    abovePrimeCurve_map_genericPoint π hbir C
  let y : U.toScheme := ⟨C.genericPoint, hC⟩
  let x : (π ⁻¹ᵁ U).toScheme := ⟨B.genericPoint, by
    change π.base B.genericPoint ∈ U
    rw [hB]
    exact hC⟩
  have hxy : (π ∣_ U).base x = y := by
    apply Subtype.ext
    exact (morphismRestrict_base_coe π U x).trans hB
  letI : IsDiscreteValuationRing (S.toScheme.presheaf.stalk B.genericPoint) :=
    B.genericPoint_isDiscreteValuationRing
  letI : IsDiscreteValuationRing (X.toScheme.presheaf.stalk C.genericPoint) :=
    C.genericPoint_isDiscreteValuationRing
  letI : IsDiscreteValuationRing ((π ⁻¹ᵁ U).toScheme.presheaf.stalk x) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion (π ⁻¹ᵁ U).ι x B.genericPoint rfl
  letI : IsDiscreteValuationRing (U.toScheme.presheaf.stalk y) :=
    stalk_isDiscreteValuationRing_of_isOpenImmersion U.ι y C.genericPoint rfl
  change cartierOrderAt S.toScheme D B.genericPoint =
    OpenCartierWeil.restrictedCoefficient U E C
  calc
    cartierOrderAt S.toScheme D B.genericPoint =
        cartierOrderAt (π ⁻¹ᵁ U).toScheme (cartierRestrictionHom (π ⁻¹ᵁ U).ι D) x :=
      (cartierOrderAt_cartierRestrictionHom (π ⁻¹ᵁ U).ι D x B.genericPoint rfl).symm
    _ = cartierOrderAt (π ⁻¹ᵁ U).toScheme (cartierRestrictionHom (π ∣_ U) E) x :=
      congrArg (fun F : CartierDivisor (π ⁻¹ᵁ U).toScheme =>
        cartierOrderAt (π ⁻¹ᵁ U).toScheme F x) hDE
    _ = cartierOrderAt U.toScheme E y :=
      cartierOrderAt_cartierRestrictionHom (π ∣_ U) E x y hxy
    _ = OpenCartierWeil.restrictedCoefficient U E C :=
      (OpenCartierWeil.restrictedCoefficient_eq_cartierOrderAt U E C hC).symm

/-- If the original target open contains every prime generic point,
the preceding actual coefficient equalities identify the finite Weil sums. -/
theorem pushforward_cartierToWeilHom_of_restriction_eq
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D : CartierDivisor S.toScheme) (E : CartierDivisor U.toScheme)
    (hDE : cartierRestrictionHom (π ⁻¹ᵁ U).ι D = cartierRestrictionHom (π ∣_ U) E) :
    BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D) =
      OpenCartierWeil.restrictedWeilHom U E := by
  apply Finsupp.ext
  intro C
  exact pushforward_cartierToWeilHom_apply_of_restriction_eq π hbir U D E hDE C (hU C)

/-- The same actual comparison on the already constructed Weil classes. -/
theorem pushforward_weilClass_of_restriction_eq
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D : CartierDivisor S.toScheme) (E : CartierDivisor U.toScheme)
    (hDE : cartierRestrictionHom (π ⁻¹ᵁ U).ι D = cartierRestrictionHom (π ∣_ U) E) :
    BirationalWeilClassPushforward.pushforward π hbir (S.weilClassMap (S.cartierToWeilHom D)) =
      X.weilClassMap (OpenCartierWeil.restrictedWeilHom U E) := by
  rw [BirationalWeilClassPushforward.pushforward_weilClassMap,
    pushforward_cartierToWeilHom_of_restriction_eq π hbir U hU D E hDE]

end KltDP.Geometry.BirationalCartierOnIsomorphismOpen
