import KltDP.Geometry.BirationalCartierRestrictionEquality

/-!
# A principal difference on the original isomorphism open

The rational correction on the source open extends through the inverse
of its original function-field isomorphism. Subtracting its actual global
principal Cartier divisor reduces the comparison to exact restriction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalCartierOnIsomorphismOpen

open OpenImmersionRational

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

/-- A principal difference between the actual Cartier restrictions
suffices for equality of the original pushed and extended Weil classes. -/
theorem pushforward_weilClass_of_principal_difference
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D : CartierDivisor S.toScheme) (E : CartierDivisor U.toScheme)
    (g : (π ⁻¹ᵁ U).toScheme.functionFieldˣ)
    (hDE : cartierRestrictionHom (π ⁻¹ᵁ U).ι D - cartierRestrictionHom (π ∣_ U) E =
      principalCartierDivisorHom (π ⁻¹ᵁ U).toScheme (Additive.ofMul g)) :
    BirationalWeilClassPushforward.pushforward π hbir (S.weilClassMap (S.cartierToWeilHom D)) =
      X.weilClassMap (OpenCartierWeil.restrictedWeilHom U E) := by
  let t := Units.map (functionFieldIso (π ⁻¹ᵁ U).ι).inv.hom.toMonoidHom g
  have ht : Units.map (functionFieldIso (π ⁻¹ᵁ U).ι).hom.hom.toMonoidHom t = g := by
    apply Units.ext
    exact Iso.inv_hom_id_apply (functionFieldIso (π ⁻¹ᵁ U).ι)
      (g : (π ⁻¹ᵁ U).toScheme.functionField)
  let P := principalCartierDivisorHom S.toScheme (Additive.ofMul t)
  have hcorrect : cartierRestrictionHom (π ⁻¹ᵁ U).ι (D - P) =
      cartierRestrictionHom (π ∣_ U) E := by
    dsimp only [P]
    rw [map_sub, cartierRestrictionHom_principal, ht]
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hDE).trans (add_comm _ _))
  have hclass : S.weilClassMap (S.cartierToWeilHom (D - P)) =
      S.weilClassMap (S.cartierToWeilHom D) := by
    dsimp only [P]
    rw [map_sub, S.cartierToWeilHom_principal, map_sub,
      S.weilClassMap_principalDivisor, sub_zero]
  calc
    BirationalWeilClassPushforward.pushforward π hbir (S.weilClassMap (S.cartierToWeilHom D)) =
        BirationalWeilClassPushforward.pushforward π hbir
          (S.weilClassMap (S.cartierToWeilHom (D - P))) :=
      congrArg (BirationalWeilClassPushforward.pushforward π hbir) hclass.symm
    _ = X.weilClassMap (OpenCartierWeil.restrictedWeilHom U E) :=
      pushforward_weilClass_of_restriction_eq π hbir U hU (D - P) E hcorrect

end KltDP.Geometry.BirationalCartierOnIsomorphismOpen
