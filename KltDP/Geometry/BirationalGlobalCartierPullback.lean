import KltDP.Geometry.BirationalCartierModuleIso
import KltDP.Geometry.OpenCartierWeilRestriction
import KltDP.Geometry.SchemeModulePullbackSquareCoherence

/-!
# Global Cartier pullback and the original Weil-class pushforward

An actual global divisor-module isomorphism restricts through the original
commuting square of scheme morphisms. The already proved open comparison
then applies, and the target-global Cartier restriction theorem recovers
the original target Weil class.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalPicardPullbackPushforward

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

/-- A global isomorphism with the actual pullback of a target divisor
module gives the expected original Weil-class pushforward. -/
theorem pushforward_cartierWeilClass_of_module_iso
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D : CartierDivisor S.toScheme) (A : CartierDivisor X.toScheme)
    (e : cartierDivisorModule S.toScheme D ≅
      (schemeModulePullback π).obj (cartierDivisorModule X.toScheme A)) :
    BirationalWeilClassPushforward.pushforward π hbir (S.weilClassMap (S.cartierToWeilHom D)) =
      X.weilClassMap (X.cartierToWeilHom A) := by
  let eU :
      (schemeModulePullback (π ⁻¹ᵁ U).ι).obj (cartierDivisorModule S.toScheme D) ≅
        (schemeModulePullback (π ∣_ U)).obj
          (cartierDivisorModule U.toScheme (cartierRestrictionHom U.ι A)) :=
    (schemeModulePullback (π ⁻¹ᵁ U).ι).mapIso e ≪≫
      SchemeModulePullbackSquareCoherence.squareIso U.ι π (π ∣_ U) (π ⁻¹ᵁ U).ι
        (morphismRestrict_ι π U).symm (cartierDivisorModule X.toScheme A) ≪≫
      (schemeModulePullback (π ∣_ U)).mapIso (cartierModulePullbackIso U.ι A)
  exact (BirationalCartierOnIsomorphismOpen.pushforward_weilClass_of_pullback_module_iso
    π hbir U hU D (cartierRestrictionHom U.ι A) eU).trans
      (congrArg X.weilClassMap (OpenCartierWeil.restrictedWeilHom_restriction U hU A))

end KltDP.Geometry.BirationalPicardPullbackPushforward
