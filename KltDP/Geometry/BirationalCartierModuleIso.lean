import KltDP.Geometry.BirationalCartierPrincipalDifference
import KltDP.Geometry.CartierSchemePullbackOpenImmersion
import KltDP.Geometry.CartierPicardKernel

/-!
# An actual line-sheaf isomorphism gives the Weil-class comparison

The original scheme-module pullbacks of the two divisor modules are
compared on the original isomorphism open. Existing Cartier pullback
isomorphisms and the proved Picard kernel give an actual principal
difference there; the original Weil-class comparison follows.
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

/-- An isomorphism of the actual divisor-module pullbacks on the
original birational isomorphism open gives the original Weil-class
comparison, without a Cartier or principal-compatibility premise. -/
theorem pushforward_weilClass_of_pullback_module_iso
    (hU : ∀ C : X.PrimeCurve, C.genericPoint ∈ U)
    (D : CartierDivisor S.toScheme) (E : CartierDivisor U.toScheme)
    (e : (schemeModulePullback (π ⁻¹ᵁ U).ι).obj (cartierDivisorModule S.toScheme D) ≅
      (schemeModulePullback (π ∣_ U)).obj (cartierDivisorModule U.toScheme E)) :
    BirationalWeilClassPushforward.pushforward π hbir (S.weilClassMap (S.cartierToWeilHom D)) =
      X.weilClassMap (OpenCartierWeil.restrictedWeilHom U E) := by
  let A := cartierRestrictionHom (π ⁻¹ᵁ U).ι D
  let B := cartierRestrictionHom (π ∣_ U) E
  have e' : cartierDivisorModule (π ⁻¹ᵁ U).toScheme A ≅
      cartierDivisorModule (π ⁻¹ᵁ U).toScheme B :=
    (cartierModulePullbackIso (π ⁻¹ᵁ U).ι D).symm ≪≫ e ≪≫
      cartierModulePullbackIso (π ∣_ U) E
  have hPic := cartierPicardClass_eq_of_iso (π ⁻¹ᵁ U).toScheme A B e'
  have hzero : cartierPicardClass (π ⁻¹ᵁ U).toScheme (A - B) = 1 := by
    rw [cartierPicardClass_sub, hPic, div_self']
  obtain ⟨g, hg⟩ := (cartierPicardClass_eq_one_iff (π ⁻¹ᵁ U).toScheme (A - B)).mp hzero
  exact pushforward_weilClass_of_principal_difference π hbir U hU D E g hg

end KltDP.Geometry.BirationalCartierOnIsomorphismOpen
