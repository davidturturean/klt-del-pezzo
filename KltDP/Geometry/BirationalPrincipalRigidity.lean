import KltDP.Geometry.BirationalPrincipalPushforwardSource
import KltDP.Geometry.NormalCartierWeilInjective
import KltDP.Geometry.DominantCartierPullback

/-!
# Original principal divisors are detected by birational pushforward

The inverse of the original function-field map gives the target function
whose principal divisor is the original pushforward. Normal target
Cartier-to-Weil injectivity makes its principal Cartier divisor zero.
Actual signed Cartier pullback and its original principal formula then
make the original source principal divisor zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- A principal divisor with zero original proper birational pushforward
is itself zero, without a target regularity assumption. -/
theorem principalDivisor_eq_zero_of_pushforward_eq_zero
    (f : S.toScheme.functionFieldˣ)
    (hf : pushforward π hbir (S.principalDivisor f) = 0) :
    S.principalDivisor f = 0 := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  letI : IsIso (functionFieldMap π) :=
    (BirationalFunctionField.isBirationalScheme_iff_functionFieldMap_isIso π).mp hbir
  let g := Units.map (asIso (functionFieldMap π)).inv.hom.toMonoidHom f
  have hunit : Units.map (functionFieldMap π).hom.toMonoidHom g = f := by
    apply Units.ext
    exact Iso.inv_hom_id_apply (asIso (functionFieldMap π)) (f : S.toScheme.functionField)
  have hg : X.principalDivisor g = 0 :=
    (pushforward_principalDivisor_source π hbir f).symm.trans hf
  have hcartier : principalCartierDivisorHom X.toScheme (Additive.ofMul g) = 0 :=
    (X.cartierToWeilHom_eq_zero_iff _).mp ((X.cartierToWeilHom_principal g).trans hg)
  calc
    S.principalDivisor f = S.cartierToWeilHom
        (DominantCartierPullback.pullbackHom π
          (principalCartierDivisorHom X.toScheme (Additive.ofMul g))) := by
      rw [DominantCartierPullback.pullbackHom_principal, hunit,
        S.cartierToWeilHom_principal]
    _ = 0 := by rw [hcartier, map_zero, map_zero]

/-- Original pushforward is injective on actual principal divisors. -/
theorem principalDivisor_eq_of_pushforward_eq
    (f g : S.toScheme.functionFieldˣ)
    (hfg : pushforward π hbir (S.principalDivisor f) =
      pushforward π hbir (S.principalDivisor g)) :
    S.principalDivisor f = S.principalDivisor g := by
  have hratio : S.principalDivisor (f * g⁻¹) =
      S.principalDivisor f - S.principalDivisor g := by
    rw [S.principalDivisor_mul, S.principalDivisor_inv, sub_eq_add_neg]
  have hzero : pushforward π hbir (S.principalDivisor (f * g⁻¹)) = 0 := by
    rw [hratio, map_sub, hfg, sub_self]
  exact sub_eq_zero.mp (hratio.symm.trans
    (principalDivisor_eq_zero_of_pushforward_eq_zero π hbir (f * g⁻¹) hzero))

end KltDP.Geometry.BirationalWeilPushforward
