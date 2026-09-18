import KltDP.Geometry.CartierModuleIsoOfPicardClass
import KltDP.Geometry.BirationalPrincipalPushforward
import KltDP.Geometry.CartierWeilMap
import KltDP.Geometry.WeilClassGroup
import Mathlib.Tactic.Abel

/-!
A principal correction on the original source realizes an exact target
Weil representative, while preserving the original divisor line sheaf.
The correcting function is pulled back by the original generic-stalk map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

variable {k : Type u} [Field k] {S Y : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ Y.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Equality of pushed Weil classes can be realized by an exact pushed
divisor, without changing the actual source Cartier module up to isomorphism. -/
theorem exists_cartier_representative_with_pushforward
    (D : CartierDivisor S.toScheme) (E : Y.WeilDivisor)
    (h : Y.weilClassMap (pushforward π hbir (S.cartierToWeilHom D)) =
      Y.weilClassMap E) :
    ∃ D' : CartierDivisor S.toScheme,
      pushforward π hbir (S.cartierToWeilHom D') = E ∧
      Nonempty (cartierDivisorModule S.toScheme D' ≅ cartierDivisorModule S.toScheme D) := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨f, hf⟩ := (Y.weilClassMap_eq_iff
    (pushforward π hbir (S.cartierToWeilHom D)) E).mp h
  let g : S.toScheme.functionFieldˣ :=
    Units.map (functionFieldMap π).hom.toMonoidHom f
  let D' : CartierDivisor S.toScheme :=
    D - principalCartierDivisorHom S.toScheme (Additive.ofMul g)
  refine ⟨D', ?_, ?_⟩
  · change pushforward π hbir
      (S.cartierToWeilHom (D - principalCartierDivisorHom S.toScheme (Additive.ofMul g))) = E
    rw [map_sub, map_sub, S.cartierToWeilHom_principal]
    change pushforward π hbir (S.cartierToWeilHom D) -
      pushforward π hbir (S.principalDivisor
        (Units.map (functionFieldMap π).hom.toMonoidHom f)) = E
    rw [pushforward_principalDivisor π hbir f, ← hf]
    abel
  · apply cartierModuleIso_of_picardHom_eq S.toScheme D' D
    dsimp only [D']
    rw [map_sub, cartierPicardHom_principal, sub_zero]

end KltDP.Geometry.BirationalWeilPushforward
