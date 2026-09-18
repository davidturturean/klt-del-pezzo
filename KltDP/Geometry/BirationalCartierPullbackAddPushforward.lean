import KltDP.Geometry.BirationalExceptionalCartierPushforward
import KltDP.Geometry.BirationalCartierPullbackPushforward

/-!
# Pushforward of the original Cartier pullback plus the exceptional divisor

The original signed Cartier pullback recovers the base Weil divisor under
proper birational pushforward. The actual exceptional Cartier kernel over
a closed point contributes zero, by its original support geometry.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

/-- The literal divisor `π*K+E` has the original base Cartier divisor's Weil
pushforward, with the exceptional contribution derived from its actual kernel. -/
theorem pushforward_cartier_pullback_add_of_kernel_maps_to_closed_point
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (K : CartierDivisor X.toScheme)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    {Z : Scheme.{u}} (i : Z ⟶ S.toScheme) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE = i.ker)
    (x : X.toScheme) (hx : IsClosed ({x} : Set X.toScheme))
    (hi : ∀ z : Z, π.base (i.base z) = x) :
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    pushforward π hbir
      (S.cartierToWeilHom (DominantCartierPullback.pullbackHom π K + E)) =
        X.cartierToWeilHom K := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  have hzero : pushforward π hbir (S.cartierToWeilHom E) = 0 :=
    pushforward_cartier_eq_zero_of_kernel_maps_to_closed_point π hbir E hE i hI x hx hi
  rw [map_add, map_add, pushforward_cartier_pullback π hbir K, hzero, add_zero]

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.pushforward_cartier_pullback_add_of_kernel_maps_to_closed_point
#print axioms KltDP.Geometry.BirationalWeilPushforward.pushforward_cartier_pullback_add_of_kernel_maps_to_closed_point
