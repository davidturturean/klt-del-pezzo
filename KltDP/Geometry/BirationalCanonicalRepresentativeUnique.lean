import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.BirationalPrincipalRigidity

/-!
# Uniqueness of an actual canonical Cartier representative

Two Cartier divisors representing the same original second exterior sheaf
differ by an actual principal Cartier divisor. If their original proper
birational Weil pushforwards agree, principal pushforward rigidity and normal
Cartier-to-Weil injectivity make that difference zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.BirationalCanonicalRepresentative

/-- The original exterior-square sheaf and the exact original Weil pushforward
determine the source Cartier divisor uniquely. -/
theorem eq_of_exterior_iso_of_pushforward_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hbir : IsBirationalScheme π)
    (D E : CartierDivisor S.toScheme)
    (eD : cartierDivisorModule S.toScheme D ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (eE : cartierDivisorModule S.toScheme E ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (hpush : BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom D) =
      BirationalWeilPushforward.pushforward π hbir (S.cartierToWeilHom E)) :
    D = E := by
  obtain ⟨q, hq⟩ := SmoothCanonicalCartierExterior.exterior_choices_principal
    S.structureMorphism 2 D E eD eE
  have hWeil : S.cartierToWeilHom (D - E) = S.principalDivisor q :=
    (congrArg S.cartierToWeilHom hq).trans (S.cartierToWeilHom_principal q)
  have hpushzero :
      BirationalWeilPushforward.pushforward π hbir (S.principalDivisor q) = 0 := by
    rw [← hWeil, map_sub, map_sub, hpush, sub_self]
  have hprincipal : S.principalDivisor q = 0 :=
    BirationalWeilPushforward.principalDivisor_eq_zero_of_pushforward_eq_zero
      π hbir q hpushzero
  have hzero : S.cartierToWeilHom (D - E) = 0 := hWeil.trans hprincipal
  exact sub_eq_zero.mp ((S.cartierToWeilHom_eq_zero_iff (D - E)).mp hzero)

end KltDP.Geometry.BirationalCanonicalRepresentative

#check @KltDP.Geometry.BirationalCanonicalRepresentative.eq_of_exterior_iso_of_pushforward_eq
#print axioms KltDP.Geometry.BirationalCanonicalRepresentative.eq_of_exterior_iso_of_pushforward_eq
