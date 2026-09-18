import KltDP.Geometry.BirationalWeilPushforward
import KltDP.Geometry.DominantCartierPullbackOffSupport
import KltDP.Geometry.DominantCartierPullbackFunctorial

/-!
# The original exceptional Cartier divisor has zero birational pushforward

The unique original prime above a target curve maps to that curve's nonclosed
generic point. It therefore lies outside a Cartier support mapped to a closed
point. The existing original coefficient theorem off the support, applied to
the identity map, gives zero at every surviving prime. No exceptional
coefficient, primality, or multiplicity statement is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalWeilPushforward

open BirationalPrimeCorrespondence

/-- An original effective Cartier divisor supported over a closed point is
killed by the actual proper birational Weil pushforward. -/
theorem pushforward_cartier_eq_zero_of_support_maps_to_closed_point
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (x : X.toScheme) (hx : IsClosed ({x} : Set X.toScheme))
    (hcontract : ∀ z ∈
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).support,
      π.base z = x) :
    pushforward π hbir (S.cartierToWeilHom E) = 0 := by
  apply Finsupp.ext
  intro C
  change S.cartierToWeilHom E (abovePrimeCurve π hbir C) = 0
  have hoff : (abovePrimeCurve π hbir C).genericPoint ∉
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).support := by
    intro hmem
    have heq : C.genericPoint = x :=
      (abovePrimeCurve_map_genericPoint π hbir C).symm.trans (hcontract _ hmem)
    exact C.not_isClosed_singleton_genericPoint (heq.symm ▸ hx)
  have hz := DominantCartierPullback.coefficient_eq_zero_of_not_mem_support
    (𝟙 S.toScheme) E hE (abovePrimeCurve π hbir C) hoff
  simpa only [DominantCartierPullback.pullbackHom_id, AddMonoidHom.id_apply] using hz

/-- Apply the same result to the original exceptional closed immersion,
using its actual kernel ideal and original pointwise contraction map. -/
theorem pushforward_cartier_eq_zero_of_kernel_maps_to_closed_point
    {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    {Z : Scheme.{u}} (i : Z ⟶ S.toScheme) [IsClosedImmersion i]
    (hI : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE = i.ker)
    (x : X.toScheme) (hx : IsClosed ({x} : Set X.toScheme))
    (hi : ∀ z : Z, π.base (i.base z) = x) :
    pushforward π hbir (S.cartierToWeilHom E) = 0 := by
  apply pushforward_cartier_eq_zero_of_support_maps_to_closed_point π hbir E hE x hx
  intro z hz
  rw [hI] at hz
  change z ∈ ((i.ker).support : Set S.toScheme) at hz
  rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] at hz
  obtain ⟨w, rfl⟩ := hz
  exact hi w

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.pushforward_cartier_eq_zero_of_kernel_maps_to_closed_point
#print axioms KltDP.Geometry.BirationalWeilPushforward.pushforward_cartier_eq_zero_of_support_maps_to_closed_point
#print axioms KltDP.Geometry.BirationalWeilPushforward.pushforward_cartier_eq_zero_of_kernel_maps_to_closed_point
