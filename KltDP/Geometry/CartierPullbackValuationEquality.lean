import KltDP.Geometry.DominantCartierPullbackEquations
import KltDP.Geometry.CartierWeilMap

/-!
# Original Cartier pullback orders depend on the original divisorial valuation

Choose one actual local equation at the shared centre. Both original
pullbacks have the corresponding transported equation, and the given
equality on all original rational-function orders identifies their Cartier
orders. The model schemes may be nonproper and nonprojective.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

attribute [local instance] integralSchemeStalk_isDomain

theorem cartierOrderAt_pullback_eq_of_valuation_eq
    {X S V : Scheme.{u}} [IsIntegral X] [IsIntegral S] [IsIntegral V]
    (π : S ⟶ X) (v : V ⟶ X) [GenericPointPreserving π] [GenericPointPreserving v]
    (s : S) (x : V) [IsDiscreteValuationRing (S.presheaf.stalk s)]
    [IsDiscreteValuationRing (V.presheaf.stalk x)]
    (hcenter : π.base s = v.base x)
    (horder : ∀ a : X.functionFieldˣ,
      stalkDivisorOrder S s (Units.map (functionFieldMap π).hom.toMonoidHom a) =
        stalkDivisorOrder V x (Units.map (functionFieldMap v).hom.toMonoidHom a))
    (A : CartierDivisor X) :
    cartierOrderAt S (DominantCartierPullback.pullbackHom π A) s =
      cartierOrderAt V (DominantCartierPullback.pullbackHom v A) x := by
  obtain ⟨a, U, hx, ha⟩ := exists_cartierOrderEquation X A (v.base x)
  letI : Nonempty U := ⟨⟨v.base x, hx⟩⟩
  have hs : s ∈ π ⁻¹ᵁ U := by
    change π.base s ∈ U
    rw [hcenter]
    exact hx
  have hx' : x ∈ v ⁻¹ᵁ U := hx
  letI : Nonempty (π ⁻¹ᵁ U) := ⟨⟨s, hs⟩⟩
  letI : Nonempty (v ⁻¹ᵁ U) := ⟨⟨x, hx'⟩⟩
  rw [cartierOrderAt_eq_of_equation S _ s (π ⁻¹ᵁ U) hs _
      (DominantCartierPullback.pullbackHom_globalEquation_preimage π A U a ha),
    cartierOrderAt_eq_of_equation V _ x (v ⁻¹ᵁ U) hx' _
      (DominantCartierPullback.pullbackHom_globalEquation_preimage v A U a ha)]
  exact horder a

end KltDP.Geometry

#check @KltDP.Geometry.cartierOrderAt_pullback_eq_of_valuation_eq
#print axioms KltDP.Geometry.cartierOrderAt_pullback_eq_of_valuation_eq
