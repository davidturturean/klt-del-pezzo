import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The original exterior differential near a valuation stalk

The actual proper birational morphism is an isomorphism over an open
neighborhood of the chosen valuation stalk. Its original exterior differential,
pulled back to the original inverse-image open, is therefore invertible in
every degree. The original structure triangle and points are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProperBirationalExteriorIsomorphismOpen

attribute [local instance] integralSchemeStalk_isDomain

variable {k : Type u} [CommRing k] {S X : Scheme.{u}}
    [IsIntegral S] [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (q : S ⟶ X)
    [IsProper q] (hbir : IsBirationalScheme q)
    (g : S ⟶ Spec (CommRingCat.of k)) (h : q ≫ f = g)

include hbir

/-- One actual target neighborhood makes the original pulled exterior map
invertible in every degree. No differential comparison is supplied as input. -/
theorem exists_open_at_valuation_stalk
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (q ∣_ U) ∧
      IsOpenImmersion ((q ⁻¹ᵁ U).ι ≫ q) ∧
      ∀ n : ℕ, IsIso ((schemeModulePullback (q ⁻¹ᵁ U).ι).map
        (SchemeKaehlerExteriorPullbackTransport.map f q g h n)) := by
  obtain ⟨U, hxU, hU⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk q hbir x
  letI : IsIso (q ∣_ U) := hU
  letI : IsOpenImmersion ((q ⁻¹ᵁ U).ι ≫ q) := by
    rw [← morphismRestrict_ι q U]
    infer_instance
  refine ⟨U, hxU, hU, inferInstance, ?_⟩
  intro n
  exact SchemeKaehlerExteriorPullbackTransport.pullback_map_isIso_of_open_comp
    f q g h n (q ⁻¹ᵁ U).ι

/-- The same original neighborhood also retains a specified source point.
In particular, the point may be the original detected divisor generic point. -/
theorem exists_open_at_source_point
    (s : S) [ValuationRing (X.presheaf.stalk (q.base s))] :
    ∃ U : X.Opens, q.base s ∈ U ∧ s ∈ q ⁻¹ᵁ U ∧ IsIso (q ∣_ U) ∧
      IsOpenImmersion ((q ⁻¹ᵁ U).ι ≫ q) ∧
      ∀ n : ℕ, IsIso ((schemeModulePullback (q ⁻¹ᵁ U).ι).map
        (SchemeKaehlerExteriorPullbackTransport.map f q g h n)) := by
  obtain ⟨U, hxU, hU, hopen, hmap⟩ :=
    exists_open_at_valuation_stalk f q hbir g h (q.base s)
  exact ⟨U, hxU, hxU, hU, hopen, hmap⟩

end KltDP.Geometry.ProperBirationalExteriorIsomorphismOpen
