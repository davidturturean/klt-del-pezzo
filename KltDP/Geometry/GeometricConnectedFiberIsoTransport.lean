import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Connected.Basic

/-!
# Geometric connectedness under an isomorphism of the original target

The comparison uses the identity on the original source and on each test
scheme. Only the target is changed by the given scheme isomorphism.
Connectedness then passes through the actual pullback homeomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.GeometricConnectedFiberIsoTransport

/-- The actual pullbacks before and after the target isomorphism, retaining
the original source and the original test scheme. -/
def pullbackTargetIso {X T Y S : Scheme.{u}}
    (f : X ⟶ T) (g : X ⟶ Y) (e : T ≅ Y) (h : f ≫ e.hom = g)
    (q : S ⟶ Y) : pullback f (q ≫ e.inv) ≅ pullback g q :=
  asIso (pullback.map f (q ≫ e.inv) g q (𝟙 X) (𝟙 S) e.hom
    (by simpa only [Category.id_comp] using h)
    (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]))

/-- Connectedness of the original pullback is preserved by that comparison. -/
theorem connectedSpace_pullback_of_target_iso {X T Y S : Scheme.{u}}
    (f : X ⟶ T) (g : X ⟶ Y) (e : T ≅ Y) (h : f ≫ e.hom = g)
    (q : S ⟶ Y) [ConnectedSpace (pullback f (q ≫ e.inv) : Scheme.{u})] :
    ConnectedSpace (pullback g q : Scheme.{u}) := by
  let c := Scheme.homeoOfIso (pullbackTargetIso f g e h q)
  exact c.surjective.connectedSpace c.continuous

/-- The original all-field pullback condition transports to the isomorphic
target without changing the source, the field, or the meaning of connectedness. -/
theorem forall_field_pullback_connected_of_target_iso {X T Y : Scheme.{u}}
    (f : X ⟶ T) (g : X ⟶ Y) (e : T ≅ Y) (h : f ≫ e.hom = g)
    (hf : ∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ T),
      ConnectedSpace (pullback f q : Scheme.{u})) :
    ∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Y),
      ConnectedSpace (pullback g q : Scheme.{u}) := by
  intro K _ q
  letI : ConnectedSpace (pullback f (q ≫ e.inv) : Scheme.{u}) := hf K (q ≫ e.inv)
  exact connectedSpace_pullback_of_target_iso f g e h q

end KltDP.Geometry.GeometricConnectedFiberIsoTransport
