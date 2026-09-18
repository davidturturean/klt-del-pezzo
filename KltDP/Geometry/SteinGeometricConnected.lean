import KltDP.Literature.SteinFactorizationNoetherian
import KltDP.Geometry.GeometricConnectedFiberIsoTransport
import KltDP.Geometry.GeometricConnectedFiberTopology

/-!
The full published existential factorization supplies geometric
connectedness. Its canonical target comparison and ordinary pullback
transport prove the clause for the already constructed original map.
-/

open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.SteinGeometricConnected

variable {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]

/-- Every original field-valued pullback of the constructed source map is connected. -/
theorem fromSource_geometrically_connected :
    ∀ (K : Type u) [Field K]
        (q : Spec (CommRingCat.of K) ⟶ PushforwardRelativeSpec.relativeSpec f),
      ConnectedSpace (pullback (PushforwardRelativeSpec.fromSource f) q : Scheme.{u}) := by
  obtain ⟨T, g, π, _, _, hg, _, _, ⟨e, he, _⟩, _⟩ :=
    KltDP.Literature.Stacks.steinFactorization_noetherian_literal S X f
  exact GeometricConnectedFiberIsoTransport.forall_field_pullback_connected_of_target_iso
    g (PushforwardRelativeSpec.fromSource f) e he hg

/-- The actual underlying point fibers are connected and nonempty. -/
theorem fromSource_pointFibers_connected (y : PushforwardRelativeSpec.relativeSpec f) :
    IsConnected ((PushforwardRelativeSpec.fromSource f).base ⁻¹' {y}) :=
  GeometricConnectedFiberTopology.isConnected_preimage_singleton
    (PushforwardRelativeSpec.fromSource f) (fromSource_geometrically_connected f) y

end KltDP.Geometry.SteinGeometricConnected
