import KltDP.Geometry.SteinGeometricConnected
import KltDP.Geometry.PushforwardRelativeSpecTrivial

/-!
For an original proper morphism whose canonical pushforward-O map is an
isomorphism, the constructed relative spectrum is the original target.
The full Stein theorem and ordinary target-isomorphism transport therefore
give geometric connectedness of the original morphism itself.
-/

open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.ProperSteinConnected

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsIso f.c]

/-- Every original field-valued base change is connected. -/
theorem geometrically_connected :
    ∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Y),
      ConnectedSpace (pullback f q : Scheme.{u}) := by
  letI : IsIso (PushforwardRelativeSpec.toBase f) :=
    PushforwardRelativeSpec.toBase_isIso_of_c_isIso f
  exact GeometricConnectedFiberIsoTransport.forall_field_pullback_connected_of_target_iso
    (PushforwardRelativeSpec.fromSource f) f (asIso (PushforwardRelativeSpec.toBase f))
    (PushforwardRelativeSpec.fromSource_toBase f)
    (SteinGeometricConnected.fromSource_geometrically_connected f)

/-- The original topological fibers are connected and nonempty. -/
theorem pointFibers_connected (y : Y) : IsConnected (f.base ⁻¹' {y}) :=
  GeometricConnectedFiberTopology.isConnected_preimage_singleton
    f (geometrically_connected f) y

end KltDP.Geometry.ProperSteinConnected
