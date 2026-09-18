import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Topology.Connected.Basic

/-!
The all-field geometric connectedness condition applies to each original
residue field. The pinned original fiber homeomorphism then gives
connectedness of the actual topological fiber, including nonemptiness.
-/

open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.GeometricConnectedFiberTopology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Y),
      ConnectedSpace (pullback f q : Scheme.{u}))

include hf

/-- The original scheme-theoretic fiber is connected at every point. -/
theorem connectedSpace_fiber (y : Y) : ConnectedSpace (f.fiber y) :=
  hf (Y.residueField y) (Y.fromSpecResidueField y)

/-- The original underlying point fiber is connected and nonempty. -/
theorem isConnected_preimage_singleton (y : Y) :
    IsConnected (f.base ⁻¹' {y}) := by
  letI : ConnectedSpace (f.fiber y) := connectedSpace_fiber f hf y
  apply isConnected_iff_connectedSpace.mpr
  exact (f.fiberHomeo y).surjective.connectedSpace (f.fiberHomeo y).continuous

end KltDP.Geometry.GeometricConnectedFiberTopology
