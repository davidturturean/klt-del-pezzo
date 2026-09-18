import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Connected components from the original connected fibers

Mathlib already constructs the lift of a continuous map to connected
components. If its target is totally disconnected and its original fibers
are connected and nonempty, that very lift is a bijection.
-/

noncomputable section

open Set

universe u v

namespace KltDP.Topology.ConnectedFiberComponentEquiv

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  [TotallyDisconnectedSpace B] (f : A → B) (hf : Continuous f)
  (hfibers : ∀ y : B, IsConnected (f ⁻¹' {y}))

include hfibers in
/-- The pinned connected-component lift is injective because two points
with the same original image lie in one connected fiber. -/
theorem lift_bijective : Function.Bijective hf.connectedComponentsLift := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    apply ConnectedComponents.coe_eq_coe'.mpr
    exact (hfibers (f y)).isPreconnected.subset_connectedComponent
      (show y ∈ f ⁻¹' {f y} from rfl)
      (show x ∈ f ⁻¹' {f y} from hab)
  · intro y
    obtain ⟨x, hx⟩ := (hfibers y).nonempty
    exact ⟨(x : ConnectedComponents A), hx⟩

/-- The equivalence uses the original function, through its proved lift. -/
def equiv : ConnectedComponents A ≃ B :=
  Equiv.ofBijective hf.connectedComponentsLift (lift_bijective f hf hfibers)

@[simp] theorem equiv_apply_coe (x : A) :
    equiv f hf hfibers (x : ConnectedComponents A) = f x := rfl

end KltDP.Topology.ConnectedFiberComponentEquiv
