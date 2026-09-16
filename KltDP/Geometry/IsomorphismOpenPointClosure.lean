import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sober

/-!
# Point closures over an actual isomorphism open

For an actual morphism which is an isomorphism over an open, the closure
of the full inverse image of a generically nonempty closed subset on that
open is the closure of its lifted generic point. This is proved by
reflecting specializations through the actual restricted isomorphism.
No properness, dimension, normality, or source integrality is required.

Reuse: pinned `IsGenericPoint.specializes`, `subtype_specializes_iff`,
`Topology.IsInducing.specializes_iff`, and `morphismRestrict_base_coe`.
The pinned statements suffice, so no newer-library port is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The whole punctured inverse image has precisely the closure of the
actual point lying above the generic point. The only geometric input is
the actual isomorphism of the restricted morphism. -/
theorem closure_preimage_inter_eq_lifted_point_closure
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    {C : Set Y} {η : Y} (hη : IsGenericPoint η C) (hηU : η ∈ U)
    (ξ : X) (hξ : f.base ξ = η) :
    closure (f.base ⁻¹' (C ∩ (U : Set Y))) = closure ({ξ} : Set X) := by
  have hξU : f.base ξ ∈ U := hξ.symm ▸ hηU
  let ξ' : (f ⁻¹ᵁ U).toScheme := ⟨ξ, hξU⟩
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    intro z hz
    let z' : (f ⁻¹ᵁ U).toScheme := ⟨z, hz.2⟩
    have hξmap : ((f ∣_ U).base ξ').val = f.base ξ :=
      morphismRestrict_base_coe f U ξ'
    have hzmap : ((f ∣_ U).base z').val = f.base z :=
      morphismRestrict_base_coe f U z'
    have ht : ((f ∣_ U).base ξ').val ⤳ ((f ∣_ U).base z').val := by
      rw [hξmap, hzmap, hξ]
      exact hη.specializes hz.1
    have ht' : (f ∣_ U).base ξ' ⤳ (f ∣_ U).base z' :=
      (subtype_specializes_iff _ _).mpr ht
    have hs : ξ' ⤳ z' :=
      (f ∣_ U).isOpenEmbedding.isInducing.specializes_iff.mp ht'
    exact ((subtype_specializes_iff ξ' z').mp hs).mem_closure
  · apply closure_mono
    apply Set.singleton_subset_iff.mpr
    exact ⟨hξ.symm ▸ hη.mem, hξU⟩

end KltDP.Geometry
