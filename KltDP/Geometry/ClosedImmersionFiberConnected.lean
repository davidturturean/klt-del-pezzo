import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Connected.Basic

/-!
An original point fiber contained in the range of a closed immersion
remains connected in that closed subscheme. For all restricted point
fibers, exhaustion is needed only at points of the actual restricted
image: the other restricted fibers are empty and hence preconnected.
-/

open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ClosedImmersionFiberConnected

variable {E X Y : Scheme.{u}} (ι : E ⟶ X) [IsClosedImmersion ι]
  (f : X ⟶ Y)

/-- The lifted original fiber maps onto the whole original fiber when
that fiber is contained in the actual closed-subscheme range. -/
theorem image_pointFiber_eq (y : Y)
    (hcover : f.base ⁻¹' {y} ⊆ Set.range ι.base) :
    ι.base '' ((ι ≫ f).base ⁻¹' {y}) = f.base ⁻¹' {y} := by
  change ι.base '' (ι.base ⁻¹' (f.base ⁻¹' {y})) = f.base ⁻¹' {y}
  exact Set.image_preimage_eq_of_subset hcover

/-- Connectedness transports through the original closed immersion. -/
theorem pointFiber_isConnected (y : Y)
    (hcover : f.base ⁻¹' {y} ⊆ Set.range ι.base)
    (hconnected : IsConnected (f.base ⁻¹' {y})) :
    IsConnected ((ι ≫ f).base ⁻¹' {y}) := by
  change IsConnected (ι.base ⁻¹' (f.base ⁻¹' {y}))
  exact hconnected.preimage_of_isClosedMap
    ι.isClosedEmbedding.injective ι.isClosedEmbedding.isClosedMap hcover

/-- Exhaustion at actual image points suffices for preconnectedness of
every original restricted point fiber, including the empty ones. -/
theorem all_pointFibers_isPreconnected
    (hcover : ∀ y ∈ Set.range (ι ≫ f).base,
      f.base ⁻¹' {y} ⊆ Set.range ι.base)
    (hconnected : ∀ y : Y, IsConnected (f.base ⁻¹' {y})) :
    ∀ y : Y, IsPreconnected ((ι ≫ f).base ⁻¹' {y}) := by
  intro y
  by_cases hy : y ∈ Set.range (ι ≫ f).base
  · exact (pointFiber_isConnected ι f y (hcover y hy) (hconnected y)).isPreconnected
  · have hempty : (ι ≫ f).base ⁻¹' {y} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro z hz
      exact hy ⟨z, hz⟩
    rw [hempty]
    exact isPreconnected_empty

end KltDP.Geometry.ClosedImmersionFiberConnected
