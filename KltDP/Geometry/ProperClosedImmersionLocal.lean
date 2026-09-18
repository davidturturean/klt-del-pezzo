import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Closed immersions from target opens covering the proper image

The target opens need only have preimages covering the original source. The
complement of the closed proper image completes them to a target open cover;
the restriction over that complement has empty source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry.ProperClosedImmersionLocal

/-- Closed-immersion restrictions over target opens covering the image of an
actual proper morphism imply that the original morphism is a closed immersion. -/
theorem of_preimage_iSup_eq_top {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]
    {ι : Type v} (U : ι → Y.Opens) (hcover : (⨆ i, g ⁻¹ᵁ U i) = ⊤)
    (hU : ∀ i, IsClosedImmersion (g ∣_ U i)) : IsClosedImmersion g := by
  classical
  let W : Y.Opens :=
    ⟨(Set.range g.base)ᶜ, g.isClosedMap.isClosed_range.isOpen_compl⟩
  let V : Option ι → Y.Opens := fun j => match j with
    | none => W
    | some i => U i
  have hV : (⨆ j, V j) = ⊤ := by
    apply top_unique
    intro y _
    by_cases hy : y ∈ Set.range g.base
    · obtain ⟨x, rfl⟩ := hy
      have hx : x ∈ ⨆ i, g ⁻¹ᵁ U i := by
        rw [hcover]
        trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      exact Opens.mem_iSup.mpr ⟨some i, hi⟩
    · exact Opens.mem_iSup.mpr ⟨none, hy⟩
  apply IsLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) V hV
  intro j
  cases j with
  | none =>
      change IsClosedImmersion (g ∣_ W)
      letI : IsEmpty (g ⁻¹ᵁ W).toScheme :=
        ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
  | some i => exact hU i

end KltDP.Geometry.ProperClosedImmersionLocal
