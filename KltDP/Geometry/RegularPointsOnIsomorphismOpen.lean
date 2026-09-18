import KltDP.Geometry.RegularLocalEquiv
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Regularity on the actual target open where a morphism is an isomorphism

The original source stalks are regular. The actual open restrictions and
the given restricted isomorphism identify them with the original target
stalks on that open. No assertion is made about points outside the open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RegularPointsOnIsomorphismOpen

/-- Regularity of the original source transports to every target point on
an open over which the original morphism restricts to an isomorphism. -/
theorem regularPoint_of_mem {X Y : Scheme.{u}} (π : X ⟶ Y) (U : Y.Opens)
    [IsIso (π ∣_ U)] (hreg : ∀ x : X, RegularPoint X x) (y : Y) (hy : y ∈ U) :
    RegularPoint Y y := by
  have hs : Function.Surjective (π ∣_ U).base :=
    (Scheme.homeoOfIso (asIso (π ∣_ U))).surjective
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  have hxreg : RegularPoint (π ⁻¹ᵁ U).toScheme x :=
    (regularPoint_iff_of_isOpenImmersion (π ⁻¹ᵁ U).ι x).mpr (hreg x.1)
  have htreg : RegularPoint U.toScheme ((π ∣_ U).base x) :=
    (regularPoint_iff_of_isOpenImmersion (π ∣_ U) x).mp hxreg
  have hyreg : RegularPoint U.toScheme ⟨y, hy⟩ := hx ▸ htreg
  exact (regularPoint_iff_of_isOpenImmersion U.ι ⟨y, hy⟩).mp hyreg

/-- The actual singular locus is contained in the complement of this open. -/
theorem singularLocus_subset_compl {X Y : Scheme.{u}} (π : X ⟶ Y) (U : Y.Opens)
    [IsIso (π ∣_ U)] (hreg : ∀ x : X, RegularPoint X x) :
    singularLocus Y ⊆ (U : Set Y)ᶜ := by
  intro y hy hyU
  exact hy (regularPoint_of_mem π U hreg y hyU)

end KltDP.Geometry.RegularPointsOnIsomorphismOpen
