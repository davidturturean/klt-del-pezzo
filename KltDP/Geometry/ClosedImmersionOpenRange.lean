import KltDP.Geometry.ClosedPartitionUnitTriviality

/-!
# An original closed immersion with open range into a reduced scheme

Expose the geometric argument already used by the closed-partition frame
construction. The lift to the original image open is a surjective closed
immersion into a reduced scheme, hence an isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The original closed immersion is an open immersion when its range is
open and its target reduced. -/
theorem isOpenImmersion_of_closedImmersion_of_openRange
    {Y X : Scheme.{u}} [IsReduced X] (i : Y ⟶ X) [IsClosedImmersion i]
    (hopen : IsOpen (Set.range i.base)) : IsOpenImmersion i := by
  let U : X.Opens := ⟨Set.range i.base, hopen⟩
  let l : Y ⟶ U.toScheme := IsOpenImmersion.lift U.ι i (by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.refl _)
  have hl : l ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (l ≫ U.ι) := by rw [hl]; infer_instance
  letI : IsClosedImmersion l := IsClosedImmersion.of_comp l U.ι
  letI : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  letI : Surjective l := by
    constructor
    intro z
    have hz : U.ι.base z ∈ Set.range i.base := by
      change U.ι.base z ∈ (U : Set X)
      rw [← Scheme.Opens.range_ι]
      exact ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    change (l ≫ U.ι).base y = U.ι.base z
    simpa only [hl] using hy
  letI : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  rw [← hl]
  infer_instance

end KltDP.Geometry
