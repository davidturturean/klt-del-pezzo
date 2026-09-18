import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# An open range makes a closed immersion into a reduced scheme open

The original closed immersion factors through its actual open range.
That factor is a surjective closed immersion into a reduced scheme, so
the pinned closed-immersion criterion makes it an isomorphism. This is
a short adapter of the existing open-immersion lift and closed-immersion
isomorphism theorems; no stalk isomorphism is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- A closed immersion into a reduced scheme, with open actual range, is an open immersion. -/
theorem isOpenImmersion_of_isClosedImmersion_of_open_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [IsReduced Y]
    (hopen : IsOpen (Set.range f.base)) : IsOpenImmersion f := by
  let U : Y.Opens := ⟨Set.range f.base, hopen⟩
  have hr : Set.range f.base ⊆ Set.range U.ι.base := by
    rintro y hy
    exact ⟨⟨y, hy⟩, rfl⟩
  let l := IsOpenImmersion.lift U.ι f hr
  have hfac : l ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hr
  letI : IsClosedImmersion (l ≫ U.ι) := by rw [hfac]; infer_instance
  letI : IsClosedImmersion l := IsClosedImmersion.of_comp l U.ι
  letI : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  letI : Surjective l := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    change (l ≫ U.ι).base x = y.val
    simpa only [hfac] using hx
  letI : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  rw [← hfac]
  infer_instance

end KltDP.Geometry

#print axioms KltDP.Geometry.isOpenImmersion_of_isClosedImmersion_of_open_range
