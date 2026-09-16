import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Open charts of an actual reduced closed image

Suppose a closed immersion into an open chart factors through an actual
reduced closed subscheme, whose support is the closure of its image. The
factorization is an open immersion. The proof uses the actual pullback of
the ambient open chart: its comparison map is a surjective closed immersion
into a reduced scheme, hence an isomorphism by the pinned criterion.

The support and factorization premises concern the original maps. In the
Frobenius application both are supplied by the proved kernel subscheme
construction; no chart isomorphism or stalk identification is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ReducedClosedImageChart

variable {X U Y Z : Scheme.{u}}

/-- A closed subset of an open chart is recovered by pulling its ambient
closure back through the original open immersion. -/
theorem preimage_closure_range (c : X ⟶ U) (j : U ⟶ Y)
    [IsClosedImmersion c] [IsOpenImmersion j] :
    j.base ⁻¹' closure (Set.range (c ≫ j).base) = Set.range c.base := by
  rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous]
  have h : j.base ⁻¹' Set.range (c ≫ j).base = Set.range c.base := by
    ext q
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, j.isOpenEmbedding.injective hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  rw [h, c.isClosedEmbedding.isClosed_range.closure_eq]

/-- The original factorization into its reduced closed image is an open
chart, derived through the actual ambient-open pullback. -/
theorem isOpenImmersion_of_reduced_closed_image
    (c : X ⟶ U) (j : U ⟶ Y) (i : Z ⟶ Y) (f : X ⟶ Z)
    [IsClosedImmersion c] [IsOpenImmersion j] [IsClosedImmersion i] [IsReduced Z]
    (w : f ≫ i = c ≫ j)
    (hr : Set.range i.base = closure (Set.range (c ≫ j).base)) :
    IsOpenImmersion f := by
  let l : X ⟶ pullback i j := pullback.lift f c w
  letI : IsClosedImmersion (pullback.snd i j) :=
    MorphismProperty.pullback_snd (P := @IsClosedImmersion) i j inferInstance
  letI : IsClosedImmersion (l ≫ pullback.snd i j) := by
    change IsClosedImmersion (pullback.lift f c w ≫ pullback.snd i j)
    rw [pullback.lift_snd]
    infer_instance
  letI : IsClosedImmersion l :=
    IsClosedImmersion.of_comp_isClosedImmersion l (pullback.snd i j)
  letI : IsReduced (pullback i j) :=
    isReduced_of_isOpenImmersion (pullback.fst i j)
  letI : Surjective l := by
    constructor
    intro z
    have hz : j.base ((pullback.snd i j).base z) ∈
        closure (Set.range (c ≫ j).base) := by
      rw [← hr]
      exact ⟨(pullback.fst i j).base z,
        congrArg (fun h => h.base z) (pullback.condition (f := i) (g := j))⟩
    have hmem : (pullback.snd i j).base z ∈ Set.range c.base := by
      rw [← preimage_closure_range c j]
      exact hz
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, (pullback.snd i j).isClosedEmbedding.injective ?_⟩
    change (l ≫ pullback.snd i j).base x = (pullback.snd i j).base z
    simpa only [l, pullback.lift_snd] using hx
  letI : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  have hfac : l ≫ pullback.fst i j = f := pullback.lift_fst f c w
  rw [← hfac]
  infer_instance

end KltDP.Geometry.ReducedClosedImageChart
