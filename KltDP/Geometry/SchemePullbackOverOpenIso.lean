import KltDP.Geometry.SchemePullbackRestrictIso

/-!
# Base changes of morphisms that are isomorphisms over an open

Three generic consequences of `IsIso (h ∣_ W)` for a scheme morphism `h : T ⟶ X` and an open
`W` of `X`, used to lift closed curves of one blowup tower to the multi-centre surface:

* the base change `pullback.snd f g` of a morphism `f` that is an isomorphism over `U` is an
  isomorphism over `g ⁻¹ᵁ U` (the symmetric form of `isIso_pullback_fst_restrict`);
* every point of `W` is in the image of `h`;
* if a morphism `ι : C ⟶ X` has image inside `W`, then the base change `pullback.snd h ι` of
  `h` along `ι` is an isomorphism (`C ×_X T ≅ C`): pasting the fibre-product square of `h ∣_ W`
  with the restriction square of `h` gives a second pullback of the same cospan.

Only pinned Mathlib is used; nothing about the schemes is assumed beyond the stated isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry

variable {S T X : Scheme.{u}}

/-- The base change of a morphism that is an isomorphism over `U` is an isomorphism over the
preimage of `U` in the other factor. -/
theorem isIso_pullback_snd_restrict (f : S ⟶ X) (g : T ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  letI := isIso_pullback_fst_restrict g f U
  rw [← pullbackSymmetry_hom_comp_fst f g, morphismRestrict_comp]
  infer_instance

/-- Every point of an open over which `h` is an isomorphism lies in the image of `h`. -/
theorem subset_range_of_restrict_isIso (h : T ⟶ X) (W : X.Opens) [IsIso (h ∣_ W)] :
    (W : Set X) ⊆ Set.range h.base := by
  intro w hw
  refine ⟨(h ⁻¹ᵁ W).ι.base ((inv (h ∣_ W)).base ⟨w, hw⟩), ?_⟩
  have h1 : ((h ⁻¹ᵁ W).ι ≫ h).base ((inv (h ∣_ W)).base ⟨w, hw⟩) =
      ((h ∣_ W) ≫ W.ι).base ((inv (h ∣_ W)).base ⟨w, hw⟩) := by
    rw [morphismRestrict_ι]
  change ((h ⁻¹ᵁ W).ι ≫ h).base ((inv (h ∣_ W)).base ⟨w, hw⟩) = w
  rw [h1]
  change W.ι.base ((inv (h ∣_ W) ≫ (h ∣_ W)).base ⟨w, hw⟩) = w
  rw [IsIso.inv_hom_id]
  rfl

/-- If `ι` lands in an open over which `h` is an isomorphism, the base change of `h` along `ι`
is an isomorphism. -/
theorem isIso_pullback_snd_of_range_subset (h : T ⟶ X) {C : Scheme.{u}} (ι : C ⟶ X)
    (W : X.Opens) [IsIso (h ∣_ W)] (hr : Set.range ι.base ⊆ Set.range W.ι.base) :
    IsIso (pullback.snd h ι) := by
  let ι' : C ⟶ W.toScheme := IsOpenImmersion.lift W.ι ι hr
  have hι' : ι' ≫ W.ι = ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : IsPullback (pullback.fst (h ∣_ W) ι' ≫ (h ⁻¹ᵁ W).ι) (pullback.snd (h ∣_ W) ι')
      h (ι' ≫ W.ι) :=
    (IsPullback.of_hasPullback (h ∣_ W) ι').paste_horiz (isPullback_morphismRestrict h W).flip
  rw [hι'] at h1
  have h2 := IsPullback.of_hasPullback h ι
  have he : pullback.snd h ι =
      (h2.isoIsPullback _ _ h1).hom ≫ pullback.snd (h ∣_ W) ι' :=
    (h2.isoIsPullback_hom_snd _ _ h1).symm
  rw [he]
  infer_instance

end KltDP.Geometry
