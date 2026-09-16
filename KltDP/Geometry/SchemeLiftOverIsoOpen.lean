import KltDP.Geometry.SchemePullbackOverOpenIso

/-!
# Lifting a morphism through an isomorphism over an open

Let `h : S ⟶ X` be a scheme morphism which is an isomorphism over an open `V ⊆ X`
(`IsIso (h ∣_ V)`), and let `f : Z ⟶ X` land inside `V`. Then `f` lifts uniquely to `S`:
`liftOverIso h V f hf := lift_V f ≫ inv (h ∣_ V) ≫ (h ⁻¹ᵁ V).ι`. The lift is a literal pullback
of `f` along `h` with identity second leg, and its image lies in `h ⁻¹ᵁ V`.

This is the generic form of the stage-lift construction used for unaffected fibres; here `h` is
arbitrary (in the application, the projection of the multi-centre surface to the projective
product). Only pinned Mathlib is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry

variable {S X Z : Scheme.{u}} (h : S ⟶ X) (V : X.Opens) [IsIso (h ∣_ V)]
  (f : Z ⟶ X) (hf : Set.range f.base ⊆ Set.range V.ι.base)

/-- The actual restriction pullback determines a lift over an isomorphism open. -/
theorem eq_lift_over_restrict_iso' {Y W : Scheme.{u}} (g : Y ⟶ X) [IsIso (g ∣_ V)]
    (t : W ⟶ Y) (q : W ⟶ V.toScheme) (w : q ≫ V.ι = t ≫ g) :
    t = q ≫ inv (g ∣_ V) ≫ (g ⁻¹ᵁ V).ι := by
  let H := isPullback_morphismRestrict g V
  let l := H.lift q t w
  have hl : l = q ≫ inv (g ∣_ V) := by
    apply (cancel_mono (g ∣_ V)).mp
    change H.lift q t w ≫ (g ∣_ V) = (q ≫ inv (g ∣_ V)) ≫ (g ∣_ V)
    rw [H.lift_fst, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    t = l ≫ (g ⁻¹ᵁ V).ι := (H.lift_snd q t w).symm
    _ = q ≫ inv (g ∣_ V) ≫ (g ⁻¹ᵁ V).ι := by rw [hl, Category.assoc]

/-- The lift of `f` to `S` through the isomorphism over `V`. -/
def liftOverIso : Z ⟶ S :=
  IsOpenImmersion.lift V.ι f hf ≫ inv (h ∣_ V) ≫ (h ⁻¹ᵁ V).ι

@[reassoc] theorem liftOverIso_comp : liftOverIso h V f hf ≫ h = f := by
  rw [liftOverIso, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    IsOpenImmersion.lift_fac]

/-- Uniqueness of morphisms over `f`. -/
theorem liftOverIso_eq_of_projection {W : Scheme.{u}} (t : W ⟶ S) (q : W ⟶ Z)
    (w : t ≫ h = q ≫ f) : t = q ≫ liftOverIso h V f hf := by
  have hw : (q ≫ IsOpenImmersion.lift V.ι f hf) ≫ V.ι = t ≫ h := by
    rw [Category.assoc, IsOpenImmersion.lift_fac]
    exact w.symm
  have he := eq_lift_over_restrict_iso' V h t (q ≫ IsOpenImmersion.lift V.ι f hf) hw
  rw [liftOverIso]
  simpa only [Category.assoc] using he

/-- The lift is the literal scheme-theoretic inverse image of `f` under `h`. -/
theorem liftOverIso_isPullback : IsPullback (liftOverIso h V f hf) (𝟙 Z) h f := by
  have w : liftOverIso h V f hf ≫ h = (𝟙 Z) ≫ f := by
    rw [liftOverIso_comp, Category.id_comp]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w (fun s => s.snd)
    (fun s => (liftOverIso_eq_of_projection h V f hf s.fst s.snd s.condition).symm)
    (fun s => Category.comp_id s.snd)
    (fun s m _ hm => by simpa only [Category.comp_id] using hm))

/-- The lift lands in the open over which `h` is an isomorphism. -/
theorem liftOverIso_mem (z : Z) : (liftOverIso h V f hf).base z ∈ h ⁻¹ᵁ V := by
  change h.base ((liftOverIso h V f hf).base z) ∈ V
  have hz : h.base ((liftOverIso h V f hf).base z) = f.base z := by
    change (liftOverIso h V f hf ≫ h).base z = f.base z
    rw [liftOverIso_comp]
  rw [hz]
  obtain ⟨w, hw⟩ := hf ⟨z, rfl⟩
  rw [← hw]
  exact w.2

end KltDP.Geometry
