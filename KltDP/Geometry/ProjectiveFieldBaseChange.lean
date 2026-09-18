import KltDP.Geometry.RelativeProjectiveBaseChange
import KltDP.Geometry.ProjectiveOverSeparatedPullback

/-! Actual projective embeddings survive field extension. For a map from
a projective scheme to a separated base, its field-valued fibers inherit
projectivity over their original fields. The embeddings use the proved
coefficient base-change isomorphism of polynomial Proj. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.ProjectiveFieldBaseChange

variable {k l : Type u} [Field k] [Field l] {X Y : Scheme.{u}}

/-- Base change of the original closed projective embedding along a field map. -/
theorem projective_pullback_specMap
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveOverField f)
    (φ : k →+* l) :
    IsProjectiveOverField (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) := by
  obtain ⟨n, i, hi, hif⟩ := hf
  letI : IsClosedImmersion i := hi
  let g := Spec.map (CommRingCat.ofHom φ)
  let j := pullback.map f g (projectiveSpaceToSpec k n) g i (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans hif.symm) (by simp)
  have hj : IsClosedImmersion j :=
    MorphismProperty.pullback_map (P := @IsClosedImmersion)
      hi (by infer_instance) hif.symm (by simp)
  letI : IsClosedImmersion j := hj
  let e : projectiveSpace l n ≅ pullback (projectiveSpaceToSpec k n) g :=
    RelativeProjectiveChart.baseChangeIso n φ
  have he : e.inv ≫ projectiveSpaceToSpec l n = pullback.snd _ _ := by
    apply (cancel_epi e.hom).mp
    simpa only [Iso.hom_inv_id_assoc] using
      (RelativeProjectiveChart.baseChangeIso_hom_snd n φ).symm
  refine ⟨n, j ≫ e.inv, inferInstance, ?_⟩
  rw [Category.assoc, he]
  simp only [j, g, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Field base change expressed using the actual scheme morphism. -/
theorem projective_pullback
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveOverField f)
    (g : Spec (CommRingCat.of l) ⟶ Spec (CommRingCat.of k)) :
    IsProjectiveOverField (pullback.snd f g) := by
  have h := projective_pullback_specMap f hf (Spec.preimage g).hom
  change IsProjectiveOverField (pullback.snd f (Spec.map (Spec.preimage g))) at h
  rwa [Spec.map_preimage] at h

/-- A field-valued fiber of a map from a projective scheme to a separated
base is projective over that original field. -/
theorem projective_fieldFiber
    (f : X ⟶ Y) (σ : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated σ]
    (hf : IsProjectiveOverField (f ≫ σ))
    (q : Spec (CommRingCat.of l) ⟶ Y) :
    IsProjectiveOverField (pullback.snd f q) := by
  have h := ProjectiveOverSeparatedPullback.projective_comp_closedImmersion
    (pullback.mapDesc f q σ) (pullback.snd (f ≫ σ) (q ≫ σ))
    (projective_pullback (f ≫ σ) hf (q ≫ σ))
  simpa only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
    using h

end KltDP.Geometry.ProjectiveFieldBaseChange

#print axioms KltDP.Geometry.ProjectiveFieldBaseChange.projective_pullback
#print axioms KltDP.Geometry.ProjectiveFieldBaseChange.projective_fieldFiber
