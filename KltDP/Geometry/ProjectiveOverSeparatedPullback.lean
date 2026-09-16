import KltDP.Geometry.ProjectiveSegreGeneralRange
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Projective embeddings of fibre products over a separated base

The actual product over the field is projective by the accepted Segre embedding.
For a separated base over that field, pinned Mathlib makes the comparison from
the fibre product over the base to the product over the field a closed immersion.
Composing these embeddings proves projectivity of the former fibre product.
The auxiliary closed-immersion and isomorphism transport statements also preserve
the actual structure morphism in the definition of `IsProjectiveOverField`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ProjectiveOverSeparatedPullback

variable {k : Type u} [Field k]

/-- A closed subscheme of a projective scheme has an actual projective embedding
over the same field. -/
theorem projective_comp_closedImmersion {X Y : Scheme.{u}}
    (ι : X ⟶ Y) [IsClosedImmersion ι] (f : Y ⟶ Spec (CommRingCat.of k))
    (hf : IsProjectiveOverField f) : IsProjectiveOverField (ι ≫ f) := by
  obtain ⟨N, j, hj, hjf⟩ := hf
  letI : IsClosedImmersion j := hj
  refine ⟨N, ι ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hjf]

/-- Projectivity transfers through an actual scheme isomorphism over the field. -/
theorem projective_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (hfg : e.hom ≫ g = f) (hf : IsProjectiveOverField f) :
    IsProjectiveOverField g := by
  have hgf : e.inv ≫ f = g := by
    rw [← hfg, Iso.inv_hom_id_assoc]
  rw [← hgf]
  exact projective_comp_closedImmersion e.inv f hf

/-- Two projective schemes mapping to a separated scheme over the field have
projective fibre product over that scheme. -/
theorem projective_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (σ : S ⟶ Spec (CommRingCat.of k)) [IsSeparated σ]
    (hf : IsProjectiveOverField (f ≫ σ)) (hg : IsProjectiveOverField (g ≫ σ)) :
    IsProjectiveOverField (pullback.fst f g ≫ f ≫ σ) := by
  have hprod := ProjectiveSegreGeneral.isProjectiveOverField_pullback k (f ≫ σ) (g ≫ σ) hf hg
  have h := projective_comp_closedImmersion (pullback.mapDesc f g σ)
    (pullback.fst (f ≫ σ) (g ≫ σ) ≫ f ≫ σ) hprod
  simpa only [pullback.mapDesc, pullback.map, Category.assoc,
    pullback.lift_fst_assoc, Category.comp_id] using h

end KltDP.Geometry.ProjectiveOverSeparatedPullback
