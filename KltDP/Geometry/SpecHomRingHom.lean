import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The ring map of a morphism into an affine scheme

For `f : W ⟶ Spec R` the ring map `specHomRingHom f : R ⟶ Γ(W, ⊤)` is `(ΓSpecIso R).inv ≫ f.appTop`
(the scalar map of the accepted `BaseRingCohomology`). The pinned Γ–Spec adjunction gives
`f = W.toSpecΓ ≫ Spec.map (specHomRingHom f)` (`specHom_eq_toSpecΓ`) and the composition rule
`specHomRingHom (f ≫ Spec.map g) = g ≫ specHomRingHom f` (`specHomRingHom_comp_specMap`), so two
morphisms into `Spec R` are compared through their ring maps, without an affine description of `W`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

variable {W : Scheme.{u}} {R : CommRingCat.{u}}

/-- The ring map `R ⟶ Γ(W, ⊤)` of a morphism `W ⟶ Spec R`. -/
def specHomRingHom (f : W ⟶ Spec R) : R ⟶ Γ(W, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/-- Every morphism into an affine scheme is the spectrum of its ring map, precomposed with the
canonical `W ⟶ Spec Γ(W, ⊤)`. -/
theorem specHom_eq_toSpecΓ (f : W ⟶ Spec R) :
    f = W.toSpecΓ ≫ Spec.map (specHomRingHom f) := by
  have h := Scheme.toSpecΓ_naturality f
  rw [← SpecMap_ΓSpecIso_hom] at h
  rw [specHomRingHom, Spec.map_comp, ← Category.assoc, ← h, Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The ring map of a composite with `Spec.map g` is the composite with `g`. -/
theorem specHomRingHom_comp_specMap {S : CommRingCat.{u}} (f : W ⟶ Spec R) (g : S ⟶ R) :
    specHomRingHom (f ≫ Spec.map g) = g ≫ specHomRingHom f := by
  rw [specHomRingHom, specHomRingHom, Scheme.comp_appTop, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Equal composites with `Spec.map`s have equal ring maps. -/
theorem specHomRingHom_congr {R' S : CommRingCat.{u}} {f : W ⟶ Spec R} {f' : W ⟶ Spec R'}
    {g : S ⟶ R} {g' : S ⟶ R'} (h : f ≫ Spec.map g = f' ≫ Spec.map g') :
    g ≫ specHomRingHom f = g' ≫ specHomRingHom f' := by
  rw [← specHomRingHom_comp_specMap, ← specHomRingHom_comp_specMap, h]

end KltDP.Geometry
