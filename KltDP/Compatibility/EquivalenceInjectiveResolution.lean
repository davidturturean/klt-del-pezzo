import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injective resolutions transported through an additive equivalence

The transported resolution uses the image of the original cochain complex and
augmentation. Its maps are the images of the original maps of complexes.
The degree-zero compatibility equation is the one consumed by the pinned
`InjectiveResolution.isoRightDerivedObj_hom_naturality` theorem.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.InjectiveResolution

open CategoryTheory HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The image of an injective resolution under an additive equivalence. -/
def mapEquivalence (e : C ≌ D) [e.functor.Additive] {X : C}
    (R : InjectiveResolution X) : InjectiveResolution (e.functor.obj X) where
  cocomplex := (e.functor.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  injective n := e.functor.injective_obj (R.cocomplex.X n)
  hasHomology i := by infer_instance
  ι := (singleMapHomologicalComplex e.functor (.up ℕ) 0).inv.app X ≫
    (e.functor.mapHomologicalComplex (.up ℕ)).map R.ι
  quasiIso := by infer_instance

variable (e : C ≌ D) [e.functor.Additive] {X X' : C}
  (R : InjectiveResolution X) (R' : InjectiveResolution X')

@[simp]
lemma mapEquivalence_X (n : ℕ) :
    (mapEquivalence e R).cocomplex.X n = e.functor.obj (R.cocomplex.X n) := rfl

@[simp]
lemma mapEquivalence_d (i j : ℕ) :
    (mapEquivalence e R).cocomplex.d i j = e.functor.map (R.cocomplex.d i j) := rfl

lemma mapEquivalence_ι :
    (mapEquivalence e R).ι =
      (singleMapHomologicalComplex e.functor (.up ℕ) 0).inv.app X ≫
        (e.functor.mapHomologicalComplex (.up ℕ)).map R.ι := rfl

@[simp]
lemma mapEquivalence_ι_f_zero :
    (mapEquivalence e R).ι.f 0 = e.functor.map (R.ι.f 0) := by
  simp [mapEquivalence, singleMapHomologicalComplex_inv_app_self]

/-- The image of the original map of resolution complexes. -/
def mapEquivalenceHom (φ : R.cocomplex ⟶ R'.cocomplex) :
    (mapEquivalence e R).cocomplex ⟶ (mapEquivalence e R').cocomplex :=
  (e.functor.mapHomologicalComplex (.up ℕ)).map φ

@[simp]
lemma mapEquivalenceHom_f (φ : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    (mapEquivalenceHom e R R' φ).f n = e.functor.map (φ.f n) := rfl

/-- A coefficient-map lift retains its original degree-zero compatibility. -/
lemma mapEquivalenceHom_commutes_zero (f : X ⟶ X')
    (φ : R.cocomplex ⟶ R'.cocomplex)
    (hφ : R.ι.f 0 ≫ φ.f 0 = f ≫ R'.ι.f 0) :
    (mapEquivalence e R).ι.f 0 ≫ (mapEquivalenceHom e R R' φ).f 0 =
      e.functor.map f ≫ (mapEquivalence e R').ι.f 0 := by
  simpa only [mapEquivalence_ι_f_zero, mapEquivalenceHom_f, Functor.map_comp]
    using congrArg (fun g => e.functor.map g) hφ

/-- The same lift commutes with the complete transported augmentation. -/
lemma mapEquivalenceHom_commutes (f : X ⟶ X')
    (φ : R.cocomplex ⟶ R'.cocomplex)
    (hφ : R.ι.f 0 ≫ φ.f 0 = f ≫ R'.ι.f 0) :
    (mapEquivalence e R).ι ≫ mapEquivalenceHom e R R' φ =
      (CochainComplex.single₀ D).map (e.functor.map f) ≫ (mapEquivalence e R').ι := by
  apply HomologicalComplex.from_single_hom_ext
  simpa only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
    using mapEquivalenceHom_commutes_zero e R R' f φ hφ

/-- The mapped pinned descent lifts the image of the original coefficient map. -/
lemma mapEquivalence_desc_commutes_zero (f : X ⟶ X') :
    (mapEquivalence e R).ι.f 0 ≫
        (mapEquivalenceHom e R R' (desc f R' R)).f 0 =
      e.functor.map f ≫ (mapEquivalence e R').ι.f 0 :=
  mapEquivalenceHom_commutes_zero e R R' f (desc f R' R) (desc_commutes_zero f R' R)

lemma mapEquivalence_desc_commutes (f : X ⟶ X') :
    (mapEquivalence e R).ι ≫ mapEquivalenceHom e R R' (desc f R' R) =
      (CochainComplex.single₀ D).map (e.functor.map f) ≫ (mapEquivalence e R').ι :=
  mapEquivalenceHom_commutes e R R' f (desc f R' R) (desc_commutes_zero f R' R)

end CategoryTheory.InjectiveResolution
