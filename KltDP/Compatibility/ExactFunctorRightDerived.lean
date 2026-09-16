import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Right-derived functors along an exact functor preserving injectives

For an additive functor `G : C ⥤ D` between abelian categories that preserves homology
(exactness) and injective objects, the image of an injective resolution of `X` is an injective
resolution of `G.obj X` (`InjectiveResolution.mapExact`). Comparing the pinned
`isoRightDerivedObj` on the two resolutions gives, for every additive `F : D ⥤ A`,

    G ⋙ F.rightDerived n ≅ (G ⋙ F).rightDerived n         (`Functor.exactRightDerivedIso`)

natural in the coefficient object. This generalises the accepted
`KltDP/Compatibility/EquivalenceInjectiveResolution.lean` and `EquivalenceRightDerived.lean`
(the case of an additive equivalence) verbatim, replacing `e.functor` by `G`; naturality uses the
image of the original descent of each coefficient map, exactly as there.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category HomologicalComplex

namespace InjectiveResolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]

/-- The image of an injective resolution under an exact functor preserving injectives. -/
def mapExact {X : C} (R : InjectiveResolution X) : InjectiveResolution (G.obj X) where
  cocomplex := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  injective n := G.injective_obj_of_injective (R.injective n)
  hasHomology i := by infer_instance
  ι := (singleMapHomologicalComplex G (.up ℕ) 0).inv.app X ≫
    (G.mapHomologicalComplex (.up ℕ)).map R.ι
  quasiIso := by infer_instance

variable {X X' : C} (R : InjectiveResolution X) (R' : InjectiveResolution X')

@[simp]
lemma mapExact_X (n : ℕ) :
    (mapExact G R).cocomplex.X n = G.obj (R.cocomplex.X n) := rfl

@[simp]
lemma mapExact_d (i j : ℕ) :
    (mapExact G R).cocomplex.d i j = G.map (R.cocomplex.d i j) := rfl

lemma mapExact_ι :
    (mapExact G R).ι =
      (singleMapHomologicalComplex G (.up ℕ) 0).inv.app X ≫
        (G.mapHomologicalComplex (.up ℕ)).map R.ι := rfl

@[simp]
lemma mapExact_ι_f_zero :
    (mapExact G R).ι.f 0 = G.map (R.ι.f 0) := by
  simp [mapExact, singleMapHomologicalComplex_inv_app_self]

/-- The image of a map of resolution complexes. -/
def mapExactHom (φ : R.cocomplex ⟶ R'.cocomplex) :
    (mapExact G R).cocomplex ⟶ (mapExact G R').cocomplex :=
  (G.mapHomologicalComplex (.up ℕ)).map φ

@[simp]
lemma mapExactHom_f (φ : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    (mapExactHom G R R' φ).f n = G.map (φ.f n) := rfl

/-- A coefficient-map lift retains its degree-zero compatibility. -/
lemma mapExactHom_commutes_zero (f : X ⟶ X')
    (φ : R.cocomplex ⟶ R'.cocomplex)
    (hφ : R.ι.f 0 ≫ φ.f 0 = f ≫ R'.ι.f 0) :
    (mapExact G R).ι.f 0 ≫ (mapExactHom G R R' φ).f 0 =
      G.map f ≫ (mapExact G R').ι.f 0 := by
  simpa only [mapExact_ι_f_zero, mapExactHom_f, Functor.map_comp]
    using congrArg (fun g => G.map g) hφ

/-- The mapped pinned descent lifts the image of the coefficient map. -/
lemma mapExact_desc_commutes_zero (f : X ⟶ X') :
    (mapExact G R).ι.f 0 ≫
        (mapExactHom G R R' (desc f R' R)).f 0 =
      G.map f ≫ (mapExact G R').ι.f 0 :=
  mapExactHom_commutes_zero G R R' f (desc f R' R) (desc_commutes_zero f R' R)

variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (F : D ⥤ A) [F.Additive] (n : ℕ)

/-- The comparison computed on the original resolution and its image. -/
def exactRightDerivedIso {Y : C} (S : InjectiveResolution Y) :
    (F.rightDerived n).obj (G.obj Y) ≅
      ((G ⋙ F).rightDerived n).obj Y :=
  (mapExact G S).isoRightDerivedObj F n ≪≫
    (S.isoRightDerivedObj (G ⋙ F) n).symm

/-- The chosen-resolution comparison commutes with each coefficient map. -/
lemma exactRightDerivedIso_hom_naturality {Y Y' : C}
    (S : InjectiveResolution Y) (S' : InjectiveResolution Y') (f : Y ⟶ Y') :
    (F.rightDerived n).map (G.map f) ≫
        (exactRightDerivedIso G F n S').hom =
      (exactRightDerivedIso G F n S).hom ≫
        ((G ⋙ F).rightDerived n).map f := by
  have h₁ := isoRightDerivedObj_hom_naturality (G.map f)
    (mapExact G S) (mapExact G S')
    (mapExactHom G S S' (desc f S' S))
    (mapExact_desc_commutes_zero G S S' f) F n
  have h₂ := isoRightDerivedObj_inv_naturality f S S' (desc f S' S)
    (desc_commutes_zero f S' S) (G ⋙ F) n
  simp only [exactRightDerivedIso, Iso.trans_hom, Iso.symm_hom]
  erw [← assoc, h₁, assoc, ← h₂, ← assoc]

end InjectiveResolution

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
  {A : Type u₃} [Category.{v₃} A] [Abelian A]
  (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]
  (F : D ⥤ A) [F.Additive] (n : ℕ)

/-- Precomposition by an exact functor preserving injectives commutes with right-derived
functors. -/
def exactRightDerivedIso :
    G ⋙ F.rightDerived n ≅ (G ⋙ F).rightDerived n :=
  NatIso.ofComponents
    (fun X => InjectiveResolution.exactRightDerivedIso G F n (injectiveResolution X))
    (fun {X Y} f => InjectiveResolution.exactRightDerivedIso_hom_naturality
      G F n (injectiveResolution X) (injectiveResolution Y) f)

@[simp]
lemma exactRightDerivedIso_hom_app (X : C) :
    (exactRightDerivedIso G F n).hom.app X =
      ((InjectiveResolution.mapExact G (injectiveResolution X)).isoRightDerivedObj F n).hom ≫
        ((injectiveResolution X).isoRightDerivedObj (G ⋙ F) n).inv := rfl

end Functor

end CategoryTheory
