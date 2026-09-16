import KltDP.Compatibility.BoundedInjectiveLocalization
import KltDP.Compatibility.HomComplexHomotopyCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Ext and the original injective-resolution Hom complex

The shifted localization comparison is constructed from the actual bounded
complex of injectives. The Ext comparison then uses the original resolution
augmentation and the pinned definition of Ext. Its coefficient naturality
retains the original compatible resolution map. No K-injectivity or desired
comparison is assumed, and the additive structures are the original ones.
-/

universe w' w v u

open CategoryTheory Category Limits Preadditive
open CochainComplex.HomComplex

namespace KltDP.InjectiveResolutionExtComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C]

/-- Cohomology classes identify with the original derived morphisms into
the shifted bounded-below complex of injectives. -/
noncomputable def derivedHomAddEquiv (K L : CochainComplex C ℤ) (d n : ℤ)
    [L.IsStrictlyGE d] [∀ i : ℤ, Injective (L.X i)] :
    CohomologyClass K L n ≃+
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) := by
  letI : (L⟦n⟧).IsStrictlyGE (d - n) :=
    L.isStrictlyGE_shift d n (d - n) (by omega)
  letI : ∀ i : ℤ, Injective ((L⟦n⟧).X i) := fun i =>
    Injective.of_iso (L.shiftFunctorObjXIso n i (i + n) rfl).symm inferInstance
  exact (CohomologyClass.homAddEquiv.trans
    (BoundedInjectiveComparison.homAddEquiv (L⟦n⟧) (d - n)
      ((HomotopyCategory.quotient C _).obj K))).trans
    (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso C).app K)
      (((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧)) ≪≫
        (DerivedCategory.Q.commShiftIso n).app L)).toAddEquiv

lemma derivedHomAddEquiv_apply (K L : CochainComplex C ℤ) (d n : ℤ)
    [L.IsStrictlyGE d] [∀ i : ℤ, Injective (L.X i)]
    (x : CohomologyClass K L n) :
    derivedHomAddEquiv K L d n x =
      (DerivedCategory.quotientCompQhIso C).inv.app K ≫
        DerivedCategory.Qh.map (CohomologyClass.toHom x) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app (L⟦n⟧) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := by
  change (((DerivedCategory.quotientCompQhIso C).inv.app K ≫
      DerivedCategory.Qh.map (CohomologyClass.toHom x)) ≫
        ((DerivedCategory.quotientCompQhIso C).hom.app (L⟦n⟧) ≫
          (DerivedCategory.Q.commShiftIso n).hom.app L)) = _
  simp only [Category.assoc]

/-- On an actual cocycle, the comparison is its original shifted cochain
map followed by the canonical commutation of localization and shift. -/
lemma derivedHomAddEquiv_mk (K L : CochainComplex C ℤ) (d n : ℤ)
    [L.IsStrictlyGE d] [∀ i : ℤ, Injective (L.X i)] (x : Cocycle K L n) :
    derivedHomAddEquiv K L d n (CohomologyClass.mk x) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm x) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := by
  rw [derivedHomAddEquiv_apply, CohomologyClass.toHom_mk]
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality
    (Cocycle.equivHomShift.symm x)
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x)) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (L⟦n⟧) =
    (DerivedCategory.quotientCompQhIso C).hom.app K ≫
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm x) at h
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
    congrArg (fun z => (DerivedCategory.quotientCompQhIso C).inv.app K ≫ z ≫
      (DerivedCategory.Q.commShiftIso n).hom.app L) h

/-- Naturality in the actual coefficient cochain map. -/
lemma derivedHomAddEquiv_postcomp (K L L' : CochainComplex C ℤ) (d d' n : ℤ)
    [L.IsStrictlyGE d] [∀ i : ℤ, Injective (L.X i)]
    [L'.IsStrictlyGE d'] [∀ i : ℤ, Injective (L'.X i)]
    (f : L ⟶ L') (x : CohomologyClass K L n) :
    derivedHomAddEquiv K L' d' n (HomComplexComparison.cohomologyClassPostcomp f n x) =
      derivedHomAddEquiv K L d n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [HomComplexComparison.cohomologyClassPostcomp_mk, derivedHomAddEquiv_mk,
    derivedHomAddEquiv_mk, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]
  exact (Category.assoc _ _ _).symm

/-- The pinned single-functor comparison, evaluated at degree zero. -/
private noncomputable def singleQIso :
    DerivedCategory.singleFunctor C 0 ≅
      CochainComplex.singleFunctor C 0 ⋙ DerivedCategory.Q :=
  (SingleFunctors.evaluation _ _ 0).mapIso (DerivedCategory.singleFunctorsPostcompQIso C)

/-- The original resolution augmentation gives the actual derived
isomorphism from the original degree-zero single object. -/
noncomputable def resolutionDerivedIso {Y : C} (R : InjectiveResolution Y) :
    (DerivedCategory.singleFunctor C 0).obj Y ≅ DerivedCategory.Q.obj R.cochainComplex :=
  (singleQIso.app Y) ≪≫ asIso (DerivedCategory.Q.map R.ι')

lemma resolutionDerivedIso_naturality {Y Y' : C}
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y')
    (g : Y ⟶ Y') (φ : R.Hom R' g) :
    (resolutionDerivedIso R).hom ≫ DerivedCategory.Q.map φ.hom' =
      (DerivedCategory.singleFunctor C 0).map g ≫ (resolutionDerivedIso R').hom := by
  have h := (singleQIso (C := C)).hom.naturality g
  change (DerivedCategory.singleFunctor C 0).map g ≫ singleQIso.hom.app Y' =
    singleQIso.hom.app Y ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map g) at h
  simp only [resolutionDerivedIso, Iso.trans_hom, asIso_hom, Iso.app_hom,
    Category.assoc, ← Functor.map_comp, φ.ι'_comp_hom']
  rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc]

variable [HasExt.{w'} C]

/-- Ext is computed by the Hom complex of the original extended injective
resolution, using its actual augmentation. -/
noncomputable def extAddEquiv {Y : C} (R : InjectiveResolution Y) (X : C) (n : ℕ) :
    CategoryTheory.Abelian.Ext.{w'} X Y n ≃+
      CohomologyClass ((CochainComplex.singleFunctor C 0).obj X) R.cochainComplex (n : ℤ) :=
  (CategoryTheory.Abelian.Ext.homAddEquiv.trans
    (Linear.homCongr ℤ (singleQIso.app X)
      ((shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso (resolutionDerivedIso R))).toAddEquiv).trans
    (derivedHomAddEquiv _ R.cochainComplex 0 (n : ℤ)).symm

/-- This characterizes the comparison by the original Ext morphism and
the original augmentation, rather than a chosen additive identification. -/
lemma extAddEquiv_derived {Y : C} (R : InjectiveResolution Y) (X : C) (n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{w'} X Y n) :
    derivedHomAddEquiv _ R.cochainComplex 0 (n : ℤ) (extAddEquiv R X n α) =
      (singleQIso.app X).inv ≫ α.hom ≫ (resolutionDerivedIso R).hom⟦(n : ℤ)⟧' := by
  change (derivedHomAddEquiv _ R.cochainComplex 0 (n : ℤ))
    ((derivedHomAddEquiv _ R.cochainComplex 0 (n : ℤ)).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  change ((singleQIso.app X).inv ≫ α.hom) ≫
    (resolutionDerivedIso R).hom⟦(n : ℤ)⟧' = _
  exact Category.assoc _ _ _

/-- The comparison commutes with the actual coefficient morphism on Ext
and with any actual augmentation-compatible map of the given resolutions. -/
lemma extAddEquiv_postcomp {Y Y' : C}
    (R : InjectiveResolution Y) (R' : InjectiveResolution Y') (X : C) (n : ℕ)
    (g : Y ⟶ Y') (φ : R.Hom R' g) (α : CategoryTheory.Abelian.Ext.{w'} X Y n) :
    extAddEquiv R' X n (α.comp (CategoryTheory.Abelian.Ext.mk₀ g) (add_zero n)) =
      HomComplexComparison.cohomologyClassPostcomp φ.hom' (n : ℤ)
        (extAddEquiv R X n α) := by
  apply (derivedHomAddEquiv _ R'.cochainComplex 0 (n : ℤ)).injective
  rw [derivedHomAddEquiv_postcomp _ _ _ 0 0, extAddEquiv_derived,
    extAddEquiv_derived, CategoryTheory.Abelian.Ext.comp_hom,
    CategoryTheory.Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  have h := congrArg (fun z => z⟦(n : ℤ)⟧')
    (resolutionDerivedIso_naturality R R' g φ)
  simp only [Functor.map_comp] at h
  simpa only [Category.assoc] using
    congrArg (fun z => (singleQIso.app X).inv ≫ α.hom ≫ z) h.symm

end KltDP.InjectiveResolutionExtComparison
