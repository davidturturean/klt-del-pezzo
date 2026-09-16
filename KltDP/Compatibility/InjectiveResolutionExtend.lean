/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison, Joël Riou
-/
import KltDP.Compatibility.ExtendSingleComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Integer-indexed injective resolutions and compatible maps

The resolution and augmentation are the extension by zero of the pinned
`InjectiveResolution.cocomplex` and `InjectiveResolution.ι`. The comparison
map for a morphism of objects is constructed by the pinned injective-resolution
descent. The definitions and compatibility statements follow Mathlib's
`Preadditive.Injective.Resolution` and `Abelian.Injective.Extend` at commit
79d0395a1825a6264ad5d269e35e60537518955e.
-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace InjectiveResolution

section Morphisms

variable [HasZeroObject C] [HasZeroMorphisms C] {X X' : C}
  (R : InjectiveResolution X) (R' : InjectiveResolution X')

/-- A morphism of resolutions compatible with the given morphism of objects. -/
structure Hom (f : X ⟶ X') where
  /-- The morphism of the actual natural-number-indexed complexes. -/
  hom : R.cocomplex ⟶ R'.cocomplex
  ι_f_zero_comp_hom_f_zero :
    R.ι.f 0 ≫ hom.f 0 = ((CochainComplex.single₀ C).map f).f 0 ≫ R'.ι.f 0

variable {R R'}

@[reassoc]
lemma Hom.ι_comp_hom {f : X ⟶ X'} (φ : Hom R R' f) :
    R.ι ≫ φ.hom = (CochainComplex.single₀ C).map f ≫ R'.ι := by
  apply HomologicalComplex.from_single_hom_ext
  simpa only [HomologicalComplex.comp_f] using φ.ι_f_zero_comp_hom_f_zero

end Morphisms

section Extension

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : InjectiveResolution X)

/-- Extension by zero of an injective resolution to integer degrees. -/
noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.cocomplex.extend ComplexShape.embeddingUpNat

instance : R.cochainComplex.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  refine HomologicalComplex.isZero_extend_X R.cocomplex
    ComplexShape.embeddingUpNat n ?_
  intro k hk
  have hk' : (k : ℤ) = n := hk
  have : 0 ≤ n := hk' ▸ Int.natCast_nonneg k
  omega

/-- The component in an integer degree represented by a natural number. -/
noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : k = n) :
    R.cochainComplex.X n ≅ R.cocomplex.X k :=
  HomologicalComplex.extendXIso _ _ h

@[reassoc]
lemma cochainComplex_d (n₁ n₂ : ℤ) (k₁ k₂ : ℕ) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) :
    R.cochainComplex.d n₁ n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫
      R.cocomplex.d k₁ k₂ ≫ (cochainComplexXIso _ _ _ h₂).inv :=
  HomologicalComplex.extend_d_eq _ _ h₁ h₂

instance (n : ℤ) : Injective (R.cochainComplex.X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact Injective.of_iso (R.cochainComplexXIso _ _ rfl).symm inferInstance
  · exact IsZero.injective (CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega))

/-- The original augmentation transported along the extension of a single complex. -/
noncomputable def ι' :
    (CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex :=
  (HomologicalComplex.extendSingleIso _ _ _ _ (by simp)).inv ≫
    (ComplexShape.embeddingUpNat.extendFunctor C).map R.ι

@[reassoc]
lemma ι'_f_zero :
    R.ι'.f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ R.ι.f 0 ≫
      (R.cochainComplexXIso _ _ (by simp)).inv := by
  dsimp only [ι', HomologicalComplex.comp_f, ComplexShape.Embedding.extendFunctor]
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp),
    HomologicalComplex.extendSingleIso_inv_f]
  simp [cochainComplexXIso, Category.assoc]

end Extension

variable [Abelian C] {X : C} (R : InjectiveResolution X)

instance : QuasiIso R.ι' := by
  letI : QuasiIso (HomologicalComplex.extendMap R.ι ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff
      ((CochainComplex.single₀ C).obj X) R.cocomplex R.ι
      ComplexShape.embeddingUpNat).2 inferInstance
  dsimp only [ι', ComplexShape.Embedding.extendFunctor]
  infer_instance

instance : R.cochainComplex.IsLE 0 := by
  rw [CochainComplex.isLE_iff]
  intro n hn
  exact (exactAt_iff_of_quasiIsoAt R.ι' n).1
    (((CochainComplex.singleFunctor C 0).obj X).exactAt_of_isLE 0 n hn)

namespace Hom

variable {X' : C} (R' : InjectiveResolution X')

/-- The pinned comparison theorem supplies a compatible map for any object morphism. -/
noncomputable def ofMorphism (f : X ⟶ X') : Hom R R' f where
  hom := InjectiveResolution.desc f R' R
  ι_f_zero_comp_hom_f_zero := by
    simpa using InjectiveResolution.desc_commutes_zero f R' R

variable {R R'} {f : X ⟶ X'} (φ : Hom R R' f)

/-- Extension of the actual compatible resolution map to integer degrees. -/
noncomputable def hom' : R.cochainComplex ⟶ R'.cochainComplex :=
  HomologicalComplex.extendMap φ.hom _

@[reassoc]
lemma hom'_f (n : ℤ) (m : ℕ) (h : m = n) :
    φ.hom'.f n = (R.cochainComplexXIso n m h).hom ≫ φ.hom.f m ≫
      (R'.cochainComplexXIso n m h).inv := by
  exact HomologicalComplex.extendMap_f φ.hom ComplexShape.embeddingUpNat h

@[reassoc]
lemma ι'_comp_hom' :
    R.ι' ≫ φ.hom' = (CochainComplex.singleFunctor C 0).map f ≫ R'.ι' := by
  apply HomologicalComplex.from_single_hom_ext
  have hφ : R.ι.f 0 ≫ φ.hom.f 0 = f ≫ R'.ι.f 0 := by
    simpa using φ.ι_f_zero_comp_hom_f_zero
  simpa only [HomologicalComplex.comp_f, ι'_f_zero, hom'_f _ 0 0 rfl,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg
      (fun g => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ g ≫
        (R'.cochainComplexXIso 0 0 rfl).inv) hφ

end Hom

end InjectiveResolution

end CategoryTheory
