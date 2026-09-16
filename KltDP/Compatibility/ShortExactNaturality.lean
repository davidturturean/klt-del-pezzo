/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

Bounded port from mathlib commit 80cbd0498ab39e21d24d6730b3f932cec672a702:
Algebra/Homology/HomotopyCategory/ShortExact.lean,
Algebra/Homology/DerivedCategory/ShortExact.lean,
Algebra/Homology/DerivedCategory/SingleTriangle.lean, and
Algebra/Homology/DerivedCategory/Ext/ExtClass.lean.
Exact source snapshots: audit/library_reuse/sheaf_cohomology_exact/.
The pinned singleδ definition is preserved. Its conjugating components are
normalized using the pinned singleFunctorsPostcompQIso identity lemmas.
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Naturality of the Ext class of a short exact sequence

The mapping-cone comparison induces a morphism of the actual triangles already
defined in the pinned library. This gives naturality of their connecting maps
and of the existing Ext class, without changing either definition.
-/

universe w' w v u

open CategoryTheory Category Pretriangulated

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Naturality of the canonical map from a mapping cone to the last object. -/
lemma map_descShortComplex (S₁ S₂ : ShortComplex (CochainComplex C ℤ)) (f : S₁ ⟶ S₂) :
    map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ =
      descShortComplex S₁ ≫ f.τ₃ := by
  ext i
  simpa [mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

end CochainComplex.mappingCone

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
  (f : S₁ ⟶ S₂)

/-- The morphism of derived triangles induced by a morphism of short exact
sequences of cochain complexes. -/
noncomputable def triangleOfSES.map : triangleOfSES h₁ ⟶ triangleOfSES h₂ where
  hom₁ := Q.map f.τ₁
  hom₂ := Q.map f.τ₂
  hom₃ := Q.map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    letI := CochainComplex.mappingCone.quasiIso_descShortComplex h₁
    letI := CochainComplex.mappingCone.quasiIso_descShortComplex h₂
    dsimp [triangleOfSES, triangleOfSESδ]
    rw [assoc, assoc, IsIso.inv_comp_eq, ← Functor.map_comp_assoc,
      ← CochainComplex.mappingCone.map_descShortComplex,
      Functor.map_comp_assoc, IsIso.hom_inv_id_assoc,
      ← Functor.commShiftIso_hom_naturality,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

end DerivedCategory

namespace CategoryTheory.ShortComplex.ShortExact

open DerivedCategory Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

section

variable [HasDerivedCategory.{w} C]

/-- The pinned conjugated connecting map agrees with the connecting map of the
single-complex short exact sequence, by the pinned component identity lemmas. -/
lemma singleδ_eq_triangleOfSESδ {S : ShortComplex C} (hS : S.ShortExact) :
    hS.singleδ =
      triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  dsimp [singleδ]
  rw [singleFunctorsPostcompQIso_hom_hom, singleFunctorsPostcompQIso_inv_hom]
  erw [Category.id_comp, Functor.map_id, Category.comp_id]

/-- The morphism of the pinned single-object triangles induced by a morphism
of short exact sequences in an abelian category. -/
noncomputable def singleTriangle.map {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    h₁.singleTriangle ⟶ h₂.singleTriangle where
  hom₁ := (singleFunctor C 0).map f.τ₁
  hom₂ := (singleFunctor C 0).map f.τ₂
  hom₃ := (singleFunctor C 0).map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    change h₁.singleδ ≫ ((singleFunctor C 0).map f.τ₁)⟦1⟧' =
      (singleFunctor C 0).map f.τ₃ ≫ h₂.singleδ
    rw [singleδ_eq_triangleOfSESδ, singleδ_eq_triangleOfSESδ]
    exact ((triangleOfSES.map (h₁.map_of_exact _) (h₂.map_of_exact _))
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapShortComplex.map f)).comm₃

end

/-- Naturality of the actual Ext class attached to a short exact sequence. -/
lemma extClass_naturality [HasExt.{w} C] {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    h₁.extClass.comp (Ext.mk₀ f.τ₁) (add_zero 1) =
      (Ext.mk₀ f.τ₃).comp h₂.extClass (zero_add 1) := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom,
    ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  exact (singleTriangle.map h₁ h₂ f).comm₃

end CategoryTheory.ShortComplex.ShortExact
