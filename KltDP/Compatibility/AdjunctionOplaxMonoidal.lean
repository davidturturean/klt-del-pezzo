/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The oplax structure on a left adjoint

Bounded port of the actual adjunction proof in Mathlib revision
`5aedf732b6987e8c26ab3c9ebc855314f82b045f`,
`Mathlib/CategoryTheory/Monoidal/Functor.lean`, raw lines 1052–1097.
The complete source file has SHA-256
`4f344dc46eb34a8017b45ffb79376c6d15c98c9b88a44068af083f2bb5347855`.

The pinned structure fields have primed names, and its tensor morphism
notation is `⊗`. The mate definitions and their coherence proofs are retained.
The final computation lemmas follow directly from the adjunction equivalence.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Category Functor MonoidalCategory
open Functor.OplaxMonoidal Functor.LaxMonoidal

/-- Transport on the right postcomposes the adjunction bijection with
the chosen natural isomorphism. -/
theorem homEquiv_ofNatIsoRight_apply
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H)
    (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    (adj.ofNatIsoRight e).homEquiv X Y f =
      adj.homEquiv X Y f ≫ e.hom.app Y := by
  unfold ofNatIsoRight
  rw [mkOfHomEquiv_homEquiv]
  rfl

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxMonoidal]

/-- The left adjoint of a lax monoidal functor is oplax monoidal. -/
abbrev leftAdjointOplaxMonoidal : F.OplaxMonoidal where
  η' := (adj.homEquiv _ _).symm (ε G)
  δ' X Y := (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ adj.unit.app Y) ≫ μ G _ _)
  δ'_natural_left _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm, assoc, ← μ_natural_left]
    simp [← tensorHom_id]
    simp only [← tensor_comp_assoc, unit_naturality, comp_id, id_comp]
  δ'_natural_right _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm, assoc, ← μ_natural_right]
    simp [← id_tensorHom]
    simp only [← tensor_comp_assoc, unit_naturality, comp_id, id_comp]
  oplax_associativity' X Y Z := (adj.homEquiv _ _).injective (by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, assoc, assoc]
    conv_lhs =>
      rw [homEquiv_counit, map_comp_assoc, map_comp,
        ← μ_natural_left_assoc, map_comp, map_comp, tensorHom_def'_assoc]
      dsimp
      rw [← comp_whiskerRight_assoc]
    conv_rhs =>
      rw [← μ_natural_right, homEquiv_counit, map_comp_assoc,
        map_comp, tensorHom_def_assoc, ← associator_naturality_left_assoc]
      dsimp
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, map_comp,
        unit_naturality_assoc, MonoidalCategory.whiskerLeft_comp,
        unit_naturality_assoc, right_triangle_components, comp_id, assoc,
        tensorHom_def, MonoidalCategory.whiskerLeft_comp_assoc,
        ← associator_naturality_middle_assoc, ← associator_naturality_right_assoc,
        ← associativity G, ← comp_whiskerRight_assoc, ← tensorHom_def,
        ← whisker_exchange_assoc, ← comp_whiskerRight_assoc]
    simp)
  oplax_left_unitality' _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, assoc, ← μ_natural_left, ← tensorHom_id,
      ← tensor_comp_assoc]
    simp [tensorHom_def', homEquiv_unit, homEquiv_counit])
  oplax_right_unitality' _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, assoc, ← μ_natural_right, ← id_tensorHom,
      ← tensor_comp_assoc]
    simp [tensorHom_def, homEquiv_unit, homEquiv_counit])


/-- The unit map is the adjoint transpose of the lax unit map. -/
theorem leftAdjointOplaxMonoidal_η :
    letI := adj.leftAdjointOplaxMonoidal
    η F = (adj.homEquiv _ _).symm (ε G) := rfl

/-- The tensor map is the adjoint transpose of the two unit maps followed
by the lax tensor map. -/
theorem leftAdjointOplaxMonoidal_δ (X Y : C) :
    letI := adj.leftAdjointOplaxMonoidal
    δ F X Y =
      (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ adj.unit.app Y) ≫ μ G _ _) := rfl

/-- Applying the adjunction to its tensor mate recovers the defining map. -/
theorem leftAdjointOplaxMonoidal_unit_app_tensor_comp_map_δ (X Y : C) :
    letI := adj.leftAdjointOplaxMonoidal
    adj.unit.app (X ⊗ Y) ≫ G.map (δ F X Y) =
      (adj.unit.app X ⊗ adj.unit.app Y) ≫ μ G _ _ := by
  letI := adj.leftAdjointOplaxMonoidal
  change adj.unit.app (X ⊗ Y) ≫
      G.map ((adj.homEquiv _ _).symm
        ((adj.unit.app X ⊗ adj.unit.app Y) ≫ μ G _ _)) = _
  exact (adj.homEquiv _ _).apply_symm_apply _

end CategoryTheory.Adjunction
