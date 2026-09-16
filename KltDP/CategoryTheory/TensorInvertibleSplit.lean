/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/PicComparison.lean, lines 129–222.
The pinned name leftUnitor_tensor replaces leftUnitor_tensor_hom. The
naturality of tensoring an isomorphism is supplied directly by the pinned
whisker_exchange identity.
-/
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Split pairs against actual tensor-invertible objects

In a monoidal category, an object with a two-sided tensor inverse cannot
have a proper split summand isomorphic to the tensor unit. The proof acts
with endomorphisms of the unit, then cancels a faithful tensor functor.
The tensor inverse and the one-sided composite are actual isomorphisms
and morphism equalities, rather than an assumed converse splitting.

This is a categorical ingredient for the sheaf Picard converse. It does
not construct local sections, sheaf restriction comparisons or rank-one
trivializations.
-/

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

universe v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The conjugation action of an endomorphism of the monoidal unit on an object. -/
def unitEndAct (s : 𝟙_ D ⟶ 𝟙_ D) (X : D) : X ⟶ X :=
  (λ_ X).inv ≫ s ▷ X ≫ (λ_ X).hom

theorem unitEndAct_naturality (s : 𝟙_ D ⟶ 𝟙_ D) {X Y : D} (f : X ⟶ Y) :
    unitEndAct s X ≫ f = f ≫ unitEndAct s Y := by
  simp only [unitEndAct, Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

theorem unitEndAct_unit (s : 𝟙_ D ⟶ 𝟙_ D) : unitEndAct s (𝟙_ D) = s := by
  show (λ_ (𝟙_ D)).inv ≫ s ▷ 𝟙_ D ≫ (λ_ (𝟙_ D)).hom = s
  rw [unitors_equal, rightUnitor_naturality, unitors_inv_equal, Iso.inv_hom_id_assoc]

theorem unitEndAct_tensor (s : 𝟙_ D ⟶ 𝟙_ D) (X Y : D) :
    unitEndAct s (X ⊗ Y) = unitEndAct s X ▷ Y := by
  simp only [unitEndAct, comp_whiskerRight, whiskerRight_tensor, leftUnitor_tensor,
    leftUnitor_tensor_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- Conjugating the unit-endomorphism action along an isomorphism. -/
theorem unitEndAct_conj (s : 𝟙_ D ⟶ 𝟙_ D) {X Y : D} (k : X ≅ Y) :
    unitEndAct s Y = k.inv ≫ unitEndAct s X ≫ k.hom := by
  rw [unitEndAct_naturality s k.hom, Iso.inv_hom_id_assoc]

/-- An idempotent-producing split pair through the unit is two-sided, provided the
middle object is isomorphic to a ⊗-invertible one. -/
theorem comp_eq_id_of_comp_eq_id {P : D} (v : 𝟙_ D ⟶ P) (w : P ⟶ 𝟙_ D)
    (hwv : w ≫ v = 𝟙 P) {B' A' : D} (kP : P ≅ B') (e'' : B' ⊗ A' ≅ 𝟙_ D) :
    v ≫ w = 𝟙 (𝟙_ D) := by
  have h1 : unitEndAct (v ≫ w) P ≫ w = w := by
    rw [unitEndAct_naturality, unitEndAct_unit, ← Category.assoc, hwv, Category.id_comp]
  have hq : unitEndAct (v ≫ w) P = 𝟙 P := by
    calc unitEndAct (v ≫ w) P
        = unitEndAct (v ≫ w) P ≫ w ≫ v := by rw [hwv, Category.comp_id]
      _ = (unitEndAct (v ≫ w) P ≫ w) ≫ v := (Category.assoc _ _ _).symm
      _ = w ≫ v := by rw [h1]
      _ = 𝟙 P := hwv
  have hqB : unitEndAct (v ≫ w) B' = 𝟙 B' := by
    rw [unitEndAct_conj (v ≫ w) kP, hq, Category.id_comp, Iso.inv_hom_id]
  have hqBA : unitEndAct (v ≫ w) (B' ⊗ A') = 𝟙 (B' ⊗ A') := by
    rw [unitEndAct_tensor, hqB, id_whiskerRight]
  rw [← unitEndAct_unit (v ≫ w), unitEndAct_conj (v ≫ w) e'', hqBA,
    Category.id_comp, Iso.inv_hom_id]

/-- **Split pairs against an invertible object are two-sided:** if `A` is ⊗-invertible
and `a : 𝟙 ⟶ A`, `b : A ⟶ 𝟙` satisfy `a ≫ b = 𝟙`, then also `b ≫ a = 𝟙`.
(The heart of
"an invertible module with a unit pairing value is trivial": conjugate the idempotent
`b ≫ a` into `End (𝟙_)`, where the split property and invertibility force it to be the
identity.) -/
theorem whiskerRight_comp_eq_id_of_split {A B : D} (e : A ⊗ B ≅ 𝟙_ D)
    (e' : B ⊗ A ≅ 𝟙_ D) (a : 𝟙_ D ⟶ A) (b : A ⟶ 𝟙_ D)
    (hab : a ≫ b = 𝟙 (𝟙_ D)) : b ≫ a = 𝟙 A := by
  -- `tensorRight B` is faithful: composing with `tensorRight A` is isomorphic to `𝟭`
  haveI : (tensorRight B ⋙ tensorRight A).Faithful := by
    refine Functor.Faithful.of_iso (F := 𝟭 D) ?_
    have hcongr : tensorRight (𝟙_ D) ≅ tensorRight (B ⊗ A) :=
      NatIso.ofComponents (fun X => whiskerLeftIso X e'.symm) (by
        intro X Y f
        exact (whisker_exchange f e'.inv).symm)
    exact (rightUnitorNatIso D).symm ≪≫ hcongr ≪≫ tensorRightTensor B A
  haveI : (tensorRight B).Faithful :=
    Functor.Faithful.of_comp (tensorRight B) (tensorRight A)
  apply (tensorRight B).map_injective
  show (b ≫ a) ▷ B = 𝟙 A ▷ B
  have hvw : (e.inv ≫ b ▷ B) ≫ ((a ▷ B) ≫ e.hom) = 𝟙 (𝟙_ D) := by
    refine comp_eq_id_of_comp_eq_id (e.inv ≫ b ▷ B) ((a ▷ B) ≫ e.hom) ?_ (λ_ B) e'
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight, hab, id_whiskerRight]
  have hba : (b ▷ B) ≫ (a ▷ B) = 𝟙 (A ⊗ B) := by
    have h2 := congrArg (fun t => e.hom ≫ t ≫ e.inv) hvw
    simpa [Category.assoc] using h2
  rw [comp_whiskerRight, hba, id_whiskerRight]

end CategoryTheory.MonoidalCategory
