/-
Copyright (c) 2024, 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Joël Riou

Adapted from leanprover-community/mathlib4 at
5aedf732b6987e8c26ab3c9ebc855314f82b045f:
Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean, lines 67–74,
and Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean.

The abbreviation exposes the existing pinned pushforward, and the monoidal
proof is retained. Module-system declarations are adapted to Lean 4.19.
The final named tensor/unit comparisons specialize the proved structure.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Tensor products under actual presheaf restriction

Precomposition preserves the sectionwise tensor product of presheaves of
modules over a presheaf of commutative rings. In particular, this applies
to restriction along `Over.forget U`.

This is a statement about actual presheaves, with their restriction maps.
Compatibility of sheafification with restriction, tensor products of
locally rank-one sheaves, and sheaf duality are separate results.
-/

universe v u v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u})

/-- The existing precomposition functor, with the commutative ring
presheaf displayed explicitly for the sectionwise tensor structures. -/
abbrev pushforward₀OfCommRingCat :
    PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{v} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) :=
  pushforward₀ F (R ⋙ forget₂ CommRingCat RingCat)

open ModuleCat.MonoidalCategory in
/-- Precomposition preserves the actual tensor and unit, with the
coherence laws checked on simple tensors. -/
noncomputable instance : (pushforward₀OfCommRingCat.{u} F R).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ tensor_ext fun _ _ ↦ rfl)
      associativity _ _ _ := by
        ext1
        exact tensor_ext₃' fun m₁ m₂ m₃ ↦ rfl
      left_unitality _ := by
        ext1
        exact tensor_ext fun m₁ m₂ ↦ rfl
      right_unitality _ := by
        ext1
        exact tensor_ext fun m₁ m₂ ↦ rfl }

/-- Restricting the actual sectionwise tensor is isomorphic to the
sectionwise tensor of the restricted presheaves. -/
noncomputable def precompositionTensorIso
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (pushforward₀OfCommRingCat F R).obj (M ⊗ N) ≅
      (pushforward₀OfCommRingCat F R).obj M ⊗
        (pushforward₀OfCommRingCat F R).obj N :=
  (Functor.Monoidal.μIso (pushforward₀OfCommRingCat F R) M N).symm

/-- Restriction takes the ring presheaf as a module over itself to the
restricted ring presheaf as a module over itself. -/
noncomputable def precompositionUnitIso :
    (pushforward₀OfCommRingCat.{u} F R).obj
        (unit (R ⋙ forget₂ CommRingCat RingCat)) ≅
      unit ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) :=
  (Functor.Monoidal.εIso (pushforward₀OfCommRingCat F R)).symm

variable {F}

/-- The tensor comparison for actual restriction to the over-category. -/
noncomputable def overTensorIso (U : D)
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (pushforward₀OfCommRingCat (Over.forget U) R).obj (M ⊗ N) ≅
      (pushforward₀OfCommRingCat (Over.forget U) R).obj M ⊗
        (pushforward₀OfCommRingCat (Over.forget U) R).obj N :=
  precompositionTensorIso (Over.forget U) R M N

/-- The unit comparison for actual restriction to the over-category. -/
noncomputable def overUnitIso (U : D) :
    (pushforward₀OfCommRingCat.{u} (Over.forget U) R).obj
        (unit (R ⋙ forget₂ CommRingCat RingCat)) ≅
      unit (((Over.forget U).op ⋙ R) ⋙ forget₂ CommRingCat RingCat) :=
  precompositionUnitIso (Over.forget U) R

end PresheafOfModules
