/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

Adapted from Vilin97/MazurTheorem 9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pullback.lean, lines 881–916.
Original source: CBirkbeck/AINTLIB 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/ForMathlib/PullbackTensorGeneral.lean.

The pinned module tensor–Hom adjunction is reused. Both presheaf tensor
directions are proved pointwise, without requiring an additional
presheaf braiding port. AddCommGrp is the pinned category name.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Colimit preservation by the actual module-presheaf tensor

Evaluation jointly reflects colimits and preserves them under the stated
abelian-group colimit hypothesis. Each evaluated tensor functor preserves
colimits by the existing module tensor–Hom adjunction. The cocones agree
through the actual pointwise tensor definitions.

These proofs concern the existing module presheaves and their existing
tensor. They neither assume tensor preservation nor assert preservation
of a sheaf tensor or compatibility with a scheme pullback.
-/

noncomputable section

universe u u₁ v₁ w w'

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {T : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Tensoring on the left by an actual module presheaf preserves colimits
of every shape for which the original abelian-group colimits exist. -/
theorem preservesColimitsOfShape_tensorLeft
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat))
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J AddCommGrp.{u}] :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft Q) where
  preservesColimit {K} := {
    preserves {c} hc := by
      refine ⟨evaluationJointlyReflectsColimits _ _ (fun V => ?_)⟩
      letI : PreservesColimitsOfSize.{w', w}
          (MonoidalCategory.tensorLeft (Q.obj V)) :=
        (ihom.adjunction (Q.obj V)).leftAdjoint_preservesColimits
      have h1 : IsColimit ((evaluation
          (T ⋙ forget₂ CommRingCat RingCat) V).mapCocone c) :=
        isColimitOfPreserves _ hc
      have h2 := isColimitOfPreserves (MonoidalCategory.tensorLeft (Q.obj V)) h1
      exact h2.ofIsoColimit (Cocones.ext (Iso.refl _) (fun j => by
        change _ ≫ 𝟙 _ = _
        rw [Category.comp_id]
        rfl)) }

/-- Tensoring on the right also preserves the same colimits. The only
braiding used is the existing one in each actual module category. -/
theorem preservesColimitsOfShape_tensorRight
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat))
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J AddCommGrp.{u}] :
    PreservesColimitsOfShape J (MonoidalCategory.tensorRight Q) where
  preservesColimit {K} := {
    preserves {c} hc := by
      refine ⟨evaluationJointlyReflectsColimits _ _ (fun V => ?_)⟩
      letI : PreservesColimitsOfSize.{w', w}
          (MonoidalCategory.tensorLeft (Q.obj V)) :=
        (ihom.adjunction (Q.obj V)).leftAdjoint_preservesColimits
      letI : PreservesColimitsOfShape J (MonoidalCategory.tensorRight (Q.obj V)) :=
        preservesColimitsOfShape_of_natIso
          (BraidedCategory.tensorLeftIsoTensorRight (Q.obj V))
      have h1 : IsColimit ((evaluation
          (T ⋙ forget₂ CommRingCat RingCat) V).mapCocone c) :=
        isColimitOfPreserves _ hc
      have h2 := isColimitOfPreserves (MonoidalCategory.tensorRight (Q.obj V)) h1
      exact h2.ofIsoColimit (Cocones.ext (Iso.refl _) (fun j => by
        change _ ≫ 𝟙 _ = _
        rw [Category.comp_id]
        rfl)) }

/-- Packaging for diagrams whose object and morphism universes have
the same size as the original section rings and modules. -/
theorem preservesColimitsOfSize_tensorLeft_aux
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorLeft Q) :=
  ⟨fun {J} _ => preservesColimitsOfShape_tensorLeft Q J⟩

/-- The corresponding size-`u` statement for right tensoring. -/
theorem preservesColimitsOfSize_tensorRight_aux
    (Q : PresheafOfModules.{u} (T ⋙ forget₂ CommRingCat RingCat)) :
    PreservesColimitsOfSize.{u, u} (MonoidalCategory.tensorRight Q) :=
  ⟨fun {J} _ => preservesColimitsOfShape_tensorRight Q J⟩

end PresheafOfModules
