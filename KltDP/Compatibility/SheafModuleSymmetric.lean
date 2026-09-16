/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou, Chris Birkbeck

The presheaf symmetry is adapted from Mathlib
79d0395a1825a6264ad5d269e35e60537518955e,
Algebra/Category/ModuleCat/Presheaf/Monoidal.lean, lines 142–163.
The sheaf symmetry construction is adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/AINTLIB/Picard/Pic.lean.
Names and sheaf projections are adapted to the pinned Mathlib.
-/
import KltDP.Compatibility.SheafModuleMonoidal
import KltDP.Compatibility.LocalizedBraiding
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Symmetry of the actual module-sheaf tensor product

Presheaf module tensor products inherit the componentwise braiding of
ordinary modules. The localized braiding then gives a symmetric structure
for precisely the monoidal sheaf category constructed in
`SheafModuleMonoidal`. No rank-one condition or tensor inverse is assumed.
-/

noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory

universe u

namespace PresheafOfModules

section Presheaves

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The braiding exchanges the two tensor factors at every section.
Its naturality and coherence are those of ordinary module tensor products. -/
noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) where
  braiding M₁ M₂ :=
    isoMk (fun X ↦ braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f ↦ ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  braiding_naturality_left _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  hexagon_forward _ _ _ := by
    ext : 1
    apply hexagon_forward (C := ModuleCat (R.obj _))
  hexagon_reverse _ _ _ := by
    ext : 1
    apply hexagon_reverse (C := ModuleCat (R.obj _))
  symmetry _ _ := by
    ext : 1
    apply SymmetricCategory.symmetry (C := ModuleCat (R.obj _))

end Presheaves

section Sheaves

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrp.{u}] [HasWeakSheafify J AddCommGrp.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

/-- The localized presheaf braiding supplies the actual symmetric
structure on the monoidal category of module sheaves from Stage 1. -/
noncomputable abbrev sheafOfModulesSymmetricCategory :
    letI := sheafOfModulesMonoidalCategory S hS
    SymmetricCategory
      (SheafOfModules.{u} (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (L := sheafification.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val))
    (W := sheafificationW.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).val))
    (Iso.refl _)))

end Sheaves

end PresheafOfModules
