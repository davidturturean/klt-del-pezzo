/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

The scalar-restriction comparison is a bounded adaptation of mathlib4 PR
18262, head 2e2417862de055526b367657beb2ee543113d9d3,
Mathlib/Algebra/Category/ModuleCat/ExteriorPower.lean:354-373.
The presheaf below uses the current pinned exterior-power universal property,
without the PR's additional pseudofunctor infrastructure.
-/
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Exterior powers of an actual module presheaf

The object on an open is the exterior power over its original section ring.
Its restrictions send a pure wedge to the wedge of the original restrictions.
This is a presheaf construction; no sheaf property is asserted here.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace KltDP.Compatibility.ExteriorPowerPresheaf

section ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The canonical scalar-restriction comparison, defined by the alternating
universal property. It does not require freeness or a chosen frame. -/
def fromRestrictScalars (M : ModuleCat.{u} B) (n : ℕ) :
    ((ModuleCat.restrictScalars φ).obj M).exteriorPower n ⟶
      (ModuleCat.restrictScalars φ).obj (M.exteriorPower n) :=
  ModuleCat.exteriorPower.desc
    { toFun := fun m => ModuleCat.exteriorPower.mk m
      map_update_add' := fun m i x y => (exteriorPower.ιMulti B n).map_update_add m i x y
      map_update_smul' := fun m i r x => (exteriorPower.ιMulti B n).map_update_smul m i (φ r) x
      map_eq_zero_of_eq' := fun m _ _ hm hij =>
        (exteriorPower.ιMulti B n).map_eq_zero_of_eq m hm hij }

@[simp]
theorem fromRestrictScalars_mk (M : ModuleCat.{u} B) (n : ℕ) (m : Fin n → M) :
    fromRestrictScalars φ M n (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk m :=
  ModuleCat.exteriorPower.desc_mk _ _

end ChangeOfRings

variable {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ CommRingCat.{u})
  (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ)

local instance ringObjCommRing (V : Cᵒᵖ) :
    CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj V) :=
  inferInstanceAs (CommRing (R.obj V))

/-- The original restriction on each factor induces this restriction on exterior
powers; the change of rings is along exactly `R.map f`. -/
def restriction {V W : Cᵒᵖ} (f : V ⟶ W) :
    (M.obj V).exteriorPower n ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj W).exteriorPower n) :=
  ModuleCat.exteriorPower.map (M.map f) n ≫
    fromRestrictScalars (R.map f).hom (M.obj W) n

@[simp]
theorem restriction_mk {V W : Cᵒᵖ} (f : V ⟶ W) (m : Fin n → M.obj V) :
    restriction R M n f (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := M.obj W) (fun i => M.map f (m i)) := by
  simp [restriction, Function.comp_def]

/-- The pointwise exterior-power presheaf of modules. No atlas occurs in its
definition, and the original module presheaf determines all restriction maps. -/
def presheaf : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj V := (M.obj V).exteriorPower n
  map f := restriction R M n f
  map_id V := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    change restriction R M n (𝟙 V) (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk m
    rw [restriction_mk]
    congr 1
    funext i
    change M.presheaf.map (𝟙 V) (m i) = m i
    rw [M.presheaf.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    change restriction R M n (f ≫ g) (ModuleCat.exteriorPower.mk m) =
      restriction R M n g (restriction R M n f (ModuleCat.exteriorPower.mk m))
    rw [restriction_mk, restriction_mk, restriction_mk]
    congr 1
    funext i
    exact CategoryTheory.congr_fun (M.presheaf.map_comp f g) (m i)

@[simp]
theorem presheaf_map_mk {V W : Cᵒᵖ} (f : V ⟶ W) (m : Fin n → M.obj V) :
    (presheaf R M n).map f (exteriorPower.ιMulti (R.obj V) n m) =
      exteriorPower.ιMulti (R.obj W) n (fun i => M.map f (m i)) :=
  restriction_mk R M n f m

end KltDP.Compatibility.ExteriorPowerPresheaf
