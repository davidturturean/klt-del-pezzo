/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in
`docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt`.
Authors: Kim Morrison, Joël Riou, Dagur Asgeirsson

This compatibility port adapts selected declarations from mathlib revision
79d0395a1825a6264ad5d269e35e60537518955e:
* Mathlib/CategoryTheory/Functor/CurryingThree.lean
* Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean
* Mathlib/CategoryTheory/Monoidal/Braided/Multifunctor.lean
* Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean
* Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean

The adaptation preserves the upstream construction and namespaces while using
the project's pinned monoidal localization and Lean 4.19 syntax. The two
multifunctor constructors and elementary flips use stock abbreviations for
reducible transparency. Projection equations used below are explicit proofs;
three hexagon maps reuse the pinned curried associator and its naturality.
-/

import Mathlib.CategoryTheory.Localization.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Functor.CurryingThree
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Braiding and symmetry on a monoidal localization

This file supplies the missing trifunctor permutations and multifunctor
constructors, then lifts the braiding through the existing monoidal localization.
It constructs braided and symmetric category instances on `LocalizedMonoidal`
and proves that the localization functor is braided.
-/

namespace CategoryTheory.Functor

variable {C₁ C₂ C₃ E : Type*}
  [Category C₁] [Category C₂] [Category C₃] [Category E]

/--
Flip the first and third arguments in a trifunctor.
-/
abbrev flip₁₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : C₃ ⥤ C₂ ⥤ C₁ ⥤ E where
  obj G := {
    obj H := {
      obj K := ((F.obj K).obj H).obj G
      map f := ((F.map f).app _).app _
      map_id K := by
        exact NatTrans.congr_app (NatTrans.congr_app (F.map_id K) H) G
      map_comp f g := by
        exact NatTrans.congr_app (NatTrans.congr_app (F.map_comp f g) H) G }
    map g := {
      app X := ((F.obj X).map g).app _
      naturality _ _ f := (NatTrans.congr_app ((F.map f).naturality g) G).symm }
    map_id H := by
      ext X
      exact NatTrans.congr_app ((F.obj X).map_id H) G
    map_comp f g := by
      ext X
      exact NatTrans.congr_app ((F.obj X).map_comp f g) G }
  map h := {
    app X := {
      app Y := ((F.obj Y).obj X).map h
      naturality _ _ f := (((F.map f).app X).naturality h).symm }
    naturality _ _ g := by
      ext Y
      exact (((F.obj Y).map g).naturality h).symm }
  map_id G := by
    ext H K
    exact ((F.obj K).obj H).map_id G
  map_comp f g := by
    ext H K
    exact ((F.obj K).obj H).map_comp f g

/--
Flip the first and third arguments in a trifunctor, as a functor.
-/
def flip₁₃Functor : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₃ ⥤ C₂ ⥤ C₁ ⥤ E) where
  obj F := F.flip₁₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          exact NatTrans.congr_app (NatTrans.congr_app (f.naturality g) Y) X }
      naturality _ _ g := by
        ext Z
        exact NatTrans.congr_app ((f.app Z).naturality g) X }
    naturality _ _ g := by
      ext Y Z
      exact ((f.app Z).app Y).naturality g }
  map_id F := by
    ext X Y Z
    rfl
  map_comp f g := by
    ext X Y Z
    rfl

/--
Flip the second and third arguments in a trifunctor.
-/
abbrev flip₂₃ (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : C₁ ⥤ C₃ ⥤ C₂ ⥤ E where
  obj G := (F.obj G).flip
  map f := (flipFunctor _ _ _).map (F.map f)

@[simp]
lemma flip₂₃_obj_obj_obj (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (X : C₁) (Y : C₃) (Z : C₂) :
    ((F.flip₂₃.obj X).obj Y).obj Z = ((F.obj X).obj Z).obj Y := rfl

@[simp]
lemma flip₂₃_map_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) {X X' : C₁} (f : X ⟶ X')
    (Y : C₃) (Z : C₂) :
    ((F.flip₂₃.map f).app Y).app Z = ((F.map f).app Z).app Y := rfl

/--
Flip the second and third arguments in a trifunctor, as a functor.
-/
def flip₂₃Functor : (C₁ ⥤ C₂ ⥤ C₃ ⥤ E) ⥤ (C₁ ⥤ C₃ ⥤ C₂ ⥤ E) where
  obj F := F.flip₂₃
  map f := {
    app X := {
      app Y := {
        app Z := ((f.app _).app _).app _
        naturality _ _ g := by
          simp [← NatTrans.comp_app] } }
    naturality _ _ g := by
      ext
      simp only [flip₂₃_obj_obj_obj, NatTrans.comp_app, flip₂₃_map_app_app]
      simp [← NatTrans.comp_app] }

end CategoryTheory.Functor

namespace CategoryTheory.BraidedCategory

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

variable (C) in
/-- The braiding isomorphism as a natural isomorphism of bifunctors `C ⥤ C ⥤ C`. -/
def curriedBraidingNatIso : curriedTensor C ≅ (curriedTensor C).flip :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ β_ X Y))

@[simp]
lemma curriedBraidingNatIso_hom_app_app (X Y : C) :
    ((curriedBraidingNatIso C).hom.app X).app Y = (β_ X Y).hom := rfl

end CategoryTheory.BraidedCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

open MonoidalCategory CategoryTheory.Functor

namespace BraidedCategory

namespace Hexagon

variable (C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₂) ⊗ X₃` -/
def functor₁₂₃ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₂ ⊗ X₃)` -/
def functor₁₂₃' : C ⥤ C ⥤ C ⥤ C := bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₃) ⊗ X₁` -/
def functor₂₃₁ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₃ ⊗ X₁)` -/
def functor₂₃₁' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₁) ⊗ X₃` -/
def functor₂₁₃ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₁ ⊗ X₃)` -/
def functor₂₁₃' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

/-- The trifunctor `X₁ X₂ X₃ ↦ X₃ ⊗ (X₁ ⊗ X₂)` -/
def functor₃₁₂' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₃ ⊗ X₁) ⊗ X₂` -/
def functor₃₁₂ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₃ ⊗ X₂)` -/
def functor₁₃₂' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₃) ⊗ X₂` -/
def functor₁₃₂ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip₂₃

end Hexagon

open Hexagon

namespace ofBifunctor

namespace Forward


/-- The middle left map in the forward hexagon identity. -/
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃' C ⟶ functor₂₃₁ C :=
  (bifunctorComp₂₃Functor.map β.hom).app _

variable (C) in
/-- The bottom left map in the forward hexagon identity. -/
def firstMap₃ : functor₂₃₁ C ⟶ functor₂₃₁' C :=
  flip₁₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).hom)

/-- The top right map in the forward hexagon identity. -/
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃ C ⟶ functor₂₁₃ C :=
  (bifunctorComp₁₂Functor.map β.hom).app _

variable (C) in
/-- The middle right map in the forward hexagon identity. -/
def secondMap₂ : functor₂₁₃ C ⟶ functor₂₁₃' C :=
  (flipFunctor _ _ _).map (curriedAssociatorNatIso C).hom

/-- The bottom right map in the forward hexagon identity. -/
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₂₁₃' C ⟶ functor₂₃₁' C :=
  flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))

end Forward

namespace Reverse


/-- The middle left map in the reverse hexagon identity. -/
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃ C ⟶ functor₃₁₂' C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map ((bifunctorComp₂₃Functor.map
    ((flipFunctor _ _ _).map β.hom)).app _))

variable (C) in
/-- The bottom left map in the reverse hexagon identity. -/
def firstMap₃ : functor₃₁₂' C ⟶ functor₃₁₂ C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).inv)

/-- The top right map in the reverse hexagon identity. -/
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃' C ⟶ functor₁₃₂' C :=
  (bifunctorComp₂₃Functor.obj _).map β.hom

variable (C) in
/-- The middle right map in the reverse hexagon identity. -/
def secondMap₂ : functor₁₃₂' C ⟶ functor₁₃₂ C :=
  flip₂₃Functor.map (curriedAssociatorNatIso C).inv

/-- The bottom right map in the reverse hexagon identity. -/
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₃₂ C ⟶ functor₃₁₂ C :=
  flip₂₃Functor.map ((bifunctorComp₁₂Functor.map β.hom).app _)

end Reverse

end ofBifunctor

open ofBifunctor

variable (β : curriedTensor C ≅ (curriedTensor C).flip)
  (hexagon_forward : (curriedAssociatorNatIso C).hom ≫
    Forward.firstMap₂ β ≫ Forward.firstMap₃ C =
    Forward.secondMap₁ β ≫ Forward.secondMap₂ C ≫ Forward.secondMap₃ β)
  (hexagon_reverse : (curriedAssociatorNatIso C).inv ≫
    Reverse.firstMap₂ β ≫ Reverse.firstMap₃ C =
    Reverse.secondMap₁ β ≫ Reverse.secondMap₂ C ≫ Reverse.secondMap₃ β)

/--
Given a braiding `β : curriedTensor C ≅ (curriedTensor C).flip` as a natural isomorphism between
bifunctors, and the two equalities `hexagon_forward` and `hexagon_reverse` of natural
transformations between trifunctors, we obtain a braided category structure.
-/
abbrev ofBifunctor : BraidedCategory C where
  braiding X Y := (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse X Y Z :=
    (NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_reverse X) Y) Z)

end BraidedCategory

open BraidedCategory

/--
Alternative constructor for symmetric categories, where the symmetry of the braiding is phrased
as an equality of natural transformation of bifunctors.
-/
abbrev SymmetricCategory.ofCurried [BraidedCategory C]
    (h : (curriedBraidingNatIso C).hom ≫ (flipFunctor _ _ _).map (curriedBraidingNatIso C).hom =
      𝟙 _) :
    SymmetricCategory C where
  symmetry X Y := NatTrans.congr_app (NatTrans.congr_app h X) Y

end CategoryTheory

namespace CategoryTheory

open Category MonoidalCategory Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
  (W : MorphismProperty C) [MonoidalCategory C] [W.IsMonoidal]
  [L.IsLocalization W] {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

lemma associator_hom (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom =
    (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
      (Functor.LaxMonoidal.μ (L') (X ⊗ Y) Z) ≫
        (L').map (α_ X Y Z).hom ≫
          (Functor.OplaxMonoidal.δ (L') X (Y ⊗ Z)) ≫
            ((L').obj X) ◁ (Functor.OplaxMonoidal.δ (L') Y Z) := by
  simp

lemma associator_inv (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv =
    (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
      (Functor.LaxMonoidal.μ (L') X (Y ⊗ Z)) ≫
        (L').map (α_ X Y Z).inv ≫
          (Functor.OplaxMonoidal.δ (L') (X ⊗ Y) Z) ≫
            (Functor.OplaxMonoidal.δ (L') X Y) ▷ ((L').obj Z) := by
  simp

end CategoryTheory

open CategoryTheory Category MonoidalCategory BraidedCategory Functor

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C] [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

section Braided

variable [BraidedCategory C]

noncomputable instance : Lifting₂ L' L' W W ((curriedTensor C).flip ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L') (tensorBifunctor L W ε).flip :=
  inferInstanceAs (Lifting₂ L' L' W W (((curriedTensor C) ⋙ (whiskeringRight C C
    (LocalizedMonoidal L W ε)).obj L')).flip (tensorBifunctor L W ε).flip)

/-- The braiding on the localized category as a natural isomorphism of bifunctors. -/
noncomputable def braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip :=
  lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _ (isoWhiskerRight (curriedBraidingNatIso C) _)

lemma braidingNatIso_hom_app (X Y : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y) =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) := by
  simp [braidingNatIso, lift₂NatIso]; rfl

@[reassoc]
lemma braidingNatIso_hom_app_naturality_μ_left (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y ⊗ (L').obj Z) ≫
      (Functor.LaxMonoidal.μ (L') Y Z) ▷ (L').obj X =
        (L').obj X ◁ (Functor.LaxMonoidal.μ (L') Y Z) ≫
          ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj (Y ⊗ Z)) :=
  (((braidingNatIso L W ε).hom.app ((L').obj X)).naturality ((Functor.LaxMonoidal.μ (L') Y Z))).symm

@[reassoc]
lemma braidingNatIso_hom_app_naturality_μ_right (X Y Z : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z) ≫
      (L').obj Z ◁ (Functor.LaxMonoidal.μ (L') X Y) =
        (Functor.LaxMonoidal.μ (L') X Y) ▷ (L').obj Z ≫
          ((braidingNatIso L W ε).hom.app ((L').obj (X ⊗ Y))).app ((L').obj Z) :=
  (NatTrans.congr_app ((braidingNatIso L W ε).hom.naturality
    ((Functor.LaxMonoidal.μ (L') X Y))) ((L').obj Z)).symm

@[reassoc]
lemma map_hexagon_forward (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom ≫
      (((braidingNatIso L W ε).app ((L').obj X)).app (((L').obj Y) ⊗ ((L').obj Z))).hom ≫
        (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom =
      (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Y)).hom ▷ ((L').obj Z) ≫
        (α_ ((L').obj Y) ((L').obj X) ((L').obj Z)).hom ≫
        ((L').obj Y) ◁ (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom := by
  simp only [associator_hom, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_whiskerRight, assoc,
      Functor.Monoidal.whiskerRight_δ_μ_assoc, Functor.LaxMonoidal.μ_natural_left]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_left, braidingNatIso_hom_app]
  simp

@[reassoc]
lemma map_hexagon_reverse (X Y Z : C) :
    (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv ≫
      (((braidingNatIso L W ε).app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv =
      ((L').obj X) ◁ (((braidingNatIso L W ε).app ((L').obj Y)).app ((L').obj Z)).hom ≫
        (α_ ((L').obj X) ((L').obj Z) ((L').obj Y)).inv ≫
        (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom ▷ ((L').obj Y) := by
  simp only [associator_inv, Iso.app_hom, braidingNatIso_hom_app]
  slice_rhs 0 4 =>
    simp only [Functor.flip_obj_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, MonoidalCategory.whiskerLeft_comp, assoc,
      Functor.Monoidal.whiskerLeft_δ_μ, comp_id]
  slice_lhs 6 7 =>
    rw [braidingNatIso_hom_app_naturality_μ_right, braidingNatIso_hom_app]
  simp

noncomputable instance : BraidedCategory (LocalizedMonoidal L W ε) := by
  refine .ofBifunctor (braidingNatIso L W ε) ?_ ?_
  · apply natTrans₃_ext (L') (L') (L') W W W
    intro X Y Z
    change (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).hom ≫
      (((braidingNatIso L W ε).app ((L').obj X)).app
        (((L').obj Y) ⊗ ((L').obj Z))).hom ≫
      (α_ ((L').obj Y) ((L').obj Z) ((L').obj X)).hom =
      (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Y)).hom ▷ ((L').obj Z) ≫
      (α_ ((L').obj Y) ((L').obj X) ((L').obj Z)).hom ≫
      ((L').obj Y) ◁ (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom
    exact map_hexagon_forward L W ε X Y Z
  · apply natTrans₃_ext (L') (L') (L') W W W
    intro X Y Z
    change (α_ ((L').obj X) ((L').obj Y) ((L').obj Z)).inv ≫
      (((braidingNatIso L W ε).app ((L').obj X ⊗ (L').obj Y)).app ((L').obj Z)).hom ≫
      (α_ ((L').obj Z) ((L').obj X) ((L').obj Y)).inv =
      ((L').obj X) ◁ (((braidingNatIso L W ε).app ((L').obj Y)).app ((L').obj Z)).hom ≫
      (α_ ((L').obj X) ((L').obj Z) ((L').obj Y)).inv ≫
      (((braidingNatIso L W ε).app ((L').obj X)).app ((L').obj Z)).hom ▷ ((L').obj Y)
    exact map_hexagon_reverse L W ε X Y Z

lemma β_hom_app (X Y : C) :
    (β_ ((L').obj X) ((L').obj Y)).hom =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) :=
  braidingNatIso_hom_app L W ε X Y

noncomputable instance : (toMonoidalCategory L W ε).Braided where
  braided X Y := by simp [β_hom_app]

end Braided

section Symmetric

variable [SymmetricCategory C]

noncomputable instance : SymmetricCategory (LocalizedMonoidal L W ε) := by
  refine .ofCurried (natTrans₂_ext (L') (L') W W fun X Y ↦ ?_)
  simp [-Functor.map_braiding, β_hom_app, ← Functor.map_comp_assoc]

end Symmetric

end CategoryTheory.Localization.Monoidal
