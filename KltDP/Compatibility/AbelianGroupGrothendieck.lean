/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Original authors: David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn,
Amelia Livingston, Joël Riou
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Abelian sheaves as Grothendieck categories with small Ext groups

This file adapts the following declarations from Mathlib revision
`5aedf732b6987e8c26ab3c9ebc855314f82b045f`:

* `Mathlib/Algebra/Category/Grp/AB.lean`, lines 100–108: a separator and the
  Grothendieck abelian instance for abelian groups;
* `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean`: the
  instance `CategoryTheory.IsGrothendieckAbelian.hasExt`.

The separator proof uses the pinned `AddCommGrp.coyonedaObjIsoForget`
instead of repeating the upstream elementwise proof. The pinned AB5,
sheaf-category, and enough-injectives results supply the other steps.
For a space with points in `Type u`, the resulting Ext groups of abelian
sheaves lie in `Type u`, not the larger universe of sheaf objects.
No coherent-cohomology finiteness statement is asserted here.
-/

open CategoryTheory

universe u v w

namespace AddCommGrp

/-- The lifted integers separate morphisms of abelian groups. -/
theorem isSeparator_uliftInt : IsSeparator (of (ULift.{u} ℤ)) :=
  (isSeparator_iff_faithful_coyoneda_obj _).2
    (Functor.Faithful.of_iso coyonedaObjIsoForget.symm)

instance hasSeparator : HasSeparator AddCommGrp.{u} where
  hasSeparator := ⟨of (ULift.{u} ℤ), isSeparator_uliftInt⟩

instance isGrothendieckAbelian : IsGrothendieckAbelian.{u} AddCommGrp.{u} where

end AddCommGrp

namespace CategoryTheory

/-- Ext groups in a Grothendieck abelian category have the universe of
its small morphism types. -/
instance IsGrothendieckAbelian.hasExt
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasExt.{w} C :=
  hasExt_of_enoughInjectives _

end CategoryTheory

namespace KltDP.Compatibility

/-- Abelian sheaves on a space in `Type u` have Ext groups in `Type u`.
This applies to the underlying space of a `TopCat.{u}` or `Scheme.{u}`. -/
theorem hasExt_opensSheaf (X : Type u) [TopologicalSpace X] :
    HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrp.{u}) := by
  infer_instance

end KltDP.Compatibility
