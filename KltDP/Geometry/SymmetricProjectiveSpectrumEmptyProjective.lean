/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.SymmetricProjectiveSpaceComparison
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite-module symmetric Proj is projective, including rank zero

The actual symmetric Proj of a zero module is empty. The pinned initial-object
map embeds any empty scheme as a closed subscheme of the existing projective
zero-space. Uniqueness of maps from the original empty scheme supplies the
original structure-map equation.

Combining this branch with the compiled positive-dimensional basis comparison
gives projectivity for every finite field module. Its closed-immersion consumer
requires no nonempty source or nonzero module hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SymmetricProjectiveSpectrumEmptyProjective

open KltDP.SymmetricAlgebra
open SymmetricProjectiveSpace

variable {k : Type u} [Field k]

/-- The actual empty scheme embeds as a closed subscheme of the existing `P⁰`.
The original map to the field is preserved by initial-object uniqueness. -/
theorem isProjectiveOverField_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (f : X ⟶ Spec (CommRingCat.of k)) : IsProjectiveOverField f := by
  let i : X ⟶ projectiveSpace k 0 :=
    (AlgebraicGeometry.isInitialOfIsEmpty (X := X)).to (projectiveSpace k 0)
  refine ⟨0, i, inferInstance, ?_⟩
  exact (AlgebraicGeometry.isInitialOfIsEmpty (X := X)).hom_ext _ _

variable (k) (M : Type u) [AddCommGroup M] [Module k M]

/-- The genuine rank-zero symmetric Proj is projective via its empty embedding. -/
theorem structureMap_isProjective_of_subsingleton [Subsingleton M] :
    IsProjectiveOverField (structureMap k M) := by
  letI : IsEmpty (Proj (grading k M)) :=
    KltDP.SymmetricAlgebra.isEmpty_proj_of_subsingleton
  exact isProjectiveOverField_of_isEmpty (structureMap k M)

/-- The original symmetric Proj structure map is projective for every finite
field module, with the zero and positive-dimensional cases both proved. -/
theorem structureMap_isProjective [Module.Finite k M] :
    IsProjectiveOverField (structureMap k M) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · letI : Subsingleton M := hM
    exact structureMap_isProjective_of_subsingleton k M
  · letI : Nontrivial M := hM
    exact SymmetricProjectiveSpace.structureMap_isProjective k M

variable {k M}

/-- A closed subscheme of the actual finite-module symmetric Proj is projective.
The source and the module are allowed to be empty and zero, respectively. -/
theorem projective_of_closedImmersion [Module.Finite k M]
    {X : Scheme.{u}} (f : X ⟶ Proj (grading k M)) [IsClosedImmersion f] :
    IsProjectiveOverField (f ≫ structureMap k M) := by
  obtain ⟨n, i, hi, hstructure⟩ := structureMap_isProjective k M
  letI : IsClosedImmersion i := hi
  exact ⟨n, f ≫ i, inferInstance, by rw [Category.assoc, hstructure]⟩

/-- The same conclusion for a displayed original map to the field. -/
theorem projective_of_closedImmersion_over [Module.Finite k M]
    {X : Scheme.{u}} (f : X ⟶ Proj (grading k M)) [IsClosedImmersion f]
    (g : X ⟶ Spec (CommRingCat.of k)) (hfg : f ≫ structureMap k M = g) :
    IsProjectiveOverField g := by
  rw [← hfg]
  exact projective_of_closedImmersion f

end KltDP.Geometry.SymmetricProjectiveSpectrumEmptyProjective
