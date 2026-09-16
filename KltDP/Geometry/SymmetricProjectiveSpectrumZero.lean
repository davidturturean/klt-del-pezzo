/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SymmetricAlgebra.Grading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The actual rank-zero symmetric projective spectrum

For a zero module, every element of its actual symmetric algebra has degree
zero. Hence the irrelevant ideal is zero and the original projective spectrum
has no points. A map from a nonempty scheme to this actual Proj therefore
forces the original module to be nontrivial, and its dimension is positive
when the module is finite over a field. No projective-space convention or
chosen model is used in the rank-zero branch.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.SymmetricAlgebra

universe u

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

/-- If the original module is zero, its whole symmetric algebra is degree zero. -/
theorem mem_grading_zero_of_subsingleton [Subsingleton M]
    (x : SymmetricAlgebra R M) : x ∈ grading R M 0 := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact Submodule.algebraMap_mem r
  | ι m =>
    rw [Subsingleton.elim m 0, map_zero]
    exact (grading R M 0).zero_mem
  | mul x y hx hy => exact SetLike.mul_mem_graded hx hy
  | add x y hx hy => exact (grading R M 0).add_mem hx hy

/-- The actual symmetric Proj of a zero module is empty. -/
theorem isEmpty_proj_of_subsingleton [Subsingleton M] :
    IsEmpty (Proj (grading R M)) := by
  refine ⟨fun x => x.not_irrelevant_le ?_⟩
  intro a ha
  have hzero := (HomogeneousIdeal.mem_irrelevant_iff (grading R M) a).mp ha
  change (DirectSum.decompose (grading R M) a 0 : SymmetricAlgebra R M) = 0 at hzero
  rw [DirectSum.decompose_of_mem_same (grading R M)
    (mem_grading_zero_of_subsingleton a)] at hzero
  rw [hzero]
  exact x.asHomogeneousIdeal.zero_mem

/-- A map from a nonempty actual scheme into the actual symmetric Proj excludes
the zero module. No injectivity or projectivity premise is needed. -/
theorem nontrivial_of_morphism {X : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Proj (grading R M)) : Nontrivial M := by
  classical
  rcases subsingleton_or_nontrivial M with hM | hM
  · letI : Subsingleton M := hM
    letI : IsEmpty (Proj (grading R M)) := isEmpty_proj_of_subsingleton
    exact isEmptyElim (f.base (Classical.choice (inferInstance : Nonempty X)))
  · exact hM

end KltDP.SymmetricAlgebra

namespace KltDP.SymmetricAlgebra

universe u

variable {k M : Type u} [Field k] [AddCommGroup M] [Module k M]

/-- The same map gives the positive rank needed to index a projective space;
this branch cannot silently replace rank zero by natural subtraction. -/
theorem finrank_pos_of_morphism [Module.Finite k M]
    {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Proj (grading k M)) :
    0 < Module.finrank k M := by
  letI : Nontrivial M := nontrivial_of_morphism f
  exact Module.finrank_pos

end KltDP.SymmetricAlgebra
