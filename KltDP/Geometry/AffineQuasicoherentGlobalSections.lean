/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/SchemeModuleCohomologyAffineExact.lean:53-95.
The original pinned tilde, counit, global sections and Ext-based H0 are
retained. The newer epi-cancellation helper is replaced by the pinned
Iso.eq_comp_inv identity on the original counit.
-/
import KltDP.Geometry.AffineQuasicoherentCounit
import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Geometry.ModuleCohomology
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Surjectivity of original affine quasicoherent global sections

The actual counit identifies each original quasicoherent sheaf with the
tilde of its original global sections. Naturality expresses the tilde of
the global-section map as the original sheaf map between these canonical
isomorphisms. Full faithfulness then reflects its epimorphism property.
The existing natural H0 comparison gives surjectivity on actual H0.

Positive-degree affine acyclicity and proper cohomology finiteness remain
separate results. No cohomology action is introduced or transported here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]
variable {M N : (Spec (.of R)).Modules} (f : M ⟶ N)
variable [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f]

/-- Actual affine global sections preserve an epimorphism between original
quasicoherent module sheaves. -/
theorem globalSections_epi_of_epi : Epi ((globalSectionsFunctor R).map f) := by
  letI : IsIso (counit M) := counit_isIso_of_isQuasicoherent M
  letI : IsIso (counit N) := counit_isIso_of_isQuasicoherent N
  have heq : map ((globalSectionsFunctor R).map f) =
      (counit M ≫ f) ≫ (asIso (counit N)).inv :=
    (Iso.eq_comp_inv (asIso (counit N))).mpr (counit_naturality f)
  have hcomp : Epi ((counit M ≫ f) ≫ (asIso (counit N)).inv) := inferInstance
  have hmapped : Epi ((functor R).map ((globalSectionsFunctor R).map f)) := by
    change Epi (map ((globalSectionsFunctor R).map f))
    rw [heq]
    exact hcomp
  exact (functor R).epi_of_epi_map hmapped

/-- The original section map at the top open is surjective. -/
theorem globalSections_surjective_of_epi :
    Function.Surjective (f.val.app (op (⊤ : (Spec (.of R)).Opens))) :=
  (ModuleCat.epi_iff_surjective ((globalSectionsFunctor R).map f)).mp
    (globalSections_epi_of_epi f)

/-- The existing Ext-based H0 functor is surjective on the same original map. -/
theorem hZero_surjective_of_epi :
    Function.Surjective ((ModuleCohomology.zariskiFunctor (Spec (.of R)) 0).map f) := by
  intro y
  obtain ⟨x, hx⟩ := globalSections_surjective_of_epi f
    (ModuleCohomology.hZeroEquivGlobalSections N y)
  refine ⟨(ModuleCohomology.hZeroEquivGlobalSections M).symm x, ?_⟩
  apply (ModuleCohomology.hZeroEquivGlobalSections N).injective
  rw [← ModuleCohomology.hZeroEquivGlobalSections_naturality]
  rw [(ModuleCohomology.hZeroEquivGlobalSections M).apply_symm_apply]
  exact hx

end KltDP.Geometry.AffineModuleTilde
