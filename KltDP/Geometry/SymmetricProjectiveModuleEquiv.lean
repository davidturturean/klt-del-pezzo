/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SymmetricAlgebra.Map
import KltDP.Geometry.SymmetricProjectiveSpaceComparison

/-!
# Original symmetric Proj under an original module equivalence

The functorial symmetric algebra preserves the intrinsic grading. Applying
the proved homogeneous-localization construction therefore gives an actual
scheme isomorphism. The equation with the original field structure maps is
proved from the original algebra constants, independently of any basis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SymmetricProjectiveModuleEquiv

open KltDP.SymmetricAlgebra SymmetricProjectiveSpace

variable {k M N : Type u} [Field k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The actual symmetric Proj isomorphism induced by a module equivalence. -/
def iso (e : M ≃ₗ[k] N) : Proj (grading k M) ≅ Proj (grading k N) :=
  GradedProjIso.iso (𝒜 := grading k M) (ℬ := grading k N)
    (congr e).toRingEquiv (fun n x => (congr_mem_grading_iff e n x).symm)

/-- The induced isomorphism retains the original morphisms to the field. -/
theorem iso_structure (e : M ≃ₗ[k] N) :
    (iso e).hom ≫ structureMap k N = structureMap k M := by
  apply GradedProjIso.iso_hom_comp_toSpecBase
    (e := (congr e).toRingEquiv)
    (he := fun n x => (congr_mem_grading_iff e n x).symm)
    (constants k M) (constants k N)
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change (congr e).symm (algebraMap k (KltDP.SymmetricAlgebra k N) a) =
    algebraMap k (KltDP.SymmetricAlgebra k M) a
  exact (congr e).symm.commutes a

/-- The inverse also preserves the displayed original structure map. -/
theorem iso_inv_structure (e : M ≃ₗ[k] N) :
    (iso e).inv ≫ structureMap k M = structureMap k N := by
  rw [← iso_structure e, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- On the original projective points the map is the comap of the inverse
actual symmetric-algebra equivalence. -/
theorem iso_hom_apply (e : M ≃ₗ[k] N) (x : Proj (grading k M)) :
    (iso e).hom.base x = GradedProjIso.comapPoint (congr e).toRingEquiv.symm
      (GradedProjIso.preservesDegrees_symm (congr e).toRingEquiv
        (fun n y => (congr_mem_grading_iff e n y).symm)) x := rfl

end KltDP.Geometry.SymmetricProjectiveModuleEquiv
