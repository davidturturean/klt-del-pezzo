/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

The cokernel comparison follows Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
SchemeModuleCohomologyAffineExact.lean:100-139. The kernel comparison
uses the project's proved original localization-defined kernelIso.
-/
import KltDP.Geometry.AffineQuasicoherentGlobalSections
import KltDP.Geometry.AffineModuleTildePresentation
import KltDP.Geometry.AffineModuleTildeKernel

/-!
# Original affine quasicoherent kernels and cokernels

The actual counit square compares an original quasicoherent sheaf map
with the tilde of its original global-section map. The previously proved
kernel comparison and left-adjoint cokernel comparison retain the actual
kernel inclusion and cokernel projection. Their original module sources
are tilde sheaves, whose quasicoherence has now been proved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]
variable {M N : (Spec (.of R)).Modules} (f : M ⟶ N)
variable [M.IsQuasicoherent] [N.IsQuasicoherent]

/-- The actual module kernel gives the original sheaf kernel through the actual counit square. -/
def quasicoherentKernelIso :
    (kernel ((globalSectionsFunctor R).map f)).tilde ≅ kernel f := by
  letI : IsIso (counit M) := counit_isIso_of_isQuasicoherent M
  letI : IsIso (counit N) := counit_isIso_of_isQuasicoherent N
  exact kernelIso ((globalSectionsFunctor R).map f) ≪≫
    kernel.mapIso _ f (asIso (counit M)) (asIso (counit N)) (counit_naturality f)

/-- The comparison preserves the original kernel inclusion, followed by the original counit. -/
theorem quasicoherentKernelIso_hom_ι :
    (quasicoherentKernelIso f).hom ≫ kernel.ι f =
      (functor R).map (kernel.ι ((globalSectionsFunctor R).map f)) ≫ counit M := by
  simp only [quasicoherentKernelIso, Iso.trans_hom, Category.assoc,
    kernel.mapIso_hom, kernel.map, kernel.lift_ι, asIso_hom]
  rw [← Category.assoc, kernelIso_hom_ι]

/-- The original categorical kernel of a morphism of affine quasicoherent sheaves is quasicoherent. -/
theorem kernel_isQuasicoherent : (kernel f).IsQuasicoherent := by
  letI := tilde_isQuasicoherent (kernel ((globalSectionsFunctor R).map f))
  exact _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := (Spec (.of R)).ringCatSheaf)
    (M := (kernel ((globalSectionsFunctor R).map f)).tilde) (N := kernel f)
    (quasicoherentKernelIso f).hom

set_option maxHeartbeats 800000 in
/-- The actual module cokernel gives the original sheaf cokernel through the same counit square. -/
def quasicoherentCokernelIso :
    (cokernel ((globalSectionsFunctor R).map f)).tilde ≅ cokernel f := by
  letI : IsIso (counit M) := counit_isIso_of_isQuasicoherent M
  letI : IsIso (counit N) := counit_isIso_of_isQuasicoherent N
  exact PreservesCokernel.iso (functor R) ((globalSectionsFunctor R).map f) ≪≫
    cokernel.mapIso ((functor R).map ((globalSectionsFunctor R).map f)) f
      (asIso (counit M)) (asIso (counit N)) (counit_naturality f)

/-- The comparison retains the original cokernel projection and original target counit. -/
theorem quasicoherentCokernelIso_π_hom :
    (functor R).map (cokernel.π ((globalSectionsFunctor R).map f)) ≫
        (quasicoherentCokernelIso f).hom = counit N ≫ cokernel.π f := by
  simp only [quasicoherentCokernelIso, Iso.trans_hom, ← Category.assoc,
    PreservesCokernel.π_iso_hom, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc,
    asIso_hom]

/-- The original categorical cokernel is quasicoherent. -/
theorem cokernel_isQuasicoherent : (cokernel f).IsQuasicoherent := by
  letI := tilde_isQuasicoherent (cokernel ((globalSectionsFunctor R).map f))
  exact _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := (Spec (.of R)).ringCatSheaf)
    (M := (cokernel ((globalSectionsFunctor R).map f)).tilde) (N := cokernel f)
    (quasicoherentCokernelIso f).hom

/-- The original Ext-based H0 map of that actual cokernel projection is surjective. -/
theorem hZero_surjective_cokernel_π :
    Function.Surjective
      ((ModuleCohomology.zariskiFunctor (Spec (.of R)) 0).map (cokernel.π f)) := by
  letI := cokernel_isQuasicoherent f
  exact hZero_surjective_of_epi (cokernel.π f)

end KltDP.Geometry.AffineModuleTilde
