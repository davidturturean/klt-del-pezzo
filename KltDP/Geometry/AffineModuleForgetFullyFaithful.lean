/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The proof is adapted from SpecModulesToSheafFullyFaithful in Mathlib
AlgebraicGeometry/Modules/Tilde.lean at
633b366493a76df88a2bff099ed0cbf711a59ec9, lines 54-83.
-/
import KltDP.Geometry.AffineModuleGlobalSections
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The affine forgetful functor is fully faithful

On a basic open, an R-linear map of sections is linear over the original
localized section ring. Local equality of sheaf sections extends this
linearity to every open. Thus a morphism of the original sheaves of
R-modules determines a unique morphism over the original structure sheaf.
All auxiliary scalar instances below retain the original actions and are local to this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R]
  {M N : (Spec (CommRingCat.of R)).Modules}

local instance forgetSectionRingModule (P : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Module (Γ(Spec (CommRingCat.of R), U)) (sectionModule P U) :=
  (P.val.obj (op U)).isModule

local instance forgetStructureSheafModule (P : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Module ((Spec.structureSheaf R).val.obj (op U)) (sectionModule P U) :=
  (P.val.obj (op U)).isModule

local instance forgetSectionRingAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R (Γ(Spec (CommRingCat.of R), U)) :=
  StructureSheaf.openAlgebra R (op U)

local instance forgetBasicOpenLocalization (r : R) :
    IsLocalization.Away r (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r)) :=
  StructureSheaf.IsLocalization.to_basicOpen R r

/-- On D(r), the original R-linear section map respects every section-ring scalar. -/
theorem moduleSheafHom_basicOpen_smul
    (φ : (modulesSpecToSheaf R).obj M ⟶ (modulesSpecToSheaf R).obj N)
    (r : R) (a : Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r))
    (m : sectionModule M (PrimeSpectrum.basicOpen r)) :
    φ.val.app (op (PrimeSpectrum.basicOpen r))
        (a • (m : M.val.obj (op (PrimeSpectrum.basicOpen r)))) =
      a • (φ.val.app (op (PrimeSpectrum.basicOpen r)) m :
        N.val.obj (op (PrimeSpectrum.basicOpen r))) := by
  letI : IsScalarTower R (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r))
      (sectionModule M (PrimeSpectrum.basicOpen r)) :=
    IsScalarTower.of_algebraMap_smul (R := R)
      (A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r))
      (M := sectionModule M (PrimeSpectrum.basicOpen r)) (fun c m =>
      (sectionModule_smul_toOpen M (PrimeSpectrum.basicOpen r) c m).symm)
  letI : IsScalarTower R (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r))
      (sectionModule N (PrimeSpectrum.basicOpen r)) :=
    IsScalarTower.of_algebraMap_smul (R := R)
      (A := Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r))
      (M := sectionModule N (PrimeSpectrum.basicOpen r)) (fun c m =>
      (sectionModule_smul_toOpen N (PrimeSpectrum.basicOpen r) c m).symm)
  exact (IsLocalization.linearMap_compatibleSMul (Submonoid.powers r)
    (Γ(Spec (CommRingCat.of R), PrimeSpectrum.basicOpen r))
    (sectionModule M (PrimeSpectrum.basicOpen r))
    (sectionModule N (PrimeSpectrum.basicOpen r))).map_smul
      (φ.val.app (op (PrimeSpectrum.basicOpen r))).hom a m

/-- Local section-ring linearity implies the original section-ring linearity on every open. -/
theorem moduleSheafHom_smul
    (φ : (modulesSpecToSheaf R).obj M ⟶ (modulesSpecToSheaf R).obj N)
    (U : (Spec (CommRingCat.of R)).Opens) (a : Γ(Spec (CommRingCat.of R), U))
    (m : sectionModule M U) :
    φ.val.app (op U) (a • (m : M.val.obj (op U))) =
      a • (φ.val.app (op U) m : N.val.obj (op U)) := by
  apply TopCat.Presheaf.IsSheaf.section_ext ((modulesSpecToSheaf R).obj N).cond
  intro x hxU
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  refine ⟨PrimeSpectrum.basicOpen r, hrU, hxr, ?_⟩
  have hnat (v : sectionModule M U) :
      φ.val.app (op (PrimeSpectrum.basicOpen r)) (M.val.map (homOfLE hrU).op v) =
        N.val.map (homOfLE hrU).op (φ.val.app (op U) v) :=
    ConcreteCategory.congr_hom (φ.val.naturality (homOfLE hrU).op) v
  change N.val.map (homOfLE hrU).op
      (φ.val.app (op U) (a • (m : M.val.obj (op U)))) =
    N.val.map (homOfLE hrU).op (a • (φ.val.app (op U) m : N.val.obj (op U)))
  rw [N.val.map_smul, ← hnat, ← hnat, M.val.map_smul]
  exact moduleSheafHom_basicOpen_smul φ r
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hrU).op a)
    (M.val.map (homOfLE hrU).op m)

/-- Recover the actual structure-sheaf-module morphism from its R-linear sheaf map. -/
def moduleSheafHomPreimage
    (φ : (modulesSpecToSheaf R).obj M ⟶ (modulesSpecToSheaf R).obj N) : M ⟶ N where
  val := {
    app U := ModuleCat.ofHom {
      toFun := φ.val.app U
      map_add' m n := (φ.val.app U).hom.map_add m n
      map_smul' a m := moduleSheafHom_smul φ U.unop a m }
    naturality i := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      exact ConcreteCategory.congr_hom (φ.val.naturality i) m }

@[simp]
theorem moduleSheafHomPreimage_app
    (φ : (modulesSpecToSheaf R).obj M ⟶ (modulesSpecToSheaf R).obj N)
    (U : (Spec (CommRingCat.of R)).Opens) (m : M.val.obj (op U)) :
    (moduleSheafHomPreimage φ).val.app (op U) m = φ.val.app (op U) m := rfl

/-- Forgetting to the original sheaves of R-modules is fully faithful. -/
def modulesSpecToSheafFullyFaithful (R : Type u) [CommRing R] :
    (modulesSpecToSheaf R).FullyFaithful where
  preimage := moduleSheafHomPreimage
  map_preimage φ := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  preimage_map φ := by
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

end KltDP.Geometry.AffineModuleTilde
