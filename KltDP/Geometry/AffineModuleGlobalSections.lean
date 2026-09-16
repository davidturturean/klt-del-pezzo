/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The actual forgetful functor and scalar properties are adapted from Mathlib
AlgebraicGeometry/Modules/Tilde.lean at
633b366493a76df88a2bff099ed0cbf711a59ec9, lines 35-120.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.RingTheory.Localization.Basic

/-!
# Original affine module sheaves as sheaves of base-ring modules

Restriction of scalars along the actual global-section isomorphism gives
a sheaf of R-modules on Spec R. Its section carriers, restriction functions,
and sheaf morphisms are the original ones. The bundled section modules keep
this base-ring action explicit without replacing the original section-ring
actions. Functions invertible on an open act invertibly on these modules.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

/-- Forget only to the original base-ring scalar action on an affine scheme. -/
def modulesSpecToSheaf (R : Type u) [CommRing R] :
    (Spec (CommRingCat.of R)).Modules ⥤
      TopCat.Sheaf (ModuleCat.{u} R) (Spec (CommRingCat.of R)) :=
  _root_.SheafOfModules.forgetToSheafModuleCat
    (R := (Spec (CommRingCat.of R)).ringCatSheaf) (op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

variable {R : Type u} [CommRing R]

/-- The actual sections, bundled with their canonical R-module action. -/
abbrev sectionModule (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) : ModuleCat.{u} R :=
  ((modulesSpecToSheaf R).obj M).val.obj (op U)

-- Retain the original section-ring action alongside the bundled base-ring action.
local instance originalSectionRingModule (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Module (Γ(Spec (CommRingCat.of R), U)) (sectionModule M U) :=
  (M.val.obj (op U)).isModule

-- The original toOpen map is typed through this structure-sheaf presentation.
local instance originalStructureSheafModule (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Module ((Spec.structureSheaf R).val.obj (op U)) (sectionModule M U) :=
  (M.val.obj (op U)).isModule

/-- The forgetful construction retains the original section carrier.
This is not a simp lemma because rewriting the carrier would hide its R-action. -/
theorem sectionModule_coe (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) :
    (sectionModule M U : Type u) = M.val.obj (op U) := rfl

/-- Base-ring scalars act through the original global sections and restriction. -/
theorem sectionModule_smul (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) (r : R) (s : sectionModule M U) :
    r • s = (Spec (CommRingCat.of R)).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) • (s : M.val.obj (op U)) := rfl

/-- The same action is given by the original canonical section on U. -/
theorem sectionModule_smul_toOpen (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) (r : R) (s : sectionModule M U) :
    r • s = StructureSheaf.toOpen R U r • (s : M.val.obj (op U)) := rfl

/-- The original restriction map is linear for the canonical R-actions. -/
def sectionRestrict (M : (Spec (CommRingCat.of R)).Modules)
    {U V : (Spec (CommRingCat.of R)).Opens} (h : V ≤ U) :
    sectionModule M U ⟶ sectionModule M V :=
  ((modulesSpecToSheaf R).obj M).val.map (homOfLE h).op

@[simp]
theorem sectionRestrict_apply (M : (Spec (CommRingCat.of R)).Modules)
    {U V : (Spec (CommRingCat.of R)).Opens} (h : V ≤ U) (s : sectionModule M U) :
    sectionRestrict M h s = M.val.map (homOfLE h).op s := rfl

/-- Restriction commutes with the original base-ring action. -/
theorem sectionRestrict_smul (M : (Spec (CommRingCat.of R)).Modules)
    {U V : (Spec (CommRingCat.of R)).Opens} (h : V ≤ U) (r : R)
    (s : sectionModule M U) :
    sectionRestrict M h (r • s) = r • sectionRestrict M h s :=
  (sectionRestrict M h).hom.map_smul r s

@[simp]
theorem modulesSpecToSheaf_map_app (M N : (Spec (CommRingCat.of R)).Modules)
    (φ : M ⟶ N) (U : (Spec (CommRingCat.of R)).Opens) (s : sectionModule M U) :
    ((modulesSpecToSheaf R).map φ).val.app (op U) s = φ.val.app (op U) s := rfl

/-- On a pinned tilde sheaf, the original R-module presheaf is retained literally. -/
@[simp]
theorem modulesSpecToSheaf_tilde (M : ModuleCat.{u} R) :
    ((modulesSpecToSheaf R).obj M.tilde).val = M.tildeInModuleCat := rfl

/-- The global-section functor uses the actual section module on the whole space. -/
def globalSectionsFunctor (R : Type u) [CommRing R] :
    (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf R ⋙ TopCat.Sheaf.forget _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op ⊤)

@[simp]
theorem globalSectionsFunctor_obj (M : (Spec (CommRingCat.of R)).Modules) :
    (globalSectionsFunctor R).obj M = sectionModule M ⊤ := rfl

@[simp]
theorem globalSectionsFunctor_map_apply {M N : (Spec (CommRingCat.of R)).Modules}
    (φ : M ⟶ N) (s : sectionModule M ⊤) :
    (globalSectionsFunctor R).map φ s = φ.val.app (op ⊤) s := rfl

/-- A function defining a basic open remains a unit on every smaller open. -/
theorem sectionRing_isUnit_of_le_basicOpen (f : R)
    {U : (Spec (CommRingCat.of R)).Opens} (hU : U ≤ PrimeSpectrum.basicOpen f) :
    IsUnit (StructureSheaf.toOpen R U f) := by
  have h := (StructureSheaf.isUnit_to_basicOpen_self R f).map
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hU).op).hom
  change IsUnit ((StructureSheaf.toOpen R (PrimeSpectrum.basicOpen f) ≫
    (AlgebraicGeometry.Spec.structureSheaf R).val.map (homOfLE hU).op) f) at h
  rw [StructureSheaf.toOpen_res] at h
  exact h

/-- Such a function acts invertibly on the original module of sections. -/
theorem sectionScalar_isUnit_of_le_basicOpen (M : (Spec (CommRingCat.of R)).Modules)
    (f : R) {U : (Spec (CommRingCat.of R)).Opens}
    (hU : U ≤ PrimeSpectrum.basicOpen f) :
    IsUnit (algebraMap R (Module.End R (sectionModule M U)) f) := by
  rw [Module.End.isUnit_iff]
  have h := (sectionRing_isUnit_of_le_basicOpen f hU).smul_bijective
    (β := M.val.obj (op U))
  have hfun : (fun s : sectionModule M U =>
      StructureSheaf.toOpen R U f • (s : M.val.obj (op U))) = (fun s => f • s) :=
    funext (fun s => (sectionModule_smul_toOpen M U f s).symm)
  change Function.Bijective (fun s : sectionModule M U =>
    StructureSheaf.toOpen R U f • (s : M.val.obj (op U))) at h
  rw [hfun] at h
  exact h

/-- The same unit property holds for every power of the defining function. -/
theorem sectionScalar_map_units (M : (Spec (CommRingCat.of R)).Modules)
    (f : R) {U : (Spec (CommRingCat.of R)).Opens}
    (hU : U ≤ PrimeSpectrum.basicOpen f) (s : Submonoid.powers f) :
    IsUnit (algebraMap R (Module.End R (sectionModule M U)) s) := by
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact (sectionScalar_isUnit_of_le_basicOpen M f hU).pow n

end KltDP.Geometry.AffineModuleTilde
