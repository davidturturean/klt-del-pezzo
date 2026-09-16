/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

This is the basic-open construction of the tilde-Gamma counit from
Mathlib at 633b366493a76df88a2bff099ed0cbf711a59ec9, adapted to the
pinned original tilde objects. Naturality uses units on actual subopens.
-/
import KltDP.Geometry.AffineModuleGlobalSections
import KltDP.Geometry.AffineModuleTildeLocalization
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The affine global-section counit on the original basic opens

Restriction of an actual global section to D(f) extends uniquely across
the localization of its module. These extensions agree under the original
restriction maps. The pinned basis extension theorem glues them to a
morphism of sheaves of R-modules, with an explicit canonical-section law.

Structure-sheaf linearity is packaged separately through the proved fully
faithful forgetful functor. No counit isomorphism is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)

-- Keep the original R-action visible on the intermediate forgotten carrier.
local instance counitForgottenTildeModule (N : ModuleCat.{u} R)
    (U : (Spec (.of R)).Opens) :
    Module R
      (((_root_.PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
        (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj N.tilde.val).obj (op U)) :=
  (N.tildeInModuleCat.obj (op U)).isModule

/-- Localization of the original restriction from global sections to D(f). -/
def counitBasicOpen (f : R) :
    (sectionModule M ⊤).tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)) ⟶
      sectionModule M (PrimeSpectrum.basicOpen f) :=
  ModuleCat.ofHom
    (X := (sectionModule M ⊤).tildeInModuleCat.obj (op (PrimeSpectrum.basicOpen f)))
    (Y := sectionModule M (PrimeSpectrum.basicOpen f))
    (IsLocalizedModule.lift (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom
    (sectionRestrict M le_top).hom (sectionScalar_map_units M f le_rfl))

@[simp]
theorem counitBasicOpen_toOpen (f : R) (m : sectionModule M ⊤) :
    counitBasicOpen M f
        (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m) =
      sectionRestrict M le_top m :=
  IsLocalizedModule.lift_apply (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom
    (sectionRestrict M le_top).hom (sectionScalar_map_units M f le_rfl) m

/-- The localized restrictions agree on actual contained basic opens. -/
theorem counitBasicOpen_naturality (f g : R)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    (sectionModule M ⊤).tildeInModuleCat.map (homOfLE h).op ≫ counitBasicOpen M g =
      counitBasicOpen M f ≫ sectionRestrict M h := by
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (Submonoid.powers f)
    (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f)).hom
    (sectionScalar_map_units M f h)
  apply LinearMap.ext
  intro m
  change counitBasicOpen M g
      ((sectionModule M ⊤).tildeInModuleCat.map (homOfLE h).op
        (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m)) =
    sectionRestrict M h (counitBasicOpen M f
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m))
  have hres := ConcreteCategory.congr_hom
    (ModuleCat.Tilde.toOpen_res (sectionModule M ⊤)
      (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) (homOfLE h)) m
  change (sectionModule M ⊤).tildeInModuleCat.map (homOfLE h).op
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen f) m) =
    ModuleCat.Tilde.toOpen (sectionModule M ⊤) (PrimeSpectrum.basicOpen g) m at hres
  rw [hres, counitBasicOpen_toOpen, counitBasicOpen_toOpen]
  change ((modulesSpecToSheaf R).obj M).val.map (homOfLE le_top).op m =
    ((modulesSpecToSheaf R).obj M).val.map (homOfLE h).op
      (((modulesSpecToSheaf R).obj M).val.map (homOfLE le_top).op m)
  rw [← ModuleCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The compatible counit maps on the original induced category of basic opens. -/
def counitBasis :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (sectionModule M ⊤).tildeInModuleCat ⟶
      (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        ((modulesSpecToSheaf R).obj M).val where
  app f := counitBasicOpen M f.unop
  naturality {f g} i := counitBasicOpen_naturality M f.unop g.unop i.unop.le

/-- The actual basis extension gives the counit as a morphism of R-module sheaves. -/
def counitModuleSheaf :
    (modulesSpecToSheaf R).obj (sectionModule M ⊤).tilde ⟶
      (modulesSpecToSheaf R).obj M :=
  ⟨TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens
    (counitBasis M)⟩

@[simp]
theorem counitModuleSheaf_basicOpen_app (f : R) :
    (counitModuleSheaf M).val.app (op (PrimeSpectrum.basicOpen f)) =
      counitBasicOpen M f :=
  TopCat.Sheaf.extend_hom_app _ _ PrimeSpectrum.isBasis_basic_opens (counitBasis M) f

/-- At the top open, the extended map sends a canonical section to its original section. -/
theorem toOpen_counitModuleSheaf_top :
    ModuleCat.Tilde.toOpen (sectionModule M ⊤) ⊤ ≫
      (counitModuleSheaf M).val.app (op ⊤) = 𝟙 (sectionModule M ⊤) := by
  have h : ModuleCat.Tilde.toOpen (sectionModule M ⊤)
        (PrimeSpectrum.basicOpen (1 : R)) ≫
      (counitModuleSheaf M).val.app (op (PrimeSpectrum.basicOpen (1 : R))) =
        sectionRestrict M le_top := by
    rw [counitModuleSheaf_basicOpen_app]
    exact ModuleCat.hom_ext (LinearMap.ext (counitBasicOpen_toOpen M (1 : R)))
  have htop : ModuleCat.Tilde.toOpen (sectionModule M ⊤) ⊤ ≫
      (counitModuleSheaf M).val.app (op ⊤) =
        sectionRestrict M (show (⊤ : (Spec (.of R)).Opens) ≤ ⊤ from le_rfl) :=
    Eq.mp (congrArg (fun U : (Spec (.of R)).Opens =>
      ModuleCat.Tilde.toOpen (sectionModule M ⊤) U ≫
        (counitModuleSheaf M).val.app (op U) =
          sectionRestrict M (show U ≤ ⊤ from le_top))
        (PrimeSpectrum.basicOpen_one (R := R))) h
  refine htop.trans ?_
  change ((modulesSpecToSheaf R).obj M).val.map (𝟙 (op ⊤)) = _
  exact ((modulesSpecToSheaf R).obj M).val.map_id (op ⊤)

/-- On every open, the original canonical section maps to its original restriction. -/
theorem toOpen_counitModuleSheaf_app (U : (Spec (.of R)).Opens) :
    ModuleCat.Tilde.toOpen (sectionModule M ⊤) U ≫
      (counitModuleSheaf M).val.app (op U) = sectionRestrict M le_top := by
  have hnat := (counitModuleSheaf M).val.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op
  change (sectionModule M ⊤).tildeInModuleCat.map
      (homOfLE (show U ≤ ⊤ from le_top)).op ≫
        (counitModuleSheaf M).val.app (op U) =
      (counitModuleSheaf M).val.app (op ⊤) ≫ sectionRestrict M le_top at hnat
  rw [← ModuleCat.Tilde.toOpen_res (sectionModule M ⊤) ⊤ U (homOfLE le_top),
    Category.assoc, hnat, ← Category.assoc,
    toOpen_counitModuleSheaf_top, Category.id_comp]

end KltDP.Geometry.AffineModuleTilde
