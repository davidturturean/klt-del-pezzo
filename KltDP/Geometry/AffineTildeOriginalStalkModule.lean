import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Module

/-!
# The original structure-stalk action on the original affine tilde stalk

The scalar action uses the original structure-stalk localization map and
the pinned tilde stalk isomorphism. The germ multiplication formula checks
that it is the action of the original sheaf sections. Scalar extension
across a localization preserves the underlying pinned stalk map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineTildeOriginalStalk

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (A : Type u) [CommRing A] (p : PrimeSpectrum A) (M : ModuleCat.{u} A)

/-- Name the original stalk before specializing its scalar actions. -/
abbrev originalStalkRing : CommRingCat.{u} :=
  (Spec (CommRingCat.of A)).presheaf.stalk p

local notation "Aₚ" => originalStalkRing A p

local instance originalAlgebra : Algebra A Aₚ :=
  (StructureSheaf.toStalk A p).hom.toAlgebra

local instance originalLocalization : IsLocalization.AtPrime Aₚ p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk A p

/-- The actual structure-stalk map acts on the original module localization. -/
abbrev fiberModule : Module Aₚ (LocalizedModule p.asIdeal.primeCompl M) :=
  Module.compHom _ (StructureSheaf.stalkToFiberRingHom A p).hom

theorem fiberTower :
    letI fm := fiberModule A p M
    letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
    IsScalarTower A Aₚ (LocalizedModule p.asIdeal.primeCompl M) := by
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  apply IsScalarTower.of_algebraMap_smul
  intro a m
  change (StructureSheaf.stalkToFiberRingHom A p (StructureSheaf.toStalk A p a)) • m = a • m
  rw [StructureSheaf.stalkToFiberRingHom_toStalk, algebraMap_smul]

/-- The pinned stalk identification transports this original scalar action. -/
abbrev stalkModule : Module Aₚ ((M.tildeInModuleCat).stalk p) := by
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  exact (ModuleCat.Tilde.stalkIso M p).toLinearEquiv.toAddEquiv.module Aₚ

theorem stalkTower :
    letI sm := stalkModule A p M
    letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
    IsScalarTower A Aₚ ((M.tildeInModuleCat).stalk p) := by
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  letI := fiberTower A p M
  letI sm := stalkModule A p M
  letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
  exact (ModuleCat.Tilde.stalkIso M p).toLinearEquiv.isScalarTower Aₚ

/-- The pinned tilde stalk map is linear over the original structure stalk. -/
def iso :
    letI fm := fiberModule A p M
    letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
    letI sm := stalkModule A p M
    letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
    ((M.tildeInModuleCat).stalk p) ≃ₗ[Aₚ]
      LocalizedModule p.asIdeal.primeCompl M := by
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  letI := fiberTower A p M
  letI sm := stalkModule A p M
  letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
  letI := stalkTower A p M
  exact (ModuleCat.Tilde.stalkIso M p).toLinearEquiv.extendScalarsOfIsLocalization
    p.asIdeal.primeCompl Aₚ

theorem iso_apply (x : (M.tildeInModuleCat).stalk p) :
    letI fm := fiberModule A p M
    letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
    letI sm := stalkModule A p M
    letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
    iso A p M x = ModuleCat.Tilde.stalkToFiberLinearMap M p x := by
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  letI sm := stalkModule A p M
  letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
  change (ModuleCat.Tilde.stalkIso M p).hom x = _
  rw [ModuleCat.Tilde.stalkIso_hom]

theorem iso_germ (U : Opens (PrimeSpectrum A)) (hp : p ∈ U)
    (s : M.tildeInModuleCat.obj (op U)) :
    letI fm := fiberModule A p M
    letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
    letI sm := stalkModule A p M
    letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
    iso A p M ((M.tildeInModuleCat).germ U p hp s) = s.val ⟨p, hp⟩ := by
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  letI sm := stalkModule A p M
  letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
  rw [iso_apply]
  exact ModuleCat.Tilde.stalkToFiberLinearMap_germ M U p hp s

/-- The original structure-sheaf action on the same tilde section carrier. -/
abbrev sectionModule (U : Opens (PrimeSpectrum A)) :
    Module Γ(Spec (CommRingCat.of A), U) (M.tildeInModuleCat.obj (op U)) :=
  inferInstanceAs (Module ((Spec.structureSheaf A).val.obj (op U))
    (ModuleCat.Tilde.sectionsSubmodule M (op U)))

/-- The constructed stalk action is the original sheaf action on germs. -/
theorem germ_smul (U : Opens (PrimeSpectrum A)) (hp : p ∈ U)
    (r : Γ(Spec (CommRingCat.of A), U)) (s : M.tildeInModuleCat.obj (op U)) :
    letI um := sectionModule A M U
    letI : SMul Γ(Spec (CommRingCat.of A), U) (M.tildeInModuleCat.obj (op U)) := um.toSMul
    letI sm := stalkModule A p M
    letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
    (M.tildeInModuleCat).germ U p hp (r • s) =
      ((Spec (CommRingCat.of A)).presheaf.germ U p hp r) •
        (M.tildeInModuleCat).germ U p hp s := by
  letI um := sectionModule A M U
  letI : SMul Γ(Spec (CommRingCat.of A), U) (M.tildeInModuleCat.obj (op U)) := um.toSMul
  letI fm := fiberModule A p M
  letI : SMul Aₚ (LocalizedModule p.asIdeal.primeCompl M) := fm.toSMul
  letI sm := stalkModule A p M
  letI : SMul Aₚ ((M.tildeInModuleCat).stalk p) := sm.toSMul
  apply (iso A p M).injective
  rw [(iso A p M).map_smul, iso_germ, iso_germ]
  change (r • s).val ⟨p, hp⟩ =
    (StructureSheaf.stalkToFiberRingHom A p
      ((Spec (CommRingCat.of A)).presheaf.germ U p hp r)) • s.val ⟨p, hp⟩
  have hg : StructureSheaf.stalkToFiberRingHom A p
      ((Spec (CommRingCat.of A)).presheaf.germ U p hp r) = r.val ⟨p, hp⟩ :=
    StructureSheaf.stalkToFiberRingHom_germ A U p hp r
  exact congrArg (fun a : Localization.AtPrime p.asIdeal => a • s.val ⟨p, hp⟩) hg.symm

end KltDP.Geometry.AffineTildeOriginalStalk
