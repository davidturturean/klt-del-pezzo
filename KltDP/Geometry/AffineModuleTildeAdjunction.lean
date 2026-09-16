/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The unit-counit construction is adapted from Mathlib
AlgebraicGeometry/Modules/Tilde.lean:334-380 at
79d0395a1825a6264ad5d269e35e60537518955e. It uses the project's existing
functor, global sections, canonical maps and counit on the original pinned
tilde sheaves; no modern replacement sheaf or elaboration option is used.
-/
import KltDP.Geometry.AffineModuleCounit
import KltDP.Geometry.AffineModuleTildeGlobalIso
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The adjunction for the original affine tilde sheaf

The canonical maps to global sections form the unit, and the existing
localization-defined counit forms the counit. Their triangle identities
follow from the original canonical sections and restrictions. Since the
unit is an isomorphism, the original tilde functor is fully faithful.

No quasicoherence or counit-isomorphism premise is used. The essential
image and the counit isomorphism for arbitrary quasicoherent sheaves are
separate results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable (R : Type u) [CommRing R]

/-- The original canonical global-section comparison is natural in the module. -/
def unitNatIso : 𝟭 (ModuleCat.{u} R) ≅ functor R ⋙ globalSectionsFunctor R :=
  NatIso.ofComponents (fun M => isoTop M) (fun {M N} f => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ModuleCat.Tilde.toOpen N ⊤ (f m) =
      (map f).val.app (op ⊤) (ModuleCat.Tilde.toOpen M ⊤ m)
    exact (map_app_toOpen f ⊤ m).symm)

/-- The natural unit retains the original canonical section of every element. -/
@[simp]
theorem unitNatIso_hom_app (M : ModuleCat.{u} R) :
    (unitNatIso R).hom.app M = ModuleCat.Tilde.toOpen M ⊤ := rfl

/-- The original tilde functor is left adjoint to actual global sections. -/
def adjunction : functor R ⊣ globalSectionsFunctor R where
  unit := (unitNatIso R).hom
  counit := counitNatTrans R
  left_triangle_components M := by
    apply tilde_hom_ext
    intro f m
    change (counit M.tilde).val.app (op (PrimeSpectrum.basicOpen f))
        ((map (ModuleCat.Tilde.toOpen M ⊤)).val.app (op (PrimeSpectrum.basicOpen f))
          (ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) m)) =
      ModuleCat.Tilde.toOpen M (PrimeSpectrum.basicOpen f) m
    rw [map_app_toOpen]
    have hc := counit_toOpen (R := R) M.tilde (PrimeSpectrum.basicOpen f)
      (ModuleCat.Tilde.toOpen M ⊤ m)
    exact hc.trans (ConcreteCategory.congr_hom
      (ModuleCat.Tilde.toOpen_res M ⊤ (PrimeSpectrum.basicOpen f)
        (homOfLE le_top)) m)
  right_triangle_components M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (counit M).val.app (op ⊤)
      (ModuleCat.Tilde.toOpen (sectionModule M ⊤) ⊤ m) = m
    rw [counit_toOpen]
    change ((modulesSpecToSheaf R).obj M).val.map
      (𝟙 (op (⊤ : (Spec (.of R)).Opens))) m = m
    exact ConcreteCategory.congr_hom
      (((modulesSpecToSheaf R).obj M).val.map_id (op ⊤)) m

/-- Full faithfulness follows from the proved adjunction and its actual unit isomorphism. -/
def fullyFaithfulFunctor : (functor R).FullyFaithful := by
  letI : IsIso (adjunction R).unit := by
    change IsIso (unitNatIso R).hom
    infer_instance
  exact (adjunction R).fullyFaithfulLOfIsIsoUnit

instance functor_full : (functor R).Full := (fullyFaithfulFunctor R).full

instance functor_faithful : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

instance functor_isLeftAdjoint : (functor R).IsLeftAdjoint :=
  (adjunction R).isLeftAdjoint

end KltDP.Geometry.AffineModuleTilde
