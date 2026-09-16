/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The functorial construction follows current Mathlib's Modules/Tilde.lean,
adapted to the original localized-module section objects at the project pin.
Exact source and scope are recorded in the associated reuse dossier.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Localization.Basic

/-!
# Functoriality of the pinned affine module sheaf

A module homomorphism acts on the original locally fractional sections by
its induced maps on the localized modules at each prime. The maps preserve
the original structure-sheaf scalar actions and commute with restriction.
In particular an actual linear isomorphism induces an actual module-sheaf
isomorphism on Spec R.

This file does not assert that every invertible sheaf is a tilde sheaf.
The affine global-generation and counit isomorphism remain separate results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable {R : Type u} [CommRing R] {M N P : ModuleCat.{u} R}

/-- The canonical map between the original localized modules at a prime. -/
def fiberMap (f : M ⟶ N) (x : PrimeSpectrum R) :
    LocalizedModule x.asIdeal.primeCompl M →ₗ[R]
      LocalizedModule x.asIdeal.primeCompl N :=
  IsLocalizedModule.map x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N) f.hom

@[simp]
theorem fiberMap_mk (f : M ⟶ N) (x : PrimeSpectrum R)
    (m : M) (s : x.asIdeal.primeCompl) :
    fiberMap f x (LocalizedModule.mk m s) = LocalizedModule.mk (f m) s :=
  IsLocalizedModule.map_LocalizedModules x.asIdeal.primeCompl f.hom m s

@[simp]
theorem fiberMap_mkLinearMap (f : M ⟶ N) (x : PrimeSpectrum R) (m : M) :
    fiberMap f x (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M m) =
      LocalizedModule.mkLinearMap x.asIdeal.primeCompl N (f m) :=
  IsLocalizedModule.map_apply x.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N) f.hom m

/-- The same induced map is linear over the actual local ring at the prime. -/
theorem fiberMap_local_smul (f : M ⟶ N) (x : PrimeSpectrum R)
    (a : Localization.AtPrime x.asIdeal)
    (m : LocalizedModule x.asIdeal.primeCompl M) :
    fiberMap f x (a • m) = a • fiberMap f x m :=
  (IsLocalization.linearMap_compatibleSMul x.asIdeal.primeCompl
    (Localization.AtPrime x.asIdeal)
    (LocalizedModule x.asIdeal.primeCompl M)
    (LocalizedModule x.asIdeal.primeCompl N)).map_smul (fiberMap f x) a m

/-- Applying a module homomorphism preserves the original local-fraction predicate. -/
theorem map_isLocallyFraction (f : M ⟶ N) (U : Opens (PrimeSpectrum R))
    (s : ModuleCat.Tilde.sectionsSubmodule M (op U)) :
    (ModuleCat.Tilde.isLocallyFraction N).pred
      (fun x : U => fiberMap f x.val (s.val x)) := by
  intro x
  obtain ⟨V, hxV, i, m, r, h⟩ := s.property x
  refine ⟨V, hxV, i, f m, r, ?_⟩
  intro y
  refine ⟨(h y).1, ?_⟩
  change r • fiberMap f y.val (s.val (i y)) =
    LocalizedModule.mkLinearMap y.val.asIdeal.primeCompl N (f m)
  rw [← (fiberMap f y.val).map_smul, (h y).2]
  exact fiberMap_mkLinearMap f y.val m

/-- The section map is linear over the original ring of sections on U. -/
def sectionMap (f : M ⟶ N) (U : Opens (PrimeSpectrum R)) :
    (M.tilde).val.obj (op U) →ₗ[Γ(Spec (.of R), U)] (N.tilde).val.obj (op U) where
  toFun s := ⟨fun x => fiberMap f x.val (s.val x), map_isLocallyFraction f U s⟩
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact (fiberMap f x.val).map_add (s.val x) (t.val x)
  map_smul' a s := by
    apply Subtype.ext
    funext x
    change fiberMap f x.val (a.val x • s.val x) =
      a.val x • fiberMap f x.val (s.val x)
    exact fiberMap_local_smul f x.val (a.val x) (s.val x)

@[simp]
theorem sectionMap_val (f : M ⟶ N) (U : Opens (PrimeSpectrum R))
    (s : M.tilde.val.obj (op U)) (x : U) :
    (sectionMap f U s).val x = fiberMap f x.val (s.val x) := rfl

/-- The actual sheaf morphism induced by the original module homomorphism. -/
def map (f : M ⟶ N) : M.tilde ⟶ N.tilde where
  val :=
    { app U := ModuleCat.ofHom (sectionMap f U.unop)
      naturality i := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        rfl }

@[simp]
theorem map_app_val (f : M ⟶ N) (U : Opens (PrimeSpectrum R))
    (s : M.tilde.val.obj (op U)) (x : U) :
    ((map f).val.app (op U) s).val x = fiberMap f x.val (s.val x) := rfl

/-- The canonical section of a module element maps to that of its image. -/
theorem map_app_toOpen (f : M ⟶ N) (U : Opens (PrimeSpectrum R)) (m : M) :
    (map f).val.app (op U) (ModuleCat.Tilde.toOpen M U m) =
      ModuleCat.Tilde.toOpen N U (f m) := by
  apply Subtype.ext
  funext x
  exact fiberMap_mkLinearMap f x.val m

/-- Actual fractional sections keep their denominator under a module map. -/
theorem map_app_const (f : M ⟶ N) (U : Opens (PrimeSpectrum R)) (m : M) (r : R)
    (hr : ∀ x ∈ U, r ∈ (x : PrimeSpectrum R).asIdeal.primeCompl) :
    (map f).val.app (op U) (ModuleCat.Tilde.const M m r U hr) =
      ModuleCat.Tilde.const N (f m) r U hr := by
  apply Subtype.ext
  funext x
  exact fiberMap_mk f x.val m ⟨r, hr x.val x.property⟩

@[simp]
theorem map_id (M : ModuleCat.{u} R) : map (𝟙 M) = 𝟙 M.tilde := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  change fiberMap (𝟙 M) x.val (s.val x) = s.val x
  exact DFunLike.congr_fun
    (IsLocalizedModule.map_id x.val.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M)) (s.val x)

@[simp]
theorem map_comp (f : M ⟶ N) (g : N ⟶ P) : map (f ≫ g) = map f ≫ map g := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  change fiberMap (f ≫ g) x.val (s.val x) =
    fiberMap g x.val (fiberMap f x.val (s.val x))
  exact DFunLike.congr_fun
    (IsLocalizedModule.map_comp' x.val.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl P) f.hom g.hom) (s.val x)

/-- The functor retains precisely the pinned `ModuleCat.tilde` objects. -/
def functor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ (Spec (.of R)).Modules where
  obj M := M.tilde
  map := map
  map_id := map_id
  map_comp := map_comp

/-- An actual module isomorphism induces an actual structure-sheaf-module isomorphism. -/
def mapIso (e : M ≅ N) : M.tilde ≅ N.tilde := (functor R).mapIso e

@[simp]
theorem mapIso_hom (e : M ≅ N) : (mapIso e).hom = map e.hom := rfl

/-- Linear-coordinate changes therefore retain the original tilde sheaves. -/
def linearEquivIso (e : M ≃ₗ[R] N) : M.tilde ≅ N.tilde :=
  mapIso e.toModuleIso

end KltDP.Geometry.AffineModuleTilde
