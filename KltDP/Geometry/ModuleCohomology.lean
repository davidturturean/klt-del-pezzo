/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Vasily Ilin, Codex

Adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/SchemeModuleCohomologyHZero.lean:1–274.
The canonical cohomology action and H0 comparison are preserved.
Pinned Lean 4.19 uses AddCommGrp and the actual module-presheaf sections;
no independent cohomology, scalar action, or finiteness hypothesis is added.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import KltDP.Compatibility.AbelianSheafCohomology

/-!
# Global scalar actions and degree-zero cohomology of scheme modules

This file connects Mathlib's actual category of modules on a scheme to its
Ext-based sheaf cohomology.  The underlying abelian sheaf is supplied by the
existing functor `SheafOfModules.toSheaf`; no parallel sheaf or cohomology
notion is introduced.

For a module `M` on a scheme `X`, `zariskiFunctor X n` evaluates
`CategoryTheory.Sheaf.functorH` on the Zariski opens site.  In degree zero,
Mathlib's `CategoryTheory.Sheaf.H.equiv₀` identifies this group with the
genuine sections `sections M`.  We record its naturality for an actual module
morphism.  The comparison is proved for every actual scheme module, without
any affine acyclicity assumption.

Mathlib's cohomology functor uses the underlying abelian sheaf, so it does not
directly retain the action of `Γ(X, ⊤)`.  Multiplication by a global function
is nevertheless an actual endomorphism of every scheme module.  Applying the
cohomology functor to these endomorphisms gives a canonical global-functions
action in every degree, independent of a cover or resolution.  The actions are
named definitions rather than global instances, so clients opt into them
without changing scalar inference for arbitrary `Ext` groups.

Nothing here asserts coherence, finite-dimensionality, affine acyclicity, or
vanishing in positive degree.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Actual sections at the top open of a scheme module. -/
abbrev sections {X : Scheme.{u}} (M : X.Modules) :=
  M.val.obj (Opposite.op (⊤ : Opens X))

/-- Ext-based cohomology of the underlying abelian sheaf of a scheme module,
on the Zariski site of opens. -/
noncomputable def zariskiFunctor (X : Scheme.{u}) (n : ℕ) :
    CategoryTheory.Functor X.Modules AddCommGrp.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n

noncomputable instance (X : Scheme.{u}) (n : ℕ) :
    (zariskiFunctor X n).Additive := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n
  change (F ⋙ G).Additive
  constructor
  intro M N f g
  change G.map (F.map (f + g)) = G.map (F.map f) + G.map (F.map g)
  rw [F.map_add, G.map_add]

/-- The degree-`n` Zariski sheaf cohomology group of a module on a scheme. -/
abbrev H {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : Type u :=
  (zariskiFunctor X n).obj M

private def restrictGlobal {X : Scheme.{u}} (r : Γ(X, ⊤))
    (U : (Opens X)ᵒᵖ) : X.ringCatSheaf.val.obj U :=
  X.presheaf.map
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op r

private def globalSmulLinearMap {X : Scheme.{u}} (M : X.Modules)
    (U : (Opens X)ᵒᵖ) (r : Γ(X, ⊤)) : M.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom
    { toFun := fun x ↦ restrictGlobal r U • x
      map_add' := fun x y ↦ smul_add _ x y
      map_smul' := fun a x ↦ by
        letI : CommRing (X.ringCatSheaf.val.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        simpa only [RingHom.id_apply, smul_smul] using
          congrArg (fun b : X.ringCatSheaf.val.obj U ↦ b • x)
            (mul_comm (restrictGlobal r U) a) }

/-- Multiplication by a global function, as an actual endomorphism of a
scheme module.  On every open it is multiplication by the restriction of the
global function. -/
def globalSmulHom {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val :=
    { app := fun U ↦ globalSmulLinearMap M U r
      naturality := by
        intro U V i
        ext x
        change restrictGlobal r V • M.val.map i x =
          M.val.map i (restrictGlobal r U • x)
        rw [M.val.map_smul]
        congr 1
        unfold restrictGlobal
        change X.presheaf.map _ r =
          X.presheaf.map i (X.presheaf.map _ r)
        rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
        exact congrArg
          (fun j : Opposite.op (⊤ : Opens X) ⟶ V => X.presheaf.map j r)
          (Subsingleton.elim _ _) }

private theorem globalSmulHom_zero {X : Scheme.{u}} (M : X.Modules) :
    globalSmulHom M 0 = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal 0 U • x = 0
  rw [restrictGlobal, map_zero]
  exact (M.val.obj U).isModule.zero_smul x

private theorem globalSmulHom_one {X : Scheme.{u}} (M : X.Modules) :
    globalSmulHom M 1 = 𝟙 M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal 1 U • x = x
  rw [restrictGlobal, map_one]
  exact (M.val.obj U).isModule.one_smul x

private theorem globalSmulHom_add {X : Scheme.{u}} (M : X.Modules)
    (r s : Γ(X, ⊤)) :
    globalSmulHom M (r + s) = globalSmulHom M r + globalSmulHom M s := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal (r + s) U • x =
    restrictGlobal r U • x + restrictGlobal s U • x
  rw [restrictGlobal, map_add]
  exact (M.val.obj U).isModule.add_smul _ _ x

private theorem globalSmulHom_mul {X : Scheme.{u}} (M : X.Modules)
    (r s : Γ(X, ⊤)) :
    globalSmulHom M (r * s) = globalSmulHom M s ≫ globalSmulHom M r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal (r * s) U • x =
    restrictGlobal r U • (restrictGlobal s U • x)
  rw [restrictGlobal, map_mul]
  exact (M.val.obj U).isModule.mul_smul _ _ x

/-- The canonical action of global functions on genuine Ext-based sheaf
cohomology.  A scalar acts by applying cohomology to the corresponding
endomorphism of the coefficient module. -/
noncomputable def globalSectionsCohomologyAction {X : Scheme.{u}}
    (M : X.Modules) (n : ℕ) : Γ(X, ⊤) →+* End ((zariskiFunctor X n).obj M) where
  toFun r := (zariskiFunctor X n).map (globalSmulHom M r)
  map_zero' := by rw [globalSmulHom_zero, Functor.map_zero]
  map_one' := by
    rw [globalSmulHom_one]
    simpa only [CategoryTheory.End.one_def] using
      (zariskiFunctor X n).map_id M
  map_add' r s := by rw [globalSmulHom_add, Functor.map_add]
  map_mul' r s := by
    rw [globalSmulHom_mul]
    simpa only [CategoryTheory.End.mul_def] using
      (zariskiFunctor X n).map_comp
        (globalSmulHom M s) (globalSmulHom M r)

/-- The canonical `Γ(X, ⊤)`-module structure on genuine sheaf cohomology
in every degree.  Unlike the older Cech-transported action, this definition
does not depend on an affine cover. -/
noncomputable abbrev globalSectionsCohomologyModule {X : Scheme.{u}}
    (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (H M n) := by
  change Module Γ(X, ⊤)
    (ModuleCat.mkOfSMul' (globalSectionsCohomologyAction M n))
  infer_instance

/-- The canonical cohomology action evaluates to the cohomology map induced
by multiplication on the coefficient module. -/
theorem globalSectionsCohomologyModule_smul {X : Scheme.{u}}
    (M : X.Modules) (n : ℕ) (r : Γ(X, ⊤)) (x : H M n) :
    letI := globalSectionsCohomologyModule M n
    r • x = (zariskiFunctor X n).map (globalSmulHom M r) x := by
  rfl

/-- Multiplication by a global function commutes with every morphism of
scheme modules. -/
theorem globalSmulHom_naturality {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSmulHom M r ≫ f = f ≫ globalSmulHom N r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change f.val.app U (restrictGlobal r U • x) =
    restrictGlobal r U • f.val.app U x
  exact (f.val.app U).hom.map_smul (restrictGlobal r U) x

/-- Cohomology maps induced by actual morphisms of scheme modules are linear
for the canonical global-functions actions. -/
noncomputable def cohomologyLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (n : ℕ) (f : M ⟶ N) :
    letI := globalSectionsCohomologyModule M n
    letI := globalSectionsCohomologyModule N n
    H M n →ₗ[Γ(X, ⊤)] H N n := by
  letI := globalSectionsCohomologyModule M n
  letI := globalSectionsCohomologyModule N n
  refine
    { toFun := (zariskiFunctor X n).map f
      map_add' := ((zariskiFunctor X n).map f).hom.map_add
      map_smul' := ?_ }
  intro r x
  change (zariskiFunctor X n).map f
      ((zariskiFunctor X n).map (globalSmulHom M r) x) =
    (zariskiFunctor X n).map (globalSmulHom N r)
      ((zariskiFunctor X n).map f x)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    globalSmulHom_naturality, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- Degree-zero cohomology is the actual group of global sections at the top
open of the scheme. -/
noncomputable def hZeroEquivGlobalSections {X : Scheme.{u}}
    (M : X.Modules) : H M 0 ≃+ sections M :=
  CategoryTheory.Sheaf.H.equiv₀
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))

/-- The degree-zero/global-sections equivalence commutes with an actual
morphism of scheme modules. -/
theorem hZeroEquivGlobalSections_naturality {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (x : H M 0) :
    f.val.app (.op (⊤ : Opens X)) (hZeroEquivGlobalSections M x) =
      hZeroEquivGlobalSections N ((zariskiFunctor X 0).map f x) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) x

private theorem globalSmulHom_app_top {X : Scheme.{u}} (M : X.Modules)
    (r : Γ(X, ⊤)) (x : sections M) :
    (globalSmulHom M r).val.app (.op (⊤ : Opens X)) x = r • x := by
  have hr : restrictGlobal r (.op (⊤ : Opens X)) = r := by
    unfold restrictGlobal
    rw [show (homOfLE (show (⊤ : Opens X) ≤ ⊤ from le_rfl)).op = 𝟙 _ by
      apply Subsingleton.elim, X.presheaf.map_id]
    rfl
  change (globalSmulLinearMap M (.op (⊤ : Opens X)) r).hom x = r • x
  exact congrArg (fun s : Γ(X, ⊤) ↦ s • x) hr

/-- For the canonical cohomology action in degree zero, the comparison with
global sections is linear over the ring of global functions. -/
noncomputable def hZeroCanonicalLinearEquivGlobalSections
    {X : Scheme.{u}} (M : X.Modules) :
    letI := globalSectionsCohomologyModule M 0
    H M 0 ≃ₗ[Γ(X, ⊤)] sections M := by
  letI := globalSectionsCohomologyModule M 0
  refine
    { hZeroEquivGlobalSections M with
      map_smul' := ?_ }
  intro r x
  rw [globalSectionsCohomologyModule_smul]
  calc
    hZeroEquivGlobalSections M
        ((zariskiFunctor X 0).map (globalSmulHom M r) x) =
        (globalSmulHom M r).val.app (.op (⊤ : Opens X)) (hZeroEquivGlobalSections M x) :=
      (hZeroEquivGlobalSections_naturality (globalSmulHom M r) x).symm
    _ = r • hZeroEquivGlobalSections M x :=
      globalSmulHom_app_top M r (hZeroEquivGlobalSections M x)

/-- The actual linear map on global sections induced by a module morphism. -/
def globalSectionsLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) : sections M →ₗ[Γ(X, ⊤)] sections N :=
  (f.val.app (.op (⊤ : Opens X))).hom

/-- The canonical linear H0 comparison is natural for module morphisms. -/
theorem hZeroCanonicalLinearEquivGlobalSections_naturality
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (x : H M 0) :
    letI := globalSectionsCohomologyModule M 0
    letI := globalSectionsCohomologyModule N 0
    globalSectionsLinearMap f (hZeroCanonicalLinearEquivGlobalSections M x) =
      hZeroCanonicalLinearEquivGlobalSections N (cohomologyLinearMap 0 f x) := by
  letI := globalSectionsCohomologyModule M 0
  letI := globalSectionsCohomologyModule N 0
  exact hZeroEquivGlobalSections_naturality f x

end KltDP.Geometry.ModuleCohomology
