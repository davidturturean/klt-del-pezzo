/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

Adapted from Mathlib AlgebraicGeometry/Modules/Tilde.lean:418-484 at
79d0395a1825a6264ad5d269e35e60537518955e. The actual module coproduct
replaces the later concrete finsupp-cocone API. The original pinned
Presentation, tilde functor, structure sheaf and counit are retained.
-/
import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Geometry.AffineModuleTildeUnit
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Affine reconstruction from an actual global presentation

The original tilde functor takes a coproduct of copies of R to the
actual free sheaf. Its full faithfulness lifts the relations map of a
global sheaf presentation to a module map. Preservation of that map's
cokernel constructs a tilde presentation of the original sheaf, so the
actual adjunction counit is an isomorphism.

The hypothesis is the pinned global Presentation: generators and
generators of their actual kernel. No counit or localization statement
is assumed. Passing from local quasicoherent presentations to the
required affine restriction presentations remains a separate step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

universe u

namespace KltDP.Geometry.AffineModuleTilde

variable (R : Type u) [CommRing R]

/-- Tilde of the original module coproduct is the actual free sheaf. -/
def freeCoproductIso (I : Type u) :
    (∐ (fun (_ : I) => ModuleCat.of R R)).tilde ≅
      _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) I :=
  PreservesCoproduct.iso (functor R) (fun (_ : I) => ModuleCat.of R R) ≪≫
    Sigma.mapIso (fun _ => unitIso R)

/-- The original counit is invertible on every actual free sheaf. -/
theorem counit_isIso_of_free (I : Type u) :
    IsIso (counit (_root_.SheafOfModules.free
      (R := (Spec (.of R)).ringCatSheaf) I)) := by
  change IsIso ((adjunction R).counit.app _)
  exact (adjunction R).isIso_counit_app_of_iso (freeCoproductIso R I).symm

variable (M : (Spec (.of R)).Modules) (P : M.Presentation)

/-- The original generators are the cokernel of the original relations map. -/
def presentationIsColimit :
    IsColimit (CokernelCofork.ofπ P.generators.π (by simp) :
      CokernelCofork (P.relations.π ≫ kernel.ι P.generators.π)) := by
  letI : Epi P.generators.π := P.generators.epi
  letI : Epi P.relations.π := P.relations.epi
  exact isCokernelEpiComp
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι P.generators.π) (kernel.condition _))
      (kernelIsKernel P.generators.π)) P.relations.π rfl

include P in
/-- An actual global presentation makes the original affine counit an isomorphism. -/
theorem counit_isIso_of_presentation : IsIso (counit M) := by
  change IsIso ((adjunction R).counit.app M)
  apply ((adjunction R).isIso_counit_app_iff_mem_essImage).mpr
  let N₁ : ModuleCat.{u} R := ∐ (fun (_ : P.relations.I) => ModuleCat.of R R)
  let N₀ : ModuleCat.{u} R := ∐ (fun (_ : P.generators.I) => ModuleCat.of R R)
  let e₁ : (functor R).obj N₁ ≅ _ := freeCoproductIso R P.relations.I
  let e₀ : (functor R).obj N₀ ≅ _ := freeCoproductIso R P.generators.I
  let d : _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) P.relations.I ⟶
      _root_.SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf) P.generators.I :=
    P.relations.π ≫ kernel.ι P.generators.π
  let h : (functor R).obj N₁ ⟶ (functor R).obj N₀ := e₁.hom ≫ d ≫ e₀.inv
  let g : N₁ ⟶ N₀ := (functor R).preimage h
  have hg : (functor R).map g = h :=
    Functor.map_preimage (functor R) (X := N₁) (Y := N₀) h
  have hcomm : (functor R).map g ≫ e₀.hom = e₁.hom ≫ d := by
    calc
      (functor R).map g ≫ e₀.hom = h ≫ e₀.hom :=
        congrArg (fun f : (functor R).obj N₁ ⟶ (functor R).obj N₀ => f ≫ e₀.hom) hg
      _ = e₁.hom ≫ d := by
        change (e₁.hom ≫ d ≫ e₀.inv) ≫ e₀.hom = e₁.hom ≫ d
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let e : cokernel ((functor R).map g) ≅ cokernel d :=
    cokernel.mapIso _ _ e₁ e₀ hcomm
  exact ⟨cokernel g, ⟨PreservesCokernel.iso (functor R) g ≪≫ e ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (presentationIsColimit R M P)⟩⟩

/-- Package the actual counit without choosing a different comparison map. -/
def presentationCounitIso : (sectionModule M ⊤).tilde ≅ M := by
  letI := counit_isIso_of_presentation R M P
  exact asIso (counit M)

@[simp]
theorem presentationCounitIso_hom : (presentationCounitIso R M P).hom = counit M := rfl

end KltDP.Geometry.AffineModuleTilde
