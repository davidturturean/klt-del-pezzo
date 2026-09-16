/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The construction follows official Mathlib
79d0395a1825a6264ad5d269e35e60537518955e,
AlgebraicGeometry/Modules/Tilde.lean:435-469. The pinned categorical
coproduct replaces the newer explicit finsupp cocone. Generators are
all original module elements, and relations are all elements of the
actual kernel of their original projection.
-/
import KltDP.Geometry.AffineModulePresentationCounit
import KltDP.Compatibility.SheafPresentationQuasicoherent
import Mathlib.LinearAlgebra.Span.Basic

/-!
# An actual free presentation of every original affine tilde sheaf

The module projection sends the basis copy indexed by m to m. Its
surjectivity is witnessed by that same basis copy at 1. Applying the
construction to its actual kernel supplies all relations. The abelian
cokernel theorem and preservation by the original tilde functor give
an actual sheaf presentation, hence the original quasicoherent predicate.
No module finiteness, Noetherianity or chosen-presentation premise is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]

/-- The actual coproduct of copies of R indexed by the original module elements. -/
def freeModuleProjection (M : ModuleCat.{u} R) :
    (∐ (fun _ : M => ModuleCat.of R R)) ⟶ M :=
  Sigma.desc (fun m => ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))

/-- The original basis copy at 1 maps to its indexing element. -/
theorem freeModuleProjection_ι_one (M : ModuleCat.{u} R) (m : M) :
    freeModuleProjection M ((Sigma.ι (fun _ : M => ModuleCat.of R R) m) 1) = m := by
  have h := ConcreteCategory.congr_hom
    (Sigma.ι_desc (fun m : M => ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)) m) 1
  exact h.trans (LinearMap.toSpanSingleton_one R M m)

instance freeModuleProjection_epi (M : ModuleCat.{u} R) : Epi (freeModuleProjection M) :=
  (ModuleCat.epi_iff_surjective _).mpr (fun m =>
    ⟨(Sigma.ι (fun _ : M => ModuleCat.of R R) m) 1, freeModuleProjection_ι_one M m⟩)

/-- All elements of the actual projection kernel give the original relation map. -/
def freeModuleRelation (M : ModuleCat.{u} R) :
    (∐ (fun _ : (kernel (freeModuleProjection M) : ModuleCat.{u} R) => ModuleCat.of R R)) ⟶
      (∐ (fun _ : M => ModuleCat.of R R)) :=
  freeModuleProjection (kernel (freeModuleProjection M)) ≫ kernel.ι (freeModuleProjection M)

theorem freeModuleRelation_comp_projection (M : ModuleCat.{u} R) :
    freeModuleRelation M ≫ freeModuleProjection M = 0 := by
  simp only [freeModuleRelation, Category.assoc, kernel.condition, comp_zero]

/-- The original projection is the cokernel of these actual relations. -/
def freeModulePresentationIsColimit (M : ModuleCat.{u} R) :
    IsColimit (CokernelCofork.ofπ (freeModuleProjection M)
      (freeModuleRelation_comp_projection M)) :=
  isCokernelEpiComp
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι (freeModuleProjection M)) (kernel.condition _))
      (kernelIsKernel (freeModuleProjection M)))
    (freeModuleProjection (kernel (freeModuleProjection M)))
    (hg := freeModuleProjection_epi (R := R)
      (kernel (freeModuleProjection M) : ModuleCat.{u} R)) rfl

/-- The original tilde of an arbitrary module has an actual global free presentation. -/
def tildePresentation (M : ModuleCat.{u} R) : M.tilde.Presentation := by
  let F := functor R
  let q := freeModuleProjection M
  let r := freeModuleRelation M
  let e₀ := freeCoproductIso R M
  let e₁ := freeCoproductIso R (kernel q : ModuleCat.{u} R)
  let d := e₁.inv ≫ F.map r ≫ e₀.hom
  let p := e₀.inv ≫ F.map q
  have H : d ≫ p = 0 := by
    dsimp only [d, p]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      r, q, freeModuleRelation_comp_projection, Functor.map_zero, comp_zero]
  apply _root_.SheafOfModules.presentationOfIsCokernelFree d p H
  refine IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext e₁ e₀ (by simp [d, r]) (by simp)) _ _ ?_
    (isColimitOfPreserves F (freeModulePresentationIsColimit M))
  exact Cocones.ext (Iso.refl _) (by
    rintro (_ | _)
    <;> simp [d, p, r, q, ← Functor.map_comp])

/-- Every original affine tilde sheaf is quasicoherent in the pinned literal sense. -/
theorem tilde_isQuasicoherent (M : ModuleCat.{u} R) : M.tilde.IsQuasicoherent :=
  (tildePresentation M).isQuasicoherent

end KltDP.Geometry.AffineModuleTilde
