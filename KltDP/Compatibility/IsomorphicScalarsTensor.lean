/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import KltDP.Compatibility.PresheafRestrictionTensor

/-!
# Tensor products under isomorphic changes of scalars

Bounded port of `ModuleCat.restrictScalarsTensorIso` and the two presheaf
tensor comparisons from AINTLIB, revision
`160e446617a2168c34c95bbe7a76c4105b392434`, file
`projects/ModularCurves/ModularCurves/ForMathlib/PullbackTensorMonoidal.lean`,
lines 118–215. The complete upstream file has SHA-256
`ed4f8dbecf1a053c2faaff60bb04666ff9a502dedeac1aa1263361669b3bb001`.
The original Apache-2.0 attribution is retained above.

The pinned `TensorProduct.equivOfCompatibleSMul` takes four explicit
arguments. Its two compatible actions are supplied by the actual ring
isomorphism and its inverse. The final comparison reuses the project's
proved `precompositionTensorIso`. No scheme pullback or sheafification
is needed for these sectionwise constructions.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace KltDP.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction along a bijective ring map preserves the tensor product.
Both directions send a pure tensor to the same pure tensor. -/
def restrictScalarsTensorIso (g : R →+* S) (hg : Function.Bijective g)
    (M N : _root_.ModuleCat.{u} S) :
    (_root_.ModuleCat.restrictScalars g).obj M ⊗
        (_root_.ModuleCat.restrictScalars g).obj N ≅
      (_root_.ModuleCat.restrictScalars g).obj (M ⊗ N) := by
  let e : R ≃+* S := RingEquiv.ofBijective g hg
  letI : Module R ↑M := Module.compHom ↑M g
  letI : Module R ↑N := Module.compHom ↑N g
  letI : Algebra R S := g.toAlgebra
  letI : Algebra S R := (e.symm : S →+* R).toAlgebra
  haveI : IsScalarTower R S ↑M := ⟨fun r s m => mul_smul (g r) s m⟩
  haveI : IsScalarTower R S ↑N := ⟨fun r s n => mul_smul (g r) s n⟩
  haveI : IsScalarTower S R ↑M := ⟨fun s r m => by
    show e (e.symm s * r) • m = s • e r • m
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  haveI : IsScalarTower S R ↑N := ⟨fun s r n => by
    show e (e.symm s * r) • n = s • e r • n
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  haveI : SMulCommClass S R ↑M := ⟨fun s r m => by
    show s • e r • m = e r • s • m
    rw [smul_comm]⟩
  exact (AddEquiv.toLinearEquiv
    (M := ↑((_root_.ModuleCat.restrictScalars g).obj M ⊗
      (_root_.ModuleCat.restrictScalars g).obj N))
    (M₂ := ↑((_root_.ModuleCat.restrictScalars g).obj (M ⊗ N)))
    (TensorProduct.equivOfCompatibleSMul S R ↑M ↑N).toAddEquiv
    (fun r x => (TensorProduct.equivOfCompatibleSMul S R ↑M ↑N).map_smul r x)).toModuleIso

@[simp]
theorem restrictScalarsTensorIso_hom_tmul (g : R →+* S) (hg : Function.Bijective g)
    (M N : _root_.ModuleCat.{u} S)
    (m : ↑((_root_.ModuleCat.restrictScalars g).obj M))
    (n : ↑((_root_.ModuleCat.restrictScalars g).obj N)) :
    (restrictScalarsTensorIso g hg M N).hom (m ⊗ₜ n) = m ⊗ₜ n := rfl

@[simp]
theorem restrictScalarsTensorIso_inv_tmul (g : R →+* S) (hg : Function.Bijective g)
    (M N : _root_.ModuleCat.{u} S) (m : ↑M) (n : ↑N) :
    (restrictScalarsTensorIso g hg M N).inv (m ⊗ₜ n) =
      (m ⊗ₜ n : ↑((_root_.ModuleCat.restrictScalars g).obj M ⊗
        (_root_.ModuleCat.restrictScalars g).obj N)) := rfl

end KltDP.ModuleCat

namespace KltDP.PresheafOfModules

section RestrictScalarsTensor

variable {C : Type u₁} [Category.{v₁} C] {T₁ T₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
  (ψ : T₁ ⋙ forget₂ CommRingCat RingCat ⟶ T₂ ⋙ forget₂ CommRingCat RingCat)
  [∀ X : Cᵒᵖ, IsIso (ψ.app X)]

/-- A componentwise isomorphic scalar map preserves the actual
sectionwise tensor product of presheaves of modules. -/
def restrictScalarsTensorObjIso
    (M N : _root_.PresheafOfModules.{u} (T₂ ⋙ forget₂ CommRingCat RingCat)) :
    (_root_.PresheafOfModules.restrictScalars ψ).obj M ⊗
        (_root_.PresheafOfModules.restrictScalars ψ).obj N ≅
      (_root_.PresheafOfModules.restrictScalars ψ).obj (M ⊗ N) :=
  _root_.PresheafOfModules.isoMk
    (fun X => KltDP.ModuleCat.restrictScalarsTensorIso (ψ.app X).hom
      (ConcreteCategory.bijective_of_isIso (ψ.app X)) (M.obj X) (N.obj X))
    (fun {X Y} f => _root_.ModuleCat.MonoidalCategory.tensor_ext (fun m n => by
      dsimp
      erw [_root_.PresheafOfModules.Monoidal.tensorObj_map_tmul]))

end RestrictScalarsTensor

section PushforwardTensor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶
    F.op ⋙ (R ⋙ forget₂ CommRingCat RingCat))
  [∀ X : Cᵒᵖ, IsIso (φ.app X)]

/-- Reindexing followed by an isomorphic change of scalars preserves
the actual tensor product of presheaves of modules. -/
def pushforwardTensorIso
    (P Q : _root_.PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (_root_.PresheafOfModules.pushforward.{u} φ).obj P ⊗
        (_root_.PresheafOfModules.pushforward.{u} φ).obj Q ≅
      (_root_.PresheafOfModules.pushforward.{u} φ).obj (P ⊗ Q) :=
  restrictScalarsTensorObjIso (T₁ := S) (T₂ := F.op ⋙ R) φ
      ((_root_.PresheafOfModules.pushforward₀OfCommRingCat F R).obj P)
      ((_root_.PresheafOfModules.pushforward₀OfCommRingCat F R).obj Q) ≪≫
    (_root_.PresheafOfModules.restrictScalars φ).mapIso
      (_root_.PresheafOfModules.precompositionTensorIso F R P Q).symm

end PushforwardTensor

end KltDP.PresheafOfModules
