/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

The global-section commutation specializes the actual pushforward/forget
comparison in Mathlib AlgebraicGeometry/Modules/Tilde.lean:534-544 at
e3ea2ac394b7b87c549a259b7115f79c58e2d711. Its scalar proof is written
directly for the original pinned sheaf and section carriers. The pullback
comparison then uses existing adjunctions and their uniqueness theorem.
-/
import KltDP.Geometry.AffineModuleTildeAdjunction
import KltDP.Geometry.SchemeModuleFunctorial
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Actual affine tilde sheaves and scheme-module pullback

The global sections of the actual affine pushforward are the original
global sections with scalars restricted along the original ring map.
Their carrier is unchanged; equality of the two scalar actions follows
from the canonical Spec/global-section naturality theorem.

Composing the existing affine tilde and scheme pullback adjunctions, and
comparing with the existing tensor-extension/tilde adjunction, gives the
actual pullback comparison. Its transpose sends every original module
element to the canonical section of its original tensor 1 tensor m.
No quasicoherence, flatness, basis, or desired comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The original affine scheme map respects the canonical global sections. -/
theorem specMap_globalScalar (a : A) :
    (Spec.map (CommRingCat.ofHom φ)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ a) :=
  (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a).symm

/-- Both section carriers are literally the original N(top), and their
scalar actions agree by the actual Spec section-ring naturality. -/
def globalSectionsPushforwardEquiv (N : (Spec (CommRingCat.of B)).Modules) :
    (globalSectionsFunctor A).obj
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj N) ≃ₗ[A]
      (ModuleCat.restrictScalars φ).obj ((globalSectionsFunctor B).obj N) where
  toFun := fun s => s
  invFun := fun s => s
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' a s := by
    let smul : Γ(Spec (CommRingCat.of B), ⊤) → N.val.obj (op ⊤) →
        N.val.obj (op ⊤) :=
      @SMul.smul _ _ (N.val.obj (op ⊤)).isModule.toSMul
    change smul ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) s =
      smul ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (φ a)) s
    exact congrArg (fun r => smul r s) (specMap_globalScalar φ a)

theorem globalSectionsPushforwardEquiv_apply (N : (Spec (CommRingCat.of B)).Modules)
    (s : (globalSectionsFunctor A).obj
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj N)) :
    globalSectionsPushforwardEquiv φ N s = s := rfl

theorem globalSectionsPushforwardEquiv_symm_apply
    (N : (Spec (CommRingCat.of B)).Modules)
    (s : (ModuleCat.restrictScalars φ).obj ((globalSectionsFunctor B).obj N)) :
    (globalSectionsPushforwardEquiv φ N).symm s = s := rfl

/-- Actual affine pushforward and global sections commute with the original
restriction of scalars; the components retain the identity on sections. -/
def globalSectionsPushforwardIso :
    schemeModulePushforward (Spec.map (CommRingCat.ofHom φ)) ⋙ globalSectionsFunctor A ≅
      globalSectionsFunctor B ⋙ ModuleCat.restrictScalars φ :=
  NatIso.ofComponents (fun N => (globalSectionsPushforwardEquiv φ N).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun _ => rfl))

/-- The original tilde followed by actual scheme pullback is left adjoint
to the explicitly identified affine section functor. -/
def pulledTildeAdjunction :
    functor A ⋙ schemeModulePullback (Spec.map (CommRingCat.ofHom φ)) ⊣
      globalSectionsFunctor B ⋙ ModuleCat.restrictScalars φ :=
  (((adjunction A).comp
    (schemeModulePullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom φ)))).ofNatIsoRight
      (globalSectionsPushforwardIso φ))

/-- Original tensor extension followed by the original tilde has the same
right adjoint, using the pinned extension/restriction adjunction. -/
def extendedTildeAdjunction :
    ModuleCat.extendScalars φ ⋙ functor B ⊣
      globalSectionsFunctor B ⋙ ModuleCat.restrictScalars φ :=
  (ModuleCat.extendRestrictScalarsAdj φ).comp (adjunction B)

/-- The comparison is an isomorphism of the actual functors. -/
def pullbackTildeIso :
    functor A ⋙ schemeModulePullback (Spec.map (CommRingCat.ofHom φ)) ≅
      ModuleCat.extendScalars φ ⋙ functor B :=
  Adjunction.leftAdjointUniq (pulledTildeAdjunction φ) (extendedTildeAdjunction φ)

/-- Actual pullback of M tilde is the original tilde of tensor extension. -/
def pullbackIso (M : ModuleCat.{u} A) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ≅
      ((ModuleCat.extendScalars φ).obj M).tilde :=
  (pullbackTildeIso φ).app M

/-- The forward comparison has the original tensor-extension unit as its
transpose under the actual composed adjunction. -/
theorem pullbackTildeIso_hom_transpose (M : ModuleCat.{u} A) :
    (pulledTildeAdjunction φ).homEquiv _ _ ((pullbackTildeIso φ).hom.app M) =
      (extendedTildeAdjunction φ).unit.app M :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app
    (pulledTildeAdjunction φ) (extendedTildeAdjunction φ) M

/-- Every original module element maps to the canonical global section
of the actual tensor 1 tensor m; this fixes the comparison map. -/
theorem pullbackTildeIso_hom_transpose_apply (M : ModuleCat.{u} A) (m : M) :
    (pulledTildeAdjunction φ).homEquiv _ _ ((pullbackTildeIso φ).hom.app M) m =
      ModuleCat.Tilde.toOpen ((ModuleCat.extendScalars φ).obj M) ⊤ ((1 : B) ⊗ₜ[A,φ] m) := by
  have h := congrArg
    (fun f : M ⟶ (globalSectionsFunctor B ⋙ ModuleCat.restrictScalars φ).obj
        (((ModuleCat.extendScalars φ) ⋙ functor B).obj M) => f m)
    (pullbackTildeIso_hom_transpose φ M)
  exact h.trans rfl

end KltDP.Geometry.AffineModuleTilde
