import KltDP.Geometry.AffineModuleTildeTensorIso
import KltDP.Geometry.AffineModuleTildePullback

/-!
# Tilde tensor comparison after the original scalar extension

This adapter combines the proved affine tensor comparison with the actual
affine pullback comparison. The module rebundling and the tensor transport
are checked separately at abstract module objects, before substitution of
concrete differential or conormal modules.

The source retains the additive group obtained from its original ring-module
structure, as used by the normal-twisted affine adjunction chart. Its map to
the bundled tensor module is the identity linear equivalence. All subsequent
maps are the original tilde tensor and pullback comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AffineModuleTildeTensorPullback

variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

local instance sheafMonoidal : MonoidalCategory (Spec (CommRingCat.of B)).Modules :=
  Scheme.Modules.monoidalCategory (Spec (CommRingCat.of B))

/-- The original scalar-extension tensor module, with its ring-module additive group. -/
abbrev tensorModule : ModuleCat.{u} B :=
  letI : Algebra A B := φ.toAlgebra
  letI : AddCommGroup (_root_.TensorProduct B (_root_.TensorProduct A B M) N) :=
    Module.addCommMonoidToAddCommGroup B
  ModuleCat.of B (_root_.TensorProduct B (_root_.TensorProduct A B M) N)

private def rebundleEquiv :
    tensorModule φ M N ≃ₗ[B]
      AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ).obj M) N :=
  LinearEquiv.refl B _

private def rebundleIso :
    (tensorModule φ M N).tilde ≅
      (AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ).obj M) N).tilde :=
  AffineModuleTilde.linearEquivIso (rebundleEquiv φ M N)

private def tensorPullbackIso :
    ((ModuleCat.extendScalars φ).obj M).tilde ⊗ N.tilde ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⊗ N.tilde :=
  tensorIso (AffineModuleTilde.pullbackIso φ M).symm (Iso.refl _)

/-- Tilde of the original extended tensor is the tensor of the actual pullback and tilde. -/
def iso :
    (tensorModule φ M N).tilde ≅
      (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⊗ N.tilde :=
  rebundleIso φ M N ≪≫
    AffineModuleTildeTensor.iso ((ModuleCat.extendScalars φ).obj M) N ≪≫
    tensorPullbackIso φ M N

end KltDP.Geometry.AffineModuleTildeTensorPullback
