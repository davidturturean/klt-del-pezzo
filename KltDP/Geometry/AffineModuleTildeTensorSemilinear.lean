import KltDP.Geometry.AffineModuleTildeTensorSections
import KltDP.Geometry.AffineModuleTildeTransposeNormalization
import KltDP.Geometry.SchemeModulePullbackTensorSections
import KltDP.LinearAlgebra.TensorProductSemilinearMap

/-!
# Original affine tensor comparison under original semilinear restriction

The actual pullback tensor comparison and the original two semilinear
pullback maps agree with tilde of their original tensor map. Both sides
are evaluated by the original affine adjunction on native pure tensors.
This is the target compatibility required by the normal-twisted charts.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
universe u
namespace KltDP.Geometry.AffineModuleTildeTensorSemilinear

open AffineModuleTildeSemilinearMap SchemeModuleTensorSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
  {M N : ModuleCat.{u} A} {M' N' : ModuleCat.{u} B}
  (a : M →ₛₗ[φ] M') (b : N →ₛₗ[φ] N')

private theorem pullbackMap_unit_toOpen {P : ModuleCat.{u} A} {Q : ModuleCat.{u} B}
    (c : P →ₛₗ[φ] Q) (p : P) :
    (pullbackMap φ c).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom φ))).unit.app P.tilde).val.app (op ⊤)
            (ModuleCat.Tilde.toOpen P ⊤ p)) = ModuleCat.Tilde.toOpen Q ⊤ (c p) := by
  have h := pullbackMap_transpose_apply φ c p
  rw [pulledTilde_homEquiv_apply, Adjunction.homEquiv_unit] at h
  exact h

/-- The original sheaf pullback tensor comparison followed by the original component maps. -/
def componentMap :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj (M.tilde ⊗ N.tilde) ⟶
      M'.tilde ⊗ N'.tilde :=
  (schemeModulePullbackTensorIso (Spec.map (CommRingCat.ofHom φ)) M.tilde N.tilde).hom ≫
    (pullbackMap φ a ⊗ pullbackMap φ b)

private theorem componentMap_unit (m : M) (n : N) :
    (componentMap φ a b).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom φ))).unit.app (M.tilde ⊗ N.tilde)).val.app (op ⊤)
            (tensorSection M.tilde N.tilde ⊤
              (ModuleCat.Tilde.toOpen M ⊤ m) (ModuleCat.Tilde.toOpen N ⊤ n))) =
      tensorSection M'.tilde N'.tilde ⊤
        (ModuleCat.Tilde.toOpen M' ⊤ (a m)) (ModuleCat.Tilde.toOpen N' ⊤ (b n)) := by
  let j := Spec.map (CommRingCat.ofHom φ)
  have hT := SchemeModulePullbackTensorSections.tensor_unit_section j M.tilde N.tilde ⊤
    (ModuleCat.Tilde.toOpen M ⊤ m) (ModuleCat.Tilde.toOpen N ⊤ n)
  have hN := tensorSection_natural (pullbackMap φ a) (pullbackMap φ b) (j ⁻¹ᵁ ⊤)
    (((schemeModulePullbackPushforwardAdjunction j).unit.app M.tilde).val.app (op ⊤)
      (ModuleCat.Tilde.toOpen M ⊤ m))
    (((schemeModulePullbackPushforwardAdjunction j).unit.app N.tilde).val.app (op ⊤)
      (ModuleCat.Tilde.toOpen N ⊤ n))
  exact (congrArg ((pullbackMap φ a ⊗ pullbackMap φ b).val.app (op (j ⁻¹ᵁ ⊤))) hT).trans
    (hN.trans (congrArg₂ (tensorSection M'.tilde N'.tilde ⊤)
      (pullbackMap_unit_toOpen φ a m) (pullbackMap_unit_toOpen φ b n)))

private def component_transpose_tmul {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {M N : ModuleCat.{u} A} {M' N' : ModuleCat.{u} B}
    (a : M →ₛₗ[φ] M') (b : N →ₛₗ[φ] N') (m : M) (n : N) :=
  AffineModuleTildeTransposeNormalization.pullback_transpose_eq φ
    (AffineModuleTildeTensor.tensorModule M N) (M.tilde ⊗ N.tilde) (M'.tilde ⊗ N'.tilde)
    (AffineModuleTildeTensor.iso M N).hom (componentMap φ a b) (m ⊗ₜ[A] n) _ _
    (AffineModuleTildeTensor.iso_hom_toOpen_tmul M N ⊤ m n)
    (componentMap_unit φ a b m n)

/-- Normalize the original native tensor map before any sheaf adjunction is instantiated. -/
private theorem native_tensor_unit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {M N : ModuleCat.{u} A} {M' N' : ModuleCat.{u} B}
    (a : M →ₛₗ[φ] M') (b : N →ₛₗ[φ] N') (m : M) (n : N) :
    extendHom φ (M := AffineModuleTildeTensor.tensorModule M N)
        (N := AffineModuleTildeTensor.tensorModule M' N')
        (KltDP.LinearAlgebra.TensorProductSemilinearMap.map φ a b)
        ((1 : B) ⊗ₜ[A,φ] (m ⊗ₜ[A] n)) = a m ⊗ₜ[B] b n :=
  (extendHom_one_tmul φ (M := AffineModuleTildeTensor.tensorModule M N)
    (N := AffineModuleTildeTensor.tensorModule M' N')
    (KltDP.LinearAlgebra.TensorProductSemilinearMap.map φ a b) (m ⊗ₜ[A] n)).trans
    (KltDP.LinearAlgebra.TensorProductSemilinearMap.map_tmul φ a b m n)

private def native_transpose_tmul {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {M N : ModuleCat.{u} A} {M' N' : ModuleCat.{u} B}
    (a : M →ₛₗ[φ] M') (b : N →ₛₗ[φ] N') (m : M) (n : N) :=
  AffineModuleTildeTransposeNormalization.native_transpose_eq φ
    (AffineModuleTildeTensor.tensorModule M N) (AffineModuleTildeTensor.tensorModule M' N')
    (M'.tilde ⊗ N'.tilde)
    (extendHom φ (M := AffineModuleTildeTensor.tensorModule M N)
      (N := AffineModuleTildeTensor.tensorModule M' N')
      (KltDP.LinearAlgebra.TensorProductSemilinearMap.map φ a b))
    (AffineModuleTildeTensor.iso M' N').hom (m ⊗ₜ[A] n) (a m ⊗ₜ[B] b n)
    (tensorSection M'.tilde N'.tilde ⊤
      (ModuleCat.Tilde.toOpen M' ⊤ (a m)) (ModuleCat.Tilde.toOpen N' ⊤ (b n)))
    (native_tensor_unit φ a b m n)
    (AffineModuleTildeTensor.iso_hom_toOpen_tmul M' N' ⊤ (a m) (b n))

/-- The original tensor comparison commutes with both original semilinear restriction maps. -/
theorem iso_hom_pullback_square :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map
        (AffineModuleTildeTensor.iso M N).hom ≫ componentMap φ a b =
      pullbackMap φ (M := AffineModuleTildeTensor.tensorModule M N)
        (N := AffineModuleTildeTensor.tensorModule M' N')
        (KltDP.LinearAlgebra.TensorProductSemilinearMap.map φ a b) ≫
        (AffineModuleTildeTensor.iso M' N').hom := by
  apply ((AffineModuleTilde.pulledTildeAdjunction φ).homEquiv
    (AffineModuleTildeTensor.tensorModule M N) (M'.tilde ⊗ N'.tilde)).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m n
  exact (component_transpose_tmul φ a b m n).trans (native_transpose_tmul φ a b m n).symm

end KltDP.Geometry.AffineModuleTildeTensorSemilinear
