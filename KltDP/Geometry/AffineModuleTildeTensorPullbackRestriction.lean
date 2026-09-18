import KltDP.Geometry.AffineModuleTildeTensorPullback
import KltDP.Geometry.AffineModuleTildeTensorSemilinear
import KltDP.Geometry.SchemeModulePullbackTensorNaturality

/-!
# Restrict the actual tensor comparison after the original scalar extension

The original normal-twisted module uses the ring-module additive group on
its tensor. The identity rebundling preserves the original semilinear tensor
map. Naturality of the existing pullback tensor comparison then transports
the already proved native tensor square through the original affine pullback
isomorphisms. No commutation law for the original component maps is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
namespace KltDP.Geometry.AffineModuleTildeTensorPullbackRestriction

open AffineModuleTildeSemilinearMap

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem tensor_reframe {X Y : Scheme.{u}} (j : Y ⟶ X)
    {T P Q V : X.Modules} {P' Q' V' : Y.Modules}
    (e : Q ≅ P) (e' : Q' ≅ P') (t : T ⟶ P ⊗ V)
    (a : (schemeModulePullback j).obj P ⟶ P')
    (b : (schemeModulePullback j).obj V ⟶ V') :
    (schemeModulePullback j).map (t ≫ (e.inv ⊗ 𝟙 V)) ≫
        (schemeModulePullbackTensorIso j Q V).hom ≫
          (((schemeModulePullback j).map e.hom ≫ a ≫ e'.inv) ⊗ b) =
      (schemeModulePullback j).map t ≫
        (schemeModulePullbackTensorIso j P V).hom ≫
          (a ⊗ b) ≫ (e'.inv ⊗ 𝟙 V') := by
  rw [Functor.map_comp, Category.assoc,
    schemeModulePullbackTensorIso_natural_assoc j e.inv (𝟙 V)]
  simp only [Category.assoc, ← tensor_comp, Functor.map_id,
    Iso.map_inv_hom_id_assoc, Category.id_comp, Category.comp_id]
  simp only [(schemeModulePullback j).map_id V, Category.id_comp]

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  (φ : A →+* B) (φ' : A' →+* B') (ψ : B →+* B')
  (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
  (M' : ModuleCat.{u} A') (N' : ModuleCat.{u} B')

/-- The identity on the original tensor, retaining its original scalar action. -/
private def rebundle :
    AffineModuleTildeTensorPullback.tensorModule φ M N ≃ₗ[B]
      AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ).obj M) N :=
  LinearEquiv.refl B _

private def rebundleHom :
    AffineModuleTildeTensorPullback.tensorModule φ M N ⟶
      AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ).obj M) N :=
  (rebundle φ M N).toModuleIso.hom

private theorem iso_hom :
    (AffineModuleTildeTensorPullback.iso φ M N).hom =
      AffineModuleTilde.map (rebundleHom φ M N) ≫
        (AffineModuleTildeTensor.iso ((ModuleCat.extendScalars φ).obj M) N).hom ≫
          ((AffineModuleTilde.pullbackIso φ M).inv ⊗ 𝟙 N.tilde) := rfl

variable {M N M' N'}
  (a : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M')
  (b : N →ₛₗ[ψ] N')

/-- The same original tensor map, with the original ring-module tensor bundling. -/
def tensorRestriction :
    AffineModuleTildeTensorPullback.tensorModule φ M N →ₛₗ[ψ]
      AffineModuleTildeTensorPullback.tensorModule φ' M' N' :=
  KltDP.LinearAlgebra.TensorProductSemilinearMap.map ψ a b

/-- The original ambient module map through the actual affine pullback comparisons. -/
def ambientRestriction :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).obj
        ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde) ⟶
      (schemeModulePullback (Spec.map (CommRingCat.ofHom φ'))).obj M'.tilde :=
  (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map
      (AffineModuleTilde.pullbackIso φ M).hom ≫
    pullbackMap ψ a ≫ (AffineModuleTilde.pullbackIso φ' M').inv

/-- The actual pulled-back tensor followed by the two original restriction maps. -/
def componentRestriction :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).obj
        ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⊗ N.tilde) ⟶
      (schemeModulePullback (Spec.map (CommRingCat.ofHom φ'))).obj M'.tilde ⊗ N'.tilde :=
  (schemeModulePullbackTensorIso (Spec.map (CommRingCat.ofHom ψ))
    ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde) N.tilde).hom ≫
      (ambientRestriction φ φ' ψ a ⊗ pullbackMap ψ b)

/-- The original extended tensor comparison respects the original two semilinear maps. -/
theorem iso_hom_pullback_square :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map
        (AffineModuleTildeTensorPullback.iso φ M N).hom ≫
        componentRestriction φ φ' ψ a b =
      pullbackMap ψ (tensorRestriction φ φ' ψ a b) ≫
        (AffineModuleTildeTensorPullback.iso φ' M' N').hom := by
  let F := schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))
  let s : (AffineModuleTildeTensorPullback.tensorModule φ M N).tilde ⟶
      (AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ).obj M) N).tilde :=
    AffineModuleTilde.map (rebundleHom φ M N)
  let s' : (AffineModuleTildeTensorPullback.tensorModule φ' M' N').tilde ⟶
      (AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ').obj M') N').tilde :=
    AffineModuleTilde.map (rebundleHom φ' M' N')
  let t := (AffineModuleTildeTensor.iso ((ModuleCat.extendScalars φ).obj M) N).hom
  let t' := (AffineModuleTildeTensor.iso ((ModuleCat.extendScalars φ').obj M') N').hom
  let v := (AffineModuleTilde.pullbackIso φ M).inv ⊗ 𝟙 N.tilde
  let v' := (AffineModuleTilde.pullbackIso φ' M').inv ⊗ 𝟙 N'.tilde
  let c := AffineModuleTildeTensorSemilinear.componentMap ψ a b
  let d := pullbackMap ψ (M := AffineModuleTildeTensor.tensorModule
      ((ModuleCat.extendScalars φ).obj M) N)
    (N := AffineModuleTildeTensor.tensorModule ((ModuleCat.extendScalars φ').obj M') N')
    (KltDP.LinearAlgebra.TensorProductSemilinearMap.map ψ a b)
  have hR : F.map s ≫ d = pullbackMap ψ (tensorRestriction φ φ' ψ a b) ≫ s' :=
    pullbackMap_square ψ (rebundleHom φ M N) (rebundleHom φ' M' N')
      (tensorRestriction φ φ' ψ a b)
      (KltDP.LinearAlgebra.TensorProductSemilinearMap.map ψ a b) (fun _ => rfl)
  have hT : F.map t ≫ c = d ≫ t' :=
    AffineModuleTildeTensorSemilinear.iso_hom_pullback_square ψ a b
  have hF : F.map (t ≫ v) ≫ componentRestriction φ φ' ψ a b =
      F.map t ≫ c ≫ v' :=
    tensor_reframe (Spec.map (CommRingCat.ofHom ψ))
      (AffineModuleTilde.pullbackIso φ M) (AffineModuleTilde.pullbackIso φ' M')
      t (pullbackMap ψ a) (pullbackMap ψ b)
  rw [iso_hom, iso_hom]
  change F.map (s ≫ t ≫ v) ≫ componentRestriction φ φ' ψ a b =
    pullbackMap ψ (tensorRestriction φ φ' ψ a b) ≫ s' ≫ t' ≫ v'
  rw [F.map_comp, Category.assoc, hF]
  calc
    _ = F.map s ≫ d ≫ t' ≫ v' := by
      simpa only [Category.assoc] using congrArg (fun z => F.map s ≫ z ≫ v') hT
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ t' ≫ v') hR

end KltDP.Geometry.AffineModuleTildeTensorPullbackRestriction
