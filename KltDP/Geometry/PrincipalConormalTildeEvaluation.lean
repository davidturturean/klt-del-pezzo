import KltDP.Geometry.PrincipalConormalTildeDual
import KltDP.Geometry.AffineModuleTildeTensorPairing

/-!
# Principal coordinates of the original conormal evaluation

The previously produced tilde evaluation is exactly the product of the
original principal conormal and normal coordinates in the actual structure
module. This is a specialization of the actual tilde tensor normalization;
no pairing or comparison is assumed. Global conormal gluing is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace KltDP.Geometry.PrincipalConormalTildeEvaluation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {A : Type u} [CommRing A] (J : Ideal A) (d : J)
  (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)

/-- The original principal coordinate on the actual conormal module. -/
def conormalCoframe : PrincipalConormalTildeDual.conormalModule J ≅
    ModuleCat.of (A ⧸ J) (A ⧸ J) :=
  (KltDP.RingTheory.principalConormalEquiv J d hJ hd).symm.toModuleIso

/-- The original principal coordinate on the actual module dual. -/
def normalCoframe : PrincipalConormalTildeDual.normalModule J ≅
    ModuleCat.of (A ⧸ J) (A ⧸ J) :=
  (KltDP.RingTheory.principalNormalEquiv J d hJ hd).toModuleIso

/-- The actual conormal tilde coordinate with its original unit comparison. -/
def conormalCoordinate : (PrincipalConormalTildeDual.conormalModule J).tilde ⟶
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf :=
  AffineModuleTildeTensorPairing.coordinate (conormalCoframe J d hJ hd).hom

/-- The actual normal tilde coordinate with its original unit comparison. -/
def normalCoordinate : (PrincipalConormalTildeDual.normalModule J).tilde ⟶
    _root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf :=
  AffineModuleTildeTensorPairing.coordinate (normalCoframe J d hJ hd).hom

private theorem moduleEvaluation_hom :
    ModuleCat.ofHom (PrincipalConormalTildeDual.moduleEvaluationEquiv J d hJ hd).toLinearMap =
      AffineModuleTildeTensorPairing.moduleProduct
        (conormalCoframe J d hJ hd).hom (normalCoframe J d hJ hd).hom := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m ℓ
  change PrincipalConormalTildeDual.moduleEvaluationEquiv J d hJ hd (m ⊗ₜ[A ⧸ J] ℓ) =
    AffineModuleTildeTensorPairing.moduleProduct
      (conormalCoframe J d hJ hd).hom (normalCoframe J d hJ hd).hom (m ⊗ₜ[A ⧸ J] ℓ)
  rw [AffineModuleTildeTensorPairing.moduleProduct_tmul]
  simp only [PrincipalConormalTildeDual.moduleEvaluationEquiv,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul, smul_eq_mul] <;> rfl

/-- The original produced evaluation is exactly multiplication of its two
actual coordinates as a morphism of the original module sheaves. -/
theorem transportedEvaluation_product :
    (PrincipalConormalTildeDual.transportedEvaluationIso J d hJ hd).hom =
      (conormalCoordinate J d hJ hd ⊗ normalCoordinate J d hJ hd) ≫
        (schemeStructureTensorRightIso
          (_root_.SheafOfModules.unit (Spec (CommRingCat.of (A ⧸ J))).ringCatSheaf)).hom := by
  rw [PrincipalConormalTildeDual.transportedEvaluationIso_hom]
  change (AffineModuleTildeTensor.iso
      (PrincipalConormalTildeDual.conormalModule J)
      (PrincipalConormalTildeDual.normalModule J)).inv ≫
    AffineModuleTilde.map
      (ModuleCat.ofHom (PrincipalConormalTildeDual.moduleEvaluationEquiv J d hJ hd).toLinearMap) ≫
    (AffineModuleTilde.unitIso (A ⧸ J)).hom = _
  rw [moduleEvaluation_hom]
  exact AffineModuleTildeTensorPairing.iso_inv_product
    (conormalCoframe J d hJ hd).hom (normalCoframe J d hJ hd).hom

end KltDP.Geometry.PrincipalConormalTildeEvaluation
