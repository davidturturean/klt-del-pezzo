import KltDP.LinearAlgebra.SplitConormalDeterminant
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The exterior square of two actually framed lines

The tensor product of two framed modules is identified with the exterior
square of their direct product. The generator formula is the original
ordered wedge of the two inclusions. It proves that changing either frame
does not change this map. The determinant equivalence and wedge operations
are reused from the existing local conormal determinant construction.
-/

noncomputable section

open scoped TensorProduct
open KltDP.Geometry.AffineTopDifferentialFrame
open KltDP.LinearAlgebra.SplitConormalDeterminant

universe u v w

namespace KltDP.LinearAlgebra.FramedTensorExteriorSquare

variable {R : Type u} [CommRing R]
  {L : Type v} [AddCommGroup L] [Module R L]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- The original ordered product basis supplied by the two actual frames. -/
def productBasis (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) : Basis (Fin 2) R (L × M) :=
  (Basis.finTwoProd R).map (a.prodCongr b).symm

theorem productBasis_zero (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) :
    productBasis a b 0 = (a.symm 1, 0) := by
  rw [productBasis, Basis.map_apply, Basis.finTwoProd_zero]
  change (a.symm 1, b.symm 0) = _
  rw [map_zero]

theorem productBasis_one (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) :
    productBasis a b 1 = (0, b.symm 1) := by
  rw [productBasis, Basis.map_apply, Basis.finTwoProd_one]
  change (a.symm 0, b.symm 1) = _
  rw [map_zero]

private theorem first_inclusion (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) (x : L) :
    (x, (0 : M)) = a x • productBasis a b 0 := by
  rw [productBasis_zero]
  apply Prod.ext
  · change x = a x • a.symm 1
    rw [← a.symm.map_smul, smul_eq_mul, mul_one, a.symm_apply_apply]
  · exact (smul_zero (a x)).symm

private theorem second_inclusion (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) (y : M) :
    ((0 : L), y) = b y • productBasis a b 1 := by
  rw [productBasis_one]
  apply Prod.ext
  · exact (smul_zero (b y)).symm
  · change y = b y • b.symm 1
    rw [← b.symm.map_smul, smul_eq_mul, mul_one, b.symm_apply_apply]

private theorem wedge_basis (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) :
    leftWedge (productBasis a b 0) (productBasis a b 1) =
      exteriorPower.ιMulti R 2 (productBasis a b) := by
  rw [leftWedge_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The tensor-to-exterior equivalence obtained from the existing determinant frame. -/
def equiv (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) :
    L ⊗[R] M ≃ₗ[R] (⋀[R]^2 (L × M)) :=
  (TensorProduct.congr a b).trans
    ((TensorProduct.lid R R).trans (determinantEquiv (productBasis a b)).symm)

/-- The map sends each original pure tensor to the ordered wedge of the original inclusions. -/
theorem equiv_tmul (a : L ≃ₗ[R] R) (b : M ≃ₗ[R] R) (x : L) (y : M) :
    equiv a b (x ⊗ₜ[R] y) = exteriorPower.ιMulti R 2 ![(x, 0), (0, y)] := by
  calc
    equiv a b (x ⊗ₜ[R] y) =
        (a x * b y) • leftWedge (productBasis a b 0) (productBasis a b 1) := by
      rw [equiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, TensorProduct.lid_tmul,
        determinantEquiv_symm_apply, smul_eq_mul, wedge_basis]
    _ = leftWedge (a x • productBasis a b 0) (b y • productBasis a b 1) := by
      rw [leftWedge_smul_apply, map_smul, smul_smul]
    _ = leftWedge (x, 0) (0, y) := by
      rw [← first_inclusion, ← second_inclusion]
    _ = exteriorPower.ιMulti R 2 ![(x, 0), (0, y)] := leftWedge_apply _ _

/-- Both frames disappear from the actual tensor-to-wedge map. -/
theorem equiv_eq (a a' : L ≃ₗ[R] R) (b b' : M ≃ₗ[R] R) :
    equiv a b = equiv a' b' := by
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [equiv_tmul, equiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end KltDP.LinearAlgebra.FramedTensorExteriorSquare
