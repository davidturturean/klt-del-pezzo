import KltDP.LinearAlgebra.ChainMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# The three-leaf star rooted at a weighted leaf

The root of weight `b` meets the middle vertex of a length-three weight-two
chain. This is the remaining shape in manuscript `lem:rooted-trees` that is
not a star of paths centered at the root. The actual matrix uses coordinates
`Unit ⊕ Fin 3`, with root `Sum.inl ()` and chain middle `Sum.inr 1`.

A polynomial matrix multiplication certifies the entire Green matrix. The
determinant and root entry are respectively `4*(b-1)` and `1/(b-1)`; the latter
requires `b ≠ 1`. These statements do not classify rooted trees and contain
no assertions about geometric realization.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

private def leafRootedScalar (b : 𝕜) : Matrix Unit Unit 𝕜 := fun _ _ => b

/-- The root of weight `b` is attached to the middle of the three-vertex
chain, rather than to an endpoint. -/
def leafRootedStarMatrix (b : 𝕜) : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) 𝕜 :=
  Matrix.fromBlocks (leafRootedScalar b)
    (Matrix.replicateRow Unit (Pi.single (1 : Fin 3) (-1)))
    (Matrix.replicateCol Unit (Pi.single (1 : Fin 3) (-1))) (weightTwoChain 3)

/-- Polynomial numerator of the full inverse, in root/chain coordinate order.
This matrix is meaningful even when the original matrix is singular. -/
def leafRootedStarGreenNumerator (b : 𝕜) : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) 𝕜 :=
  Matrix.fromBlocks (fun (_ : Unit) (_ : Unit) => 4)
    (Matrix.replicateRow Unit ![2, 4, 2])
    (Matrix.replicateCol Unit ![2, 4, 2])
    !![3 * b - 2, 2 * b, b;
       2 * b, 4 * b, 2 * b;
       b, 2 * b, 3 * b - 2]

/-- The explicit Green matrix before its identification with the inverse. -/
def leafRootedStarGreen (b : 𝕜) : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) 𝕜 :=
  (4 * (b - 1))⁻¹ • leafRootedStarGreenNumerator b

/-- Exact polynomial certificate for the four-by-four matrix, checked entry
by entry in Lean. No hypothesis on `b` or matrix invertibility is used. -/
theorem leafRootedStar_mul_numerator (b : 𝕜) :
    leafRootedStarMatrix b * leafRootedStarGreenNumerator b =
      (4 * (b - 1)) • (1 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) 𝕜) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := h02.symm
  have h21 : (2 : Fin 3) ≠ 1 := h12.symm
  have h22 : (⟨2, by decide⟩ : Fin 3) = 2 := by decide
  have hvec2 (u v w : 𝕜) : (![u, v, w] : Fin 3 → 𝕜) 2 = w := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [leafRootedStarMatrix, leafRootedScalar, leafRootedStarGreenNumerator,
      Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
      Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply,
      weightTwoChain_apply, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl,
      h02, h12, h20, h21, h22, hvec2] <;> ring

variable [CharZero 𝕜]

/-- The numerator certificate yields a right inverse whenever `b ≠ 1`. -/
theorem leafRootedStar_mul_green (b : 𝕜) (hb : b ≠ 1) :
    leafRootedStarMatrix b * leafRootedStarGreen b = 1 := by
  have hden : 4 * (b - 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr hb)
  rw [leafRootedStarGreen, Matrix.mul_smul, leafRootedStar_mul_numerator,
    smul_smul, inv_mul_cancel₀ hden, one_smul]

/-- Full explicit Green inverse, including all off-diagonal entries. -/
theorem leafRootedStarMatrix_inverse (b : 𝕜) (hb : b ≠ 1) :
    (leafRootedStarMatrix b)⁻¹ = leafRootedStarGreen b :=
  Matrix.inv_eq_right_inv (leafRootedStar_mul_green b hb)

/-- The distinguished leaf's inverse diagonal entry. -/
theorem leafRootedStarMatrix_inverse_root (b : 𝕜) (hb : b ≠ 1) :
    (leafRootedStarMatrix b)⁻¹ (Sum.inl ()) (Sum.inl ()) = 1 / (b - 1) := by
  rw [leafRootedStarMatrix_inverse b hb]
  change (4 * (b - 1))⁻¹ * 4 = 1 / (b - 1)
  field_simp [sub_ne_zero.mpr hb]

/-- The inverse middle entry of the actual three-vertex chain is one. -/
theorem weightTwoChain_three_inverse_middle :
    (weightTwoChain (𝕜 := 𝕜) 3)⁻¹ (1 : Fin 3) 1 = 1 := by
  rw [weightTwoChain_inverse_apply]
  norm_num

/-- Eliminating the three-vertex chain subtracts exactly one from the root
weight. This equality uses the middle inverse entry, not an endpoint entry. -/
theorem leafRootedStar_schur (b : 𝕜) :
    leafRootedScalar b -
      Matrix.replicateRow Unit (Pi.single (1 : Fin 3) (-1 : 𝕜)) *
        (weightTwoChain (𝕜 := 𝕜) 3)⁻¹ *
        Matrix.replicateCol Unit (Pi.single (1 : Fin 3) (-1 : 𝕜)) =
      leafRootedScalar (b - 1) := by
  ext i j
  rw [Matrix.mul_assoc]
  change b - dotProduct (Pi.single (1 : Fin 3) (-1))
    ((weightTwoChain 3)⁻¹ *ᵥ Pi.single (1 : Fin 3) (-1)) = b - 1
  rw [single_dotProduct]
  change b - (-1) * dotProduct ((weightTwoChain 3)⁻¹ (1 : Fin 3))
    (Pi.single (1 : Fin 3) (-1)) = b - 1
  rw [dotProduct_single, weightTwoChain_three_inverse_middle]
  ring

/-- Determinant of the actual leaf-rooted star. This remains valid at the
singular parameter `b = 1`. -/
theorem det_leafRootedStarMatrix (b : 𝕜) :
    (leafRootedStarMatrix b).det = 4 * (b - 1) := by
  letI : Invertible (weightTwoChain (𝕜 := 𝕜) 3) := (isUnit_weightTwoChain 3).invertible
  rw [leafRootedStarMatrix, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    leafRootedStar_schur, Matrix.det_unique (n := Unit), det_weightTwoChain]
  norm_num [leafRootedScalar]

/-- The only singular parameter in characteristic zero is `b = 1`. -/
theorem isUnit_leafRootedStarMatrix_iff (b : 𝕜) :
    IsUnit (leafRootedStarMatrix b) ↔ b ≠ 1 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_leafRootedStarMatrix]
  simp [sub_eq_zero]

/-- Root coefficient for a source of strength `t` on the distinguished leaf.
The canonical source is obtained by setting `t = b - 2`. -/
theorem leafRootedStarMatrix_source_root (b t : 𝕜) (hb : b ≠ 1) :
    ((leafRootedStarMatrix b)⁻¹ *ᵥ Pi.single (Sum.inl ()) t) (Sum.inl ()) =
      t / (b - 1) := by
  change dotProduct ((leafRootedStarMatrix b)⁻¹ (Sum.inl ()))
    (Pi.single (Sum.inl ()) t) = _
  rw [dotProduct_single, leafRootedStarMatrix_inverse_root b hb]
  ring

/-- Quadratic correction for a source supported at the distinguished leaf. -/
theorem leafRootedStarMatrix_source_correction (b t : 𝕜) (hb : b ≠ 1) :
    dotProduct (Pi.single (Sum.inl ()) t)
      ((leafRootedStarMatrix b)⁻¹ *ᵥ Pi.single (Sum.inl ()) t) = t ^ 2 / (b - 1) := by
  rw [single_dotProduct, leafRootedStarMatrix_source_root b t hb]
  ring

end KltDP.LinearAlgebra
