import KltDP.LinearAlgebra.RootedTreeMatrix
import KltDP.LinearAlgebra.LeafRootedStar
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

/-!
# The small rooted matrices in the manuscript's table

The seven shapes whose branches at the weighted root are paths are represented
by their actual arm lengths. The remaining, leaf-rooted three-leaf star has its
separate concrete matrix in `LeafRootedStar`.

The proofs specialize the chain-arm Schur calculation, including the singular
parameters in determinant identities. At `b ≥ 3`, the displayed denominators
are strictly positive, so the inverse formulas apply. This file does not assert
that these are all weighted trees under any graph-theoretic hypotheses.
-/

namespace KltDP.LinearAlgebra

open Matrix

/-- Seven specified rooted shapes with path arms. This is an explicit finite
family of matrices, not a classification of arbitrary weighted trees. -/
inductive RootedArmShape where
  | point
  | endEdge
  | endTwo
  | middleTwo
  | endThree
  | innerThree
  | centerStar
  deriving DecidableEq

/-- Zero-length arms add no vertices. Padding to three arms gives one uniform
index construction for all seven shapes. -/
def rootedArmLengths : RootedArmShape → Fin 3 → ℕ
  | .point => ![0, 0, 0]
  | .endEdge => ![1, 0, 0]
  | .endTwo => ![2, 0, 0]
  | .middleTwo => ![1, 1, 0]
  | .endThree => ![3, 0, 0]
  | .innerThree => ![1, 2, 0]
  | .centerStar => ![1, 1, 1]

/-- Numerators of the root Green entries in manuscript row order. -/
def rootedArmGreenNumerator : RootedArmShape → ℕ
  | .point => 1
  | .endEdge => 2
  | .endTwo => 3
  | .middleTwo => 1
  | .endThree => 4
  | .innerThree => 6
  | .centerStar => 2

/-- Factors multiplying the Green denominator to give the determinant. -/
def rootedArmDetMultiplier : RootedArmShape → ℕ
  | .point => 1
  | .endEdge => 1
  | .endTwo => 1
  | .middleTwo => 4
  | .endThree => 1
  | .innerThree => 1
  | .centerStar => 4

variable {𝕜 : Type*} [Field 𝕜]

/-- The seven displayed affine Green denominators. -/
def rootedArmDenominator : RootedArmShape → 𝕜 → 𝕜
  | .point, b => b
  | .endEdge, b => 2 * b - 1
  | .endTwo, b => 3 * b - 2
  | .middleTwo, b => b - 1
  | .endThree, b => 4 * b - 3
  | .innerThree, b => 6 * b - 7
  | .centerStar, b => 2 * b - 3

/-- Each member is an actual weighted adjacency matrix, with diagonal `b` at
the root, weight-two path arms, and minus-one incidences. -/
def rootedArmMatrix (shape : RootedArmShape) (b : 𝕜) :
    Matrix (Unit ⊕ ArmIndex (rootedArmLengths shape))
      (Unit ⊕ ArmIndex (rootedArmLengths shape)) 𝕜 :=
  rootedStarMatrix (rootedArmLengths shape) b

/-- The actual diagonal-minus-two vector is supported at the weighted root.
Thus the algebraic source `(b-2)e_root` is computed from each matrix, rather
than supplied as a separate assertion about its entries. -/
theorem rootedArmMatrix_diagonal_source (shape : RootedArmShape) (b : 𝕜) :
    (fun i => rootedArmMatrix shape b i i - 2) = Pi.single (Sum.inl ()) (b - 2) := by
  funext i
  rcases i with ⟨⟩ | ⟨a, j⟩
  · simp only [rootedArmMatrix, rootedStarMatrix, Matrix.fromBlocks_apply₁₁,
      Pi.single_eq_same]
  · simp only [rootedArmMatrix, rootedStarMatrix, Matrix.fromBlocks_apply₂₂,
      chainArms, Matrix.blockDiagonal'_apply_eq, weightTwoChain_apply,
      if_pos rfl, if_true, sub_self, Pi.single_eq_of_ne Sum.inr_ne_inl]

/-- The same diagonal computation for the eighth, leaf-rooted matrix. -/
theorem leafRootedStarMatrix_diagonal_source (b : 𝕜) :
    (fun i => leafRootedStarMatrix b i i - 2) = Pi.single (Sum.inl ()) (b - 2) := by
  funext i
  rcases i with ⟨⟩ | j
  · simp only [leafRootedStarMatrix, Matrix.fromBlocks_apply₁₁, Pi.single_eq_same]
    rfl
  · simp only [leafRootedStarMatrix, Matrix.fromBlocks_apply₂₂, weightTwoChain_apply,
      if_pos rfl, if_true, sub_self, Pi.single_eq_of_ne Sum.inr_ne_inl]

variable [CharZero 𝕜]

/-- Explicit Schur scalars for all seven specified arm-length lists. -/
theorem rootedArm_schur (shape : RootedArmShape) (b : 𝕜) :
    rootedStarSchur (rootedArmLengths shape) b =
      rootedArmDenominator shape b / (rootedArmGreenNumerator shape : 𝕜) := by
  cases shape <;>
    norm_num [rootedStarSchur, rootedArmLengths, rootedArmDenominator,
      rootedArmGreenNumerator, Fin.sum_univ_succ] <;> ring

/-- The numerical Green numerator is nonzero over a characteristic-zero
coefficient field. No restriction on the parameter `b` is involved. -/
theorem rootedArmGreenNumerator_ne_zero (shape : RootedArmShape) :
    (rootedArmGreenNumerator shape : 𝕜) ≠ 0 := by
  cases shape <;> norm_num [rootedArmGreenNumerator]

/-- The determinant table, valid also at singular values of `b`. -/
theorem det_rootedArmMatrix (shape : RootedArmShape) (b : 𝕜) :
    (rootedArmMatrix shape b).det =
      (rootedArmDetMultiplier shape : 𝕜) * rootedArmDenominator shape b := by
  rw [rootedArmMatrix, det_rootedStarMatrix, rootedArm_schur]
  cases shape <;>
    norm_num [rootedArmLengths, rootedArmDetMultiplier, rootedArmDenominator,
      rootedArmGreenNumerator, Fin.prod_univ_succ] <;> ring

/-- Nonvanishing of the displayed denominator is precisely invertibility for
each specified actual matrix. -/
theorem isUnit_rootedArmMatrix_iff (shape : RootedArmShape) (b : 𝕜) :
    IsUnit (rootedArmMatrix shape b) ↔ rootedArmDenominator shape b ≠ 0 := by
  rw [rootedArmMatrix, isUnit_rootedStarMatrix_iff, rootedArm_schur, div_ne_zero_iff]
  have hnum : (rootedArmGreenNumerator shape : 𝕜) ≠ 0 :=
    rootedArmGreenNumerator_ne_zero shape
  exact ⟨fun h => h.1, fun h => ⟨h, hnum⟩⟩

/-- The seven root inverse entries, with the necessary nonvanishing hypothesis
explicit. The right side reduces to the corresponding manuscript table row. -/
theorem rootedArmMatrix_inverse_root (shape : RootedArmShape) (b : 𝕜)
    (hb : rootedArmDenominator shape b ≠ 0) :
    (rootedArmMatrix shape b)⁻¹ (Sum.inl ()) (Sum.inl ()) =
      (rootedArmGreenNumerator shape : 𝕜) / rootedArmDenominator shape b := by
  have hs : rootedStarSchur (rootedArmLengths shape) b ≠ 0 := by
    rw [rootedArm_schur]
    exact div_ne_zero hb (rootedArmGreenNumerator_ne_zero shape)
  change (rootedStarMatrix (rootedArmLengths shape) b)⁻¹
    (Sum.inl ()) (Sum.inl ()) = _
  rw [rootedStarMatrix_inverse_center _ _ hs, rootedArm_schur, inv_div]

/-- Coefficient at the root for an arbitrary source supported there. -/
theorem rootedArmMatrix_source_root (shape : RootedArmShape) (b t : 𝕜)
    (hb : rootedArmDenominator shape b ≠ 0) :
    ((rootedArmMatrix shape b)⁻¹ *ᵥ Pi.single (Sum.inl ()) t) (Sum.inl ()) =
      t * (rootedArmGreenNumerator shape : 𝕜) / rootedArmDenominator shape b := by
  change dotProduct ((rootedArmMatrix shape b)⁻¹ (Sum.inl ()))
    (Pi.single (Sum.inl ()) t) = _
  rw [dotProduct_single, rootedArmMatrix_inverse_root shape b hb]
  ring

/-- Quadratic correction of a root-supported source. In the manuscript,
`t = b - 2` is the canonical-degree source. -/
theorem rootedArmMatrix_source_correction (shape : RootedArmShape) (b t : 𝕜)
    (hb : rootedArmDenominator shape b ≠ 0) :
    dotProduct (Pi.single (Sum.inl ()) t)
      ((rootedArmMatrix shape b)⁻¹ *ᵥ Pi.single (Sum.inl ()) t) =
        t ^ 2 * (rootedArmGreenNumerator shape : 𝕜) / rootedArmDenominator shape b := by
  rw [single_dotProduct, rootedArmMatrix_source_root shape b t hb]
  ring

section Ordered

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The manuscript's weight bound makes each of its seven displayed affine
denominators strictly positive. -/
theorem rootedArmDenominator_pos (shape : RootedArmShape) {b : 𝕜} (hb : 3 ≤ b) :
    0 < rootedArmDenominator shape b := by
  cases shape <;> dsimp [rootedArmDenominator] <;> linarith

/-- Positivity of the scalar Schur complement at the source's weight bound. -/
theorem rootedArm_schur_pos (shape : RootedArmShape) {b : 𝕜} (hb : 3 ≤ b) :
    0 < rootedStarSchur (rootedArmLengths shape) b := by
  rw [rootedArm_schur]
  apply div_pos (rootedArmDenominator_pos shape hb)
  cases shape <;> norm_num [rootedArmGreenNumerator]

/-- The root inverse table at the exact weight assumption `b ≥ 3`. -/
theorem rootedArmMatrix_inverse_root_of_three_le (shape : RootedArmShape)
    {b : 𝕜} (hb : 3 ≤ b) :
    (rootedArmMatrix shape b)⁻¹ (Sum.inl ()) (Sum.inl ()) =
      (rootedArmGreenNumerator shape : 𝕜) / rootedArmDenominator shape b :=
  rootedArmMatrix_inverse_root shape b (ne_of_gt (rootedArmDenominator_pos shape hb))

/-- The eighth source row uses the separately defined matrix whose weighted
leaf meets the middle of a three-vertex chain. -/
theorem leafRootedStarMatrix_inverse_root_of_three_le {b : 𝕜} (hb : 3 ≤ b) :
    (leafRootedStarMatrix b)⁻¹ (Sum.inl ()) (Sum.inl ()) = 1 / (b - 1) := by
  apply leafRootedStarMatrix_inverse_root b
  linarith

end Ordered

end KltDP.LinearAlgebra
