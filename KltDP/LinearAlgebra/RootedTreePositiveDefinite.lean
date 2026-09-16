import KltDP.LinearAlgebra.RootedTreeTransport
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Positive definiteness of the eight small rooted matrices

The actual matrices of `lem:rooted-trees` are positive definite for every
rational root weight at least two. Thus both the higher-weight rows and their
all-weight-two specializations have actual occurrence witnesses.

Reuse review: the pinned Mathlib `Matrix.schur_complement_eq₂₂` supplies the
quadratic completion, and `Matrix.IsHermitian.fromBlocks₂₂` supplies symmetry.
Its `Matrix.PosSemidef.fromBlocks₂₂` gives only nonstrict positivity; the strict
adapter below retains the nonzero-vector condition. Small weight-two chains
are checked by completed squares, then assembled by genuine block diagonals.
The newer Mathlib snapshot 5aedf732 uses finitely supported positivity and is
not a compatible replacement for the pinned finite-matrix definition. Both
Mathlib versions are Apache-2.0; no source or toolchain port is used here.
-/

namespace KltDP.LinearAlgebra

open Matrix

/-- Strict Schur-complement positivity over the rational numbers. The lower
block and its actual Schur complement are the only positivity hypotheses. -/
theorem posDef_fromBlocks_of_schur {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m m ℚ) (B : Matrix m n ℚ)
    {D : Matrix n n ℚ} [Invertible D] (hD : D.PosDef)
    (hS : (A - B * D⁻¹ * Bᴴ).PosDef) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef := by
  refine ⟨(Matrix.IsHermitian.fromBlocks₂₂ A B hD.1).2 hS.1, ?_⟩
  intro x hx
  rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x,
    Matrix.schur_complement_eq₂₂ A B _ _ hD.1]
  by_cases hleft : x ∘ Sum.inl = 0
  · have hright : x ∘ Sum.inr ≠ 0 := by
      intro hzero
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hleft i
      | inr i => exact congrFun hzero i
    simp only [hleft, Matrix.mulVec_zero, zero_add, star_zero,
      Matrix.zero_vecMul, zero_dotProduct, add_zero]
    rw [← dotProduct_mulVec]
    exact hD.2 _ hright
  · apply add_pos_of_nonneg_of_pos
    · rw [← dotProduct_mulVec]
      exact hD.posSemidef.2 _
    · rw [← dotProduct_mulVec]
      exact hS.2 _ hleft

/-- Each chain needed by the rooted table is positive definite. Length zero
is included: there is no nonzero vector on its empty coordinate type. -/
theorem weightTwoChain_posDef_of_le_three (n : ℕ) (hn : n ≤ 3) :
    (weightTwoChain (𝕜 := ℚ) n).PosDef := by
  have hsym : (weightTwoChain (𝕜 := ℚ) n).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, weightTwoChain_apply]
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij, or_comm]
  refine ⟨hsym, ?_⟩
  intro x hx
  interval_cases n
  · exact False.elim (hx (Subsingleton.elim _ _))
  · have hx0 : x 0 ≠ 0 := by
      intro h
      apply hx
      funext i
      fin_cases i
      exact h
    have hs := sq_pos_of_ne_zero hx0
    norm_num [Matrix.mulVec, dotProduct, weightTwoChain_apply,
      Fin.sum_univ_succ, star_trivial] at *
    nlinarith
  · by_contra hnonpos
    simp only [not_lt] at hnonpos
    norm_num [Matrix.mulVec, dotProduct, weightTwoChain_apply,
      Fin.sum_univ_succ, star_trivial] at hnonpos
    have h0 : (x 0 - x 1 / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1)]
    have h1 : x 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1 / 2), sq_nonneg (x 1)]
    have hz0 := sq_eq_zero_iff.mp h0
    have hz1 := sq_eq_zero_iff.mp h1
    apply hx
    funext i
    fin_cases i <;> norm_num at * <;> linarith
  · by_contra hnonpos
    simp only [not_lt] at hnonpos
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := Ne.symm h12
    norm_num [Matrix.mulVec, dotProduct, weightTwoChain_apply,
      Fin.sum_univ_succ, star_trivial, h02, h12, h21] at hnonpos
    have h0 : (x 0 - x 1 / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1 / 2),
        sq_nonneg (x 1 - 2 * x 2 / 3), sq_nonneg (x 2)]
    have h1 : (x 1 - 2 * x 2 / 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1 / 2),
        sq_nonneg (x 1 - 2 * x 2 / 3), sq_nonneg (x 2)]
    have h2 : x 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - x 1 / 2),
        sq_nonneg (x 1 - 2 * x 2 / 3), sq_nonneg (x 2)]
    have hz0 := sq_eq_zero_iff.mp h0
    have hz1 := sq_eq_zero_iff.mp h1
    have hz2 := sq_eq_zero_iff.mp h2
    have hzero0 : x 0 = 0 := by linarith
    have hzero1 : x 1 = 0 := by linarith
    apply hx
    funext i
    fin_cases i
    · exact hzero0
    · exact hzero1
    · exact hz2

/-- A genuine dependent block diagonal is positive definite if each block
is positive definite, including empty blocks and an empty block index type. -/
theorem posDef_blockDiagonal_rat {α : Type*} [Fintype α] [DecidableEq α]
    {ι : α → Type*} [∀ a, Fintype (ι a)]
    (B : ∀ a, Matrix (ι a) (ι a) ℚ) (hB : ∀ a, (B a).PosDef) :
    (Matrix.blockDiagonal' B).PosDef := by
  have hmul (x : (Σ a, ι a) → ℚ) (a : α) (i : ι a) :
      (Matrix.blockDiagonal' B *ᵥ x) ⟨a, i⟩ =
        (B a *ᵥ (fun j => x ⟨a, j⟩)) i := by
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
    rw [Fintype.sum_eq_single a]
    · simp only [Matrix.blockDiagonal'_apply_eq]
    · intro b hba
      apply Finset.sum_eq_zero
      intro j _
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hba.symm, zero_mul]
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    rintro ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b
    · subst b
      simpa only [Matrix.blockDiagonal'_apply_eq] using (hB a).1.apply i j
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hab,
        Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hab), star_zero]
  · intro x hx
    have hsum : dotProduct (star x) (Matrix.blockDiagonal' B *ᵥ x) =
        ∑ a, dotProduct (star (fun j => x ⟨a, j⟩))
          (B a *ᵥ (fun j => x ⟨a, j⟩)) := by
      simp only [dotProduct, Fintype.sum_sigma, Pi.star_apply, hmul]
    rw [hsum]
    obtain ⟨⟨a, i⟩, hi⟩ := Function.ne_iff.mp hx
    apply Finset.sum_pos'
    · intro a _
      exact (hB a).posSemidef.2 _
    · refine ⟨a, Finset.mem_univ _, (hB a).2 _ ?_⟩
      intro hz
      exact hi (congrFun hz i)

private theorem scalar_posDef {b : ℚ} (hb : 0 < b) :
    Matrix.PosDef (fun (_ : Unit) (_ : Unit) => b) := by
  refine ⟨Matrix.IsHermitian.ext (fun _ _ => by simp), ?_⟩
  intro x hx
  have hx0 : x () ≠ 0 := by
    intro hz
    apply hx
    funext i
    cases i
    exact hz
  have hpositive := mul_pos hb (sq_pos_of_ne_zero hx0)
  simp only [star_trivial, Matrix.mulVec, dotProduct, Fintype.sum_unique]
  change 0 < x () * (b * x ())
  nlinarith [hpositive]

/-- The seven weighted-root shapes are positive definite even at weight two. -/
theorem rootedArmMatrix_posDef (shape : RootedArmShape) {b : ℚ} (hb : 2 ≤ b) :
    (rootedArmMatrix shape b).PosDef := by
  have hlength : ∀ a, rootedArmLengths shape a ≤ 3 := by
    intro a
    cases shape <;> fin_cases a <;> norm_num [rootedArmLengths]
  have hD : (chainArms (𝕜 := ℚ) (rootedArmLengths shape)).PosDef :=
    posDef_blockDiagonal_rat _ (fun a => weightTwoChain_posDef_of_le_three _ (hlength a))
  have hS : 0 < rootedStarSchur (rootedArmLengths shape) b := by
    rw [rootedArm_schur]
    cases shape <;>
      norm_num [rootedArmDenominator, rootedArmGreenNumerator] <;> linarith
  letI : Invertible (chainArms (𝕜 := ℚ) (rootedArmLengths shape)) :=
    (isUnit_chainArms _).invertible
  have h := posDef_fromBlocks_of_schur
    (fun (_ : Unit) (_ : Unit) => b)
    (Matrix.replicateRow Unit (-armSpokes (rootedArmLengths shape))) hD
  simp only [Matrix.conjTranspose_replicateRow, star_trivial] at h
  apply h
  rw [rootedStar_schur]
  exact scalar_posDef hS

/-- The eighth shape, rooted at a leaf of the three-leaf star, is positive
definite for every rational root weight at least two. -/
theorem leafRootedStarMatrix_posDef {b : ℚ} (hb : 2 ≤ b) :
    (leafRootedStarMatrix b).PosDef := by
  letI : Invertible (weightTwoChain (𝕜 := ℚ) 3) := (isUnit_weightTwoChain 3).invertible
  have hD := weightTwoChain_posDef_of_le_three 3 (by decide)
  have h := posDef_fromBlocks_of_schur
    (fun (_ : Unit) (_ : Unit) => b)
    (Matrix.replicateRow Unit (Pi.single (1 : Fin 3) (-1 : ℚ))) hD
  simp only [Matrix.conjTranspose_replicateRow, star_trivial] at h
  apply h
  exact Eq.mpr (congrArg Matrix.PosDef (leafRootedStar_schur b))
    (scalar_posDef (b := b - 1) (by linarith))

/-- Actual occurrence witnesses for all eight root choices, uniformly at
`b ≥ 2`. In particular the canonical all-weight-two choices are included. -/
theorem rootedBlockMatrixAt_posDef (choice : RootedBlockChoice) {b : ℚ} (hb : 2 ≤ b) :
    (rootedBlockMatrixAt choice b).PosDef := by
  cases choice with
  | arms shape => exact rootedArmMatrix_posDef shape hb
  | leafStar => exact leafRootedStarMatrix_posDef hb

end KltDP.LinearAlgebra
