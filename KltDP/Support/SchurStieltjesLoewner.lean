import KltDP.LinearAlgebra.PrincipalSubmatrixComparison
import KltDP.LinearAlgebra.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# F26: Schur complements, Stieltjes inverses and Loewner comparisons

Foundation obligation F26 (`planning/AUTOFORMALIZATION_PLAN.md` §6,
`planning/THEOREM_MAP.json` id F26; manuscript `lem:stieltjes`,
`source/manuscript.tex` lines 359–365). Everything here is finite matrix
algebra over an ordered field with trivial star, the accepted convention
`[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]`
of `KltDP.LinearAlgebra.Stieltjes`; it applies to `ℚ` and `ℝ` alike, and no
scalar extension, square root or `RCLike` structure is used. No geometric
object is constructed or assumed.

Planned exports (the plan placed them under `KltDP.Geometry`; the accepted
code lives under `KltDP.LinearAlgebra`, and this module exports them in
`KltDP.Support`):
* `stieltjes_inverse_nonnegative`: accepted
  `KltDP.LinearAlgebra.stieltjes_inverse_nonnegative` (manuscript line 360,
  first assertion of `lem:stieltjes`).
* `stieltjes_inverse_positive_connected`: accepted
  `KltDP.LinearAlgebra.stieltjes_inverse_positive` (line 360, second
  assertion; connectedness is `Preconnected` of the graph of nonzero
  off-diagonal entries).
* `schurComplement_positiveDefinite`: new. For a positive-definite block
  matrix `fromBlocks A B Bᴴ D` the blocks `A`, `D` and the Schur complement
  `D - Bᴴ A⁻¹ B` are positive definite (`principal_blocks_posDef`,
  `schurComplement_positiveDefinite`); the determinant factorization
  `det = det A · det (D - C A⁻¹ B)` (`schurComplement_det`, from the pinned
  `det_fromBlocks₁₁`) and the block inverse formula
  (`schurComplement_inverse`, from the pinned `invOf_fromBlocks₁₁_eq`). For a
  positive-definite `fromBlocks A₁₁ A₁₂ A₂₁ A₂₂` with an unconstrained
  lower-left block, `fromBlocks_posDef_lower_eq` shows `A₂₁ = A₁₂ᴴ`, and
  `schurComplement_positiveDefinite'`, `schurComplement_inverse'` restate the
  complement and inverse with `A₂₁`.
* `rankOneInverseFormula`: new. Sherman–Morrison,
  `(A + u vᵀ)⁻¹ = A⁻¹ - (1 + vᵀA⁻¹u)⁻¹ (A⁻¹ u vᵀ A⁻¹)` for invertible `A` and
  `1 + vᵀA⁻¹u ≠ 0`, with `u vᵀ = vecMulVec u v`; and the matrix determinant
  lemma `det (A + u vᵀ) = det A · (1 + vᵀA⁻¹u)` (`rankOneDetFormula`, from
  the pinned `det_add_replicateCol_mul_replicateRow`).
* `inverse_loewner_order_reverse`: new. If `A`, `B` are positive definite
  and `B - A` is positive semidefinite then `A⁻¹ - B⁻¹` is positive
  semidefinite. Proved by the variational inequality
  `2 xᵀy - yᵀAy ≤ xᵀA⁻¹x` with equality at `y = A⁻¹x`
  (`quadratic_le_inverse`, `inverse_quadratic_attained`); no square roots.
* `blockProjectionIdentities`: the accepted bordered-Gram identities of
  `KltDP.LinearAlgebra.SchurComplement` (`borderedGram_mulVec_orthogonalCorrection`,
  `orthogonalCorrection_square`, `det_borderedGram`), re-exported as one
  statement.

Further clauses of the F26 goal: principal positivity is the accepted
`posDef_principal_submatrix` (`principal_submatrix_posDef`, with the `toBlock`
and `reindex` forms `principal_toBlock_posDef`, `principal_reindex_posDef`)
together with `posDef_diag_pos`; nonsingularity is the accepted `isUnit_of_posDef`
(`posDef_isUnit`); positive definiteness of the inverse is `posDef_inv`; the
inverse diagonal lower bound `1 / A i i ≤ A⁻¹ i i` is
`inverse_diag_lower_bound`. `f26_core` bundles all clauses.

Not proved here (not required by the goal, but recorded): positivity of the
determinant of a positive-definite matrix over a general ordered field (the
pinned `Matrix.PosDef.det_pos` needs `RCLike`).
-/

namespace KltDP.Support

open Matrix KltDP.LinearAlgebra

namespace F26

variable {ι 𝕜 : Type*} [Fintype ι] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]

/-! ### Quadratic forms without stars -/

omit [IsStrictOrderedRing 𝕜] in
/-- The defining positivity, with the trivial star removed. -/
theorem quadratic_pos {A : Matrix ι ι 𝕜} (hA : A.PosDef) {x : ι → 𝕜} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by
  simpa only [star_trivial] using hA.2 x hx

omit [IsStrictOrderedRing 𝕜] in
theorem quadratic_nonneg {A : Matrix ι ι 𝕜} (hA : A.PosDef) (x : ι → 𝕜) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · exact (quadratic_pos hA hx).le

omit [Fintype ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With trivial star, Hermitian means symmetric. -/
theorem transpose_eq_of_isHermitian {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) : Aᵀ = A := by
  have h := hA.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- A symmetric matrix can be moved across the dot product. -/
theorem dotProduct_mulVec_comm_of_symm {A : Matrix ι ι 𝕜} (hA : Aᵀ = A) (x y : ι → 𝕜) :
    x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

/-! ### Principal positivity and nonsingularity (accepted, re-exported) -/

omit [IsStrictOrderedRing 𝕜] in
/-- Diagonal entries of a positive-definite matrix are positive. -/
theorem posDef_diag_pos [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef) (i : ι) :
    0 < A i i := by
  have hx : (Pi.single i (1 : 𝕜) : ι → 𝕜) ≠ 0 := by
    intro h
    have := congrFun h i
    simp at this
  have h := quadratic_pos hA hx
  simpa only [Matrix.mulVec_single_one, single_dotProduct, Matrix.transpose_apply,
    one_mul] using h

omit [IsStrictOrderedRing 𝕜] [TrivialStar 𝕜] in
/-- Principal positivity: the accepted `posDef_principal_submatrix`. -/
theorem principal_submatrix_posDef [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.PosDef) (e : κ → ι) (he : Function.Injective e) :
    (A.submatrix e e).PosDef :=
  posDef_principal_submatrix hA e he

omit [IsStrictOrderedRing 𝕜] [TrivialStar 𝕜] in
/-- Principal positivity in `toBlock` form: the block on the coordinates
satisfying `p` is positive definite. -/
theorem principal_toBlock_posDef [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (p : ι → Prop) [DecidablePred p] : (A.toBlock p p).PosDef :=
  posDef_principal_submatrix hA Subtype.val Subtype.val_injective

omit [IsStrictOrderedRing 𝕜] [TrivialStar 𝕜] in
/-- Principal positivity in `reindex` form: relabelling the coordinates by an
equivalence preserves positive definiteness. -/
theorem principal_reindex_posDef [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.PosDef) (e : ι ≃ κ) : (A.reindex e e).PosDef := by
  rw [Matrix.reindex_apply]
  exact posDef_principal_submatrix hA e.symm e.symm.injective

omit [IsStrictOrderedRing 𝕜] in
/-- Nonsingularity: the accepted `isUnit_of_posDef`. -/
theorem posDef_isUnit [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef) : IsUnit A :=
  isUnit_of_posDef hA

omit [IsStrictOrderedRing 𝕜] in
/-- The inverse of a positive-definite matrix is positive definite, directly
over the ordered field. -/
theorem posDef_inv [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef) : A⁻¹.PosDef := by
  letI := (isUnit_of_posDef hA).invertible
  have hsym := transpose_eq_of_isHermitian hA.1
  refine ⟨hA.1.inv, fun x hx => ?_⟩
  simp only [star_trivial]
  have hy : A⁻¹ *ᵥ x ≠ 0 := by
    intro h
    apply hx
    have h' := congrArg (fun z => A *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec,
      Matrix.mulVec_zero] using h'
  have key : x ⬝ᵥ (A⁻¹ *ᵥ x) = (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec, dotProduct_comm]
  rw [key]
  exact quadratic_pos hA hy

/-! ### The variational inequality -/

/-- `2 xᵀy - yᵀAy ≤ xᵀA⁻¹x` for positive-definite `A`: the difference is the
square of `y - A⁻¹x`. -/
theorem quadratic_le_inverse [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (x y : ι → 𝕜) :
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  letI := (isUnit_of_posDef hA).invertible
  have hsym := transpose_eq_of_isHermitian hA.1
  have h1 : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have h2 : (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
    rw [dotProduct_mulVec_comm_of_symm hsym, h1]
  have h3 : (A⁻¹ *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (A⁻¹ *ᵥ x) := dotProduct_comm _ _
  have h4 : y ⬝ᵥ x = x ⬝ᵥ y := dotProduct_comm _ _
  have h0 := quadratic_nonneg hA (y - A⁻¹ *ᵥ x)
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, h2, h3, h4] at h0
  linarith

omit [IsStrictOrderedRing 𝕜] in
/-- Equality holds at `y = A⁻¹x`. -/
theorem inverse_quadratic_attained [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (x : ι → 𝕜) :
    2 * (x ⬝ᵥ (A⁻¹ *ᵥ x)) - (A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (A⁻¹ *ᵥ x)) = x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  letI := (isUnit_of_posDef hA).invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec,
    dotProduct_comm (A⁻¹ *ᵥ x) x]
  ring

/-! ### Inverse diagonal lower bound -/

/-- `1 / A i i ≤ A⁻¹ i i` for positive-definite `A`. -/
theorem inverse_diag_lower_bound [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef) (i : ι) :
    1 / A i i ≤ A⁻¹ i i := by
  have hd := posDef_diag_pos hA i
  have hne : A i i ≠ 0 := hd.ne'
  set e : ι → 𝕜 := Pi.single i 1 with he
  have h := quadratic_le_inverse hA e ((1 / A i i) • e)
  have e1 : e ⬝ᵥ ((1 / A i i) • e) = 1 / A i i := by
    rw [he]
    simp [dotProduct_smul, single_dotProduct]
  have e2 : ((1 / A i i) • e) ⬝ᵥ (A *ᵥ ((1 / A i i) • e)) =
      (1 / A i i) * (1 / A i i) * A i i := by
    rw [he]
    simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, Matrix.mulVec_single_one,
      single_dotProduct, Matrix.transpose_apply, smul_eq_mul, one_mul]
    ring
  have e3 : e ⬝ᵥ (A⁻¹ *ᵥ e) = A⁻¹ i i := by
    rw [he]
    simp only [Matrix.mulVec_single_one, single_dotProduct, Matrix.transpose_apply, one_mul]
  rw [e1, e2, e3] at h
  have hval : 2 * (1 / A i i) - (1 / A i i) * (1 / A i i) * A i i = 1 / A i i := by
    field_simp
    ring
  linarith

/-! ### Loewner order reversal -/

/-- `A ≤ B` in the Loewner order: `B - A` is positive semidefinite. -/
def LoewnerLE (A B : Matrix ι ι 𝕜) : Prop := (B - A).PosSemidef

/-- If `A ≤ B` in the Loewner order and both are positive definite, then
`B⁻¹ ≤ A⁻¹`. -/
theorem inverse_loewner_order_reverse [DecidableEq ι] {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : (B - A).PosSemidef) :
    (A⁻¹ - B⁻¹).PosSemidef := by
  refine ⟨hA.1.inv.sub hB.1.inv, fun x => ?_⟩
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  have hy := quadratic_le_inverse hA x (B⁻¹ *ᵥ x)
  have hle : (B⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (B⁻¹ *ᵥ x)) ≤ (B⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (B⁻¹ *ᵥ x)) := by
    have h := hAB.2 (B⁻¹ *ᵥ x)
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h
    linarith
  have heq := inverse_quadratic_attained hB x
  linarith

theorem loewnerLE_inv_of_loewnerLE [DecidableEq ι] {A B : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : LoewnerLE A B) : LoewnerLE B⁻¹ A⁻¹ :=
  inverse_loewner_order_reverse hA hB hAB

/-! ### Schur complements -/

section Blocks

variable {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [IsStrictOrderedRing 𝕜] [TrivialStar 𝕜] in
/-- The diagonal blocks of a positive-definite block matrix are positive definite. -/
theorem principal_blocks_posDef {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜} {C : Matrix κ ι 𝕜}
    {D : Matrix κ κ 𝕜} (hM : (fromBlocks A B C D).PosDef) : A.PosDef ∧ D.PosDef := by
  have h1 := posDef_principal_submatrix hM Sum.inl Sum.inl_injective
  have h2 := posDef_principal_submatrix hM Sum.inr Sum.inr_injective
  have e1 : (fromBlocks A B C D).submatrix Sum.inl Sum.inl = A := by
    ext i j
    simp [fromBlocks_apply₁₁]
  have e2 : (fromBlocks A B C D).submatrix Sum.inr Sum.inr = D := by
    ext i j
    simp [fromBlocks_apply₂₂]
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

omit [IsStrictOrderedRing 𝕜] [TrivialStar 𝕜] [DecidableEq ι] [DecidableEq κ] in
/-- A positive-definite block matrix is Hermitian, so its lower-left block is
the conjugate transpose of its upper-right block. -/
theorem fromBlocks_posDef_lower_eq {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜} {C : Matrix κ ι 𝕜}
    {D : Matrix κ κ 𝕜} (hM : (fromBlocks A B C D).PosDef) : C = Bᴴ :=
  (Matrix.isHermitian_fromBlocks_iff.mp hM.1).2.1.symm

omit [IsStrictOrderedRing 𝕜] in
/-- The Schur complement of a positive-definite block matrix is positive
definite, by the pinned quadratic completion `schur_complement_eq₁₁`. -/
theorem schurComplement_positiveDefinite {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜}
    {D : Matrix κ κ 𝕜} (hM : (fromBlocks A B Bᴴ D).PosDef) :
    (D - Bᴴ * A⁻¹ * B).PosDef := by
  obtain ⟨hA, hD⟩ := principal_blocks_posDef hM
  letI := (isUnit_of_posDef hA).invertible
  refine ⟨hD.1.sub (Matrix.isHermitian_conjTranspose_mul_mul B hA.1.inv), fun y hy => ?_⟩
  simp only [star_trivial]
  have hxy : Sum.elim (-((A⁻¹ * B) *ᵥ y)) y ≠ 0 := by
    intro h
    apply hy
    funext i
    simpa using congrFun h (Sum.inr i)
  have hpos := quadratic_pos hM hxy
  have hschur := Matrix.schur_complement_eq₁₁ B D (-((A⁻¹ * B) *ᵥ y)) y hA.1
  simp only [star_trivial] at hschur
  rw [dotProduct_mulVec, hschur, neg_add_cancel, Matrix.zero_vecMul, zero_dotProduct, zero_add,
    ← dotProduct_mulVec] at hpos
  exact hpos

omit [IsStrictOrderedRing 𝕜] in
/-- The Schur complement `A₂₂ - A₂₁ A₁₁⁻¹ A₁₂` of a positive-definite block
matrix `fromBlocks A₁₁ A₁₂ A₂₁ A₂₂` is positive definite (the lower-left block
is forced to be `A₁₂ᴴ` by `fromBlocks_posDef_lower_eq`). -/
theorem schurComplement_positiveDefinite' {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜}
    {C : Matrix κ ι 𝕜} {D : Matrix κ κ 𝕜} (hM : (fromBlocks A B C D).PosDef) :
    (D - C * A⁻¹ * B).PosDef := by
  have hC := fromBlocks_posDef_lower_eq hM
  subst hC
  exact schurComplement_positiveDefinite hM

omit [IsStrictOrderedRing 𝕜] in
/-- The determinant of a block matrix with positive-definite upper block
factors through the Schur complement (pinned `det_fromBlocks₁₁`). -/
theorem schurComplement_det {A : Matrix ι ι 𝕜} (hA : A.PosDef) (B : Matrix ι κ 𝕜)
    (C : Matrix κ ι 𝕜) (D : Matrix κ κ 𝕜) :
    (fromBlocks A B C D).det = A.det * (D - C * A⁻¹ * B).det := by
  letI := (isUnit_of_posDef hA).invertible
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]

omit [IsStrictOrderedRing 𝕜] in
/-- The block inverse of a positive-definite block matrix (pinned
`invOf_fromBlocks₁₁_eq`, with the inverses of `A`, of the Schur complement
and of the whole matrix supplied by positive definiteness). -/
theorem schurComplement_inverse {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜}
    {D : Matrix κ κ 𝕜} (hM : (fromBlocks A B Bᴴ D).PosDef) :
    (fromBlocks A B Bᴴ D)⁻¹ =
      fromBlocks (A⁻¹ + A⁻¹ * B * (D - Bᴴ * A⁻¹ * B)⁻¹ * Bᴴ * A⁻¹)
        (-(A⁻¹ * B * (D - Bᴴ * A⁻¹ * B)⁻¹))
        (-((D - Bᴴ * A⁻¹ * B)⁻¹ * Bᴴ * A⁻¹)) (D - Bᴴ * A⁻¹ * B)⁻¹ := by
  have hA := (principal_blocks_posDef hM).1
  have hS := schurComplement_positiveDefinite hM
  letI iA : Invertible A := (isUnit_of_posDef hA).invertible
  have hS' : (D - Bᴴ * ⅟A * B).PosDef := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact hS
  letI iS : Invertible (D - Bᴴ * ⅟A * B) := (isUnit_of_posDef hS').invertible
  letI iM : Invertible (fromBlocks A B Bᴴ D) := (isUnit_of_posDef hM).invertible
  have h := Matrix.invOf_fromBlocks₁₁_eq A B Bᴴ D
  rw [Matrix.invOf_eq_nonsing_inv] at h
  rw [h]
  simp only [Matrix.invOf_eq_nonsing_inv]

omit [IsStrictOrderedRing 𝕜] in
/-- The block inverse of a positive-definite block matrix
`fromBlocks A₁₁ A₁₂ A₂₁ A₂₂`, written with the lower-left block `A₂₁`. -/
theorem schurComplement_inverse' {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜}
    {C : Matrix κ ι 𝕜} {D : Matrix κ κ 𝕜} (hM : (fromBlocks A B C D).PosDef) :
    (fromBlocks A B C D)⁻¹ =
      fromBlocks (A⁻¹ + A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹ * C * A⁻¹)
        (-(A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹))
        (-((D - C * A⁻¹ * B)⁻¹ * C * A⁻¹)) (D - C * A⁻¹ * B)⁻¹ := by
  have hC := fromBlocks_posDef_lower_eq hM
  subst hC
  exact schurComplement_inverse hM

end Blocks

/-! ### Rank-one updates -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- Two rank-one matrices with a matrix between them collapse to a scalar
multiple of a rank-one matrix. -/
theorem vecMulVec_mul_vecMulVec (u v u' v' : ι → 𝕜) (M : Matrix ι ι 𝕜) :
    vecMulVec u v * M * vecMulVec u' v' = (v ⬝ᵥ (M *ᵥ u')) • vecMulVec u v' := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.mulVec, Matrix.smul_apply,
    smul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

omit [Fintype ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- The scalar identity behind Sherman–Morrison. -/
theorem rankOne_scalar_identity {w : 𝕜} (hc : 1 + w ≠ 0) :
    (1 : 𝕜) - (1 + w)⁻¹ - (1 + w)⁻¹ * w = 0 := by
  rw [sub_sub, ← mul_one_add, inv_mul_cancel₀ hc, sub_self]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- Sherman–Morrison: the inverse of a rank-one update. -/
theorem rankOneInverseFormula [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : IsUnit A)
    (u v : ι → 𝕜) (hc : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)⁻¹ =
      A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A⁻¹ * vecMulVec u v * A⁻¹) := by
  letI := hA.invertible
  apply Matrix.inv_eq_right_inv
  have key : vecMulVec u v * A⁻¹ * vecMulVec u v = (v ⬝ᵥ (A⁻¹ *ᵥ u)) • vecMulVec u v :=
    vecMulVec_mul_vecMulVec u v u v A⁻¹
  have h1 : A * (A⁻¹ * vecMulVec u v * A⁻¹) = vecMulVec u v * A⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  have h2 : vecMulVec u v * (A⁻¹ * vecMulVec u v * A⁻¹) =
      (v ⬝ᵥ (A⁻¹ *ᵥ u)) • (vecMulVec u v * A⁻¹) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.smul_mul]
  have hscalar : (1 : 𝕜) - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ -
      (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ * (v ⬝ᵥ (A⁻¹ *ᵥ u)) = 0 := rankOne_scalar_identity hc
  calc (A + vecMulVec u v) * (A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A⁻¹ * vecMulVec u v * A⁻¹))
      = A * A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A * (A⁻¹ * vecMulVec u v * A⁻¹)) +
          (vecMulVec u v * A⁻¹ -
            (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (vecMulVec u v * (A⁻¹ * vecMulVec u v * A⁻¹))) := by
        rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul]
    _ = 1 - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (vecMulVec u v * A⁻¹) +
          (vecMulVec u v * A⁻¹ -
            ((1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ * (v ⬝ᵥ (A⁻¹ *ᵥ u))) • (vecMulVec u v * A⁻¹)) := by
        rw [Matrix.mul_inv_of_invertible, h1, h2, smul_smul]
    _ = 1 + ((1 : 𝕜) - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ -
          (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ * (v ⬝ᵥ (A⁻¹ *ᵥ u))) • (vecMulVec u v * A⁻¹) := by
        simp only [sub_smul, one_smul]
        abel
    _ = 1 := by
        rw [hscalar, zero_smul, add_zero]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- The `1 × 1` entry `vᵀ M u` of `replicateRow v * M * replicateCol u`. -/
theorem replicateRow_mul_mul_replicateCol_apply {ι' : Type*} (v u : ι → 𝕜)
    (M : Matrix ι ι 𝕜) (i j : ι') :
    (replicateRow ι' v * M * replicateCol ι' u) i j = v ⬝ᵥ (M *ᵥ u) := by
  simp only [Matrix.mul_apply, replicateRow_apply, replicateCol_apply, dotProduct,
    Matrix.mulVec]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- The matrix determinant lemma for a rank-one update (pinned
`det_add_replicateCol_mul_replicateRow`). -/
theorem rankOneDetFormula [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : IsUnit A) (u v : ι → 𝕜) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  rw [Matrix.vecMulVec_eq (ι := Unit), Matrix.det_add_replicateCol_mul_replicateRow hdet,
    Matrix.det_unique (1 + replicateRow Unit v * A⁻¹ * replicateCol Unit u), Matrix.add_apply,
    Matrix.one_apply_eq, replicateRow_mul_mul_replicateCol_apply]

/-! ### Stieltjes inverses and bordered projections (accepted, re-exported) -/

/-- First assertion of `lem:stieltjes` (manuscript line 360): the accepted
`KltDP.LinearAlgebra.stieltjes_inverse_nonnegative`. -/
theorem stieltjes_inverse_nonnegative [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) : ∀ i j, 0 ≤ A⁻¹ i j :=
  KltDP.LinearAlgebra.stieltjes_inverse_nonnegative hA hOff

/-- Second assertion of `lem:stieltjes` (line 360): the accepted
`KltDP.LinearAlgebra.stieltjes_inverse_positive`. -/
theorem stieltjes_inverse_positive_connected [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hConn : (nonzeroOffDiagonalGraph A).Preconnected) : ∀ i j, 0 < A⁻¹ i j :=
  KltDP.LinearAlgebra.stieltjes_inverse_positive hA hOff hConn

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- The accepted bordered-Gram projection identities: the correction vector
`(A⁻¹p, 1)` is orthogonal to the exceptional block, its square is the scalar
Schur complement `d + pᵀA⁻¹p`, and the bordered determinant is
`det (-A) · (d + pᵀA⁻¹p)`. -/
theorem blockProjectionIdentities [DecidableEq ι] {A : Matrix ι ι 𝕜} (hA : IsUnit A)
    (p : ι → 𝕜) (d : 𝕜) :
    borderedGram A p d *ᵥ orthogonalCorrection A p =
        Sum.elim (0 : ι → 𝕜) (fun (_ : Unit) => d + p ⬝ᵥ (A⁻¹ *ᵥ p)) ∧
      orthogonalCorrection A p ⬝ᵥ (borderedGram A p d *ᵥ orthogonalCorrection A p) =
        d + p ⬝ᵥ (A⁻¹ *ᵥ p) ∧
      (borderedGram A p d).det = (-A).det * (d + p ⬝ᵥ (A⁻¹ *ᵥ p)) :=
  ⟨borderedGram_mulVec_orthogonalCorrection hA p d, orthogonalCorrection_square hA p d,
    det_borderedGram hA p d⟩

end F26

open F26

/-- **F26 core.** Over an ordered field with trivial star, for finite index
types `ι`, `κ`: principal positivity and positive diagonals, nonsingularity,
positive definiteness of the inverse, the Schur complement (positive
definiteness of the blocks and of the complement, determinant factorization,
block inverse), the rank-one inverse and determinant formulas, the inverse
diagonal lower bound, reversal of the Loewner order under inversion, and the
two assertions of `lem:stieltjes`. -/
theorem f26_core {ι κ 𝕜 : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] :
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → ∀ e : κ → ι, Function.Injective e →
      (A.submatrix e e).PosDef) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → ∀ i, 0 < A i i) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → IsUnit A) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → A⁻¹.PosDef) ∧
    (∀ {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜} {D : Matrix κ κ 𝕜},
      (fromBlocks A B Bᴴ D).PosDef → A.PosDef ∧ D.PosDef ∧ (D - Bᴴ * A⁻¹ * B).PosDef) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → ∀ (B : Matrix ι κ 𝕜) (C : Matrix κ ι 𝕜) (D : Matrix κ κ 𝕜),
      (fromBlocks A B C D).det = A.det * (D - C * A⁻¹ * B).det) ∧
    (∀ {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜} {D : Matrix κ κ 𝕜},
      (fromBlocks A B Bᴴ D).PosDef →
        (fromBlocks A B Bᴴ D)⁻¹ =
          fromBlocks (A⁻¹ + A⁻¹ * B * (D - Bᴴ * A⁻¹ * B)⁻¹ * Bᴴ * A⁻¹)
            (-(A⁻¹ * B * (D - Bᴴ * A⁻¹ * B)⁻¹))
            (-((D - Bᴴ * A⁻¹ * B)⁻¹ * Bᴴ * A⁻¹)) (D - Bᴴ * A⁻¹ * B)⁻¹) ∧
    (∀ {A : Matrix ι ι 𝕜} {B : Matrix ι κ 𝕜} {C : Matrix κ ι 𝕜} {D : Matrix κ κ 𝕜},
      (fromBlocks A B C D).PosDef → C = Bᴴ ∧ (D - C * A⁻¹ * B).PosDef ∧
        (fromBlocks A B C D)⁻¹ =
          fromBlocks (A⁻¹ + A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹ * C * A⁻¹)
            (-(A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹))
            (-((D - C * A⁻¹ * B)⁻¹ * C * A⁻¹)) (D - C * A⁻¹ * B)⁻¹) ∧
    (∀ {A : Matrix ι ι 𝕜}, IsUnit A → ∀ u v : ι → 𝕜, 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0 →
      (A + vecMulVec u v)⁻¹ =
        A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A⁻¹ * vecMulVec u v * A⁻¹)) ∧
    (∀ {A : Matrix ι ι 𝕜}, IsUnit A → ∀ u v : ι → 𝕜,
      (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → ∀ i, 1 / A i i ≤ A⁻¹ i i) ∧
    (∀ {A B : Matrix ι ι 𝕜}, A.PosDef → B.PosDef → (B - A).PosSemidef →
      (A⁻¹ - B⁻¹).PosSemidef) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → (∀ i j, i ≠ j → A i j ≤ 0) → ∀ i j, 0 ≤ A⁻¹ i j) ∧
    (∀ {A : Matrix ι ι 𝕜}, A.PosDef → (∀ i j, i ≠ j → A i j ≤ 0) →
      (nonzeroOffDiagonalGraph A).Preconnected → ∀ i j, 0 < A⁻¹ i j) :=
  ⟨fun hA e he => principal_submatrix_posDef hA e he,
    fun hA i => posDef_diag_pos hA i,
    fun hA => posDef_isUnit hA,
    fun hA => posDef_inv hA,
    fun hM => ⟨(principal_blocks_posDef hM).1, (principal_blocks_posDef hM).2,
      schurComplement_positiveDefinite hM⟩,
    fun hA B C D => schurComplement_det hA B C D,
    fun hM => schurComplement_inverse hM,
    fun hM => ⟨fromBlocks_posDef_lower_eq hM, schurComplement_positiveDefinite' hM,
      schurComplement_inverse' hM⟩,
    fun hA u v hc => rankOneInverseFormula hA u v hc,
    fun hA u v => rankOneDetFormula hA u v,
    fun hA i => inverse_diag_lower_bound hA i,
    fun hA hB hAB => inverse_loewner_order_reverse hA hB hAB,
    fun hA hOff => F26.stieltjes_inverse_nonnegative hA hOff,
    fun hA hOff hConn => F26.stieltjes_inverse_positive_connected hA hOff hConn⟩

end KltDP.Support
