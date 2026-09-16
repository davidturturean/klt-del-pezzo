import KltDP.Lattices.TenRowPicardExclusions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Intersection-lattice numbers at equality

Manuscript `cor:equality-lattice` (`source/manuscript.tex`, lines 3336–3361)
lists numerical invariants of the seven-point equality surface. This module
proves those numbers as statements about explicit integer and rational
matrices and vectors on the index type `Fin 4 ⊕ Fin 2 × Fin 3`. No surface,
divisor, Picard group or intersection form is constructed or assumed. The
identification of `negMatrix` with the negative intersection matrix of the
actual exceptional divisor `D`, of the contact vectors with actual
intersection numbers, and of any lattice with `Pic(S)`, is a separate
geometric obligation and is not claimed here.

Coverage, by manuscript sentence:
* lines 3229–3230 and 3357–3358 ("the negative matrix of `D` is the sum of
  four `[3]` blocks and three `A_2` blocks"): `negMatrix` is that
  block-diagonal matrix by definition (`negMatrix_blocks`); `negMatrix_diag`,
  `negMatrix_offDiag`, `negMatrix_symm` record its entries.
* line 3340 ("`det A_D = 3^7`"): `negMatrix_det`, `negMatrixQ_det` (value
  `2187`), with the decimal disambiguation `three_pow_seven_ne_37`.
* line 3339 ("ten original exceptional components"): `card_index`.
* line 3340 ("three original edges") and line 3360 ("`10-3=7` is the
  component count of the exceptional forest"): `negMatrix_pair_count` (six
  ordered adjacent pairs), `dualGraph_card_edgeFinset` (three edges of the
  graph read off the matrix), `card_connectedComponent` (seven components of
  that graph), `card_blocks` and `ten_sub_three`.
* line 3347 ("no isolated exceptional nodes") and lines 3358–3359 ("no
  isolated `A_1` component"): `negMatrix_no_isolated_node`,
  `negMatrix_weight_three_isolated`, `no_isolated_a1_block`.
* lines 3290–3295 (shortest contact rows `P_i : B, F_i, V_i` and
  `T_i : F_j, F_k, U_i`): `contactP`, `contactT`.
* line 3343 ("`pᵀ A_D⁻¹ p = 4/3`" at every shortest center): `contactP_green`
  and `contactT_green`, through the explicit inverse `negMatrixInvQ`
  (`negMatrixQ_inv`).
* line 3344 ("`|det ⟨D,P⟩| = 3^6`"): `borderedGram_contactP_det`,
  `borderedGram_contactT_det`, `borderedGram_contact_absDet` (value `729`),
  using the accepted `det_minusOne_borderedGram`, with
  `three_pow_six_ne_36`.
* line 3345 ("`[Pic(S) : ⟨D,P⟩] = 27`"): `span_index_eq_27` and
  `sublattice_index_eq_27`. Both are conditional on an actual unimodular
  integral lattice (`IsUnimodular`, definitionally the accepted determinant
  condition) with a basis indexed by `Index ⊕ Unit` whose Gram matrix on the
  family is the bordered matrix (for the sublattice form, `SublatticeGramIs`);
  they use the accepted index-square relations of `TenRowPicardExclusions`
  and `IndexDeterminant` through the abstract-index steps
  `span_index_eq_27_of_natAbs_det` and `sublattice_index_eq_27_of_absDet`.
  `sqrt_729` records `27 ^ 2 = 729`.
* line 3340 ("`ℓ = L^2 = 1/3`"), line 468 (`H^2 = K^2 + qᵀA⁻¹q`) and lines
  612–620 (`pᵀA⁻¹p = 1 + (L·P)^2/K_Y^2`, `pᵀA⁻¹q = 1 - L·P`):
  `canonicalSource_green`, `anticanonical_square_value`, `contactP_charge`,
  `contactT_charge`, `degree_value`, `green_projection_check` are the
  numerical evaluations of those formulas with `K_S^2 = -1` and the
  canonical source `q = weight - 2`. They do not prove the geometric
  identities themselves.
* `u_equality_numbers` bundles the unconditional numerical clauses.

The graph `dualGraph` is the combinatorial graph whose adjacency is a nonzero
off-diagonal entry of `negMatrix`; `graphWeightMatrix_dualGraph` identifies
`negMatrixQ` with the accepted `graphWeightMatrix` convention for it.

Reuse: `borderedGram`, `det_minusOne_borderedGram`, `graphWeightMatrix`,
`familyGram`, `span_index_sq_of_gram_det`, `natAbs_det_of_rational_matrix`
and `natAbs_det_gram_restriction_of_unimodular` are the accepted project
declarations; the pinned Mathlib block-determinant, block-multiplication,
`Fin 2` notation and nonsingular-inverse lemmas supply the algebra.
-/

namespace KltDP.Support

open Matrix KltDP.LinearAlgebra KltDP.Lattices.TenRowPicardExclusions
open KltDP.Lattices.SmallADEForestLattice KltDP.Lattices.IndexDeterminant
open LinearMap (BilinForm)
open scoped BigOperators

namespace EqualityNumbers

/-- Index set of the ten exceptional components: `Sum.inl 0` is `B`,
`Sum.inl i.succ` is `F_i`, and `Sum.inr (0, i)`, `Sum.inr (1, i)` are
`U_i`, `V_i` (manuscript lines 3229–3230). -/
abbrev Index : Type := Fin 4 ⊕ Fin 2 × Fin 3

/-- The negative intersection matrix `A_D`: four `[3]` blocks and three
`A_2 = [[2,-1],[-1,2]]` blocks (manuscript lines 3229–3230, 3357–3358). -/
def negMatrix : Matrix Index Index ℤ :=
  fromBlocks (diagonal fun _ : Fin 4 => 3) 0 0
    (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ))

/-- The same matrix over `ℚ`, the field used by the accepted `borderedGram`. -/
def negMatrixQ : Matrix Index Index ℚ :=
  fromBlocks (diagonal fun _ : Fin 4 => 3) 0 0
    (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℚ))

/-- The explicit inverse of `negMatrixQ`: `[1/3]` blocks and
`A_2⁻¹ = (1/3)[[2,1],[1,2]]` blocks. -/
def negMatrixInvQ : Matrix Index Index ℚ :=
  fromBlocks (diagonal fun _ : Fin 4 => 1 / 3) 0 0
    (blockDiagonal fun _ : Fin 3 =>
      (!![2 / 3, 1 / 3; 1 / 3, 2 / 3] : Matrix (Fin 2) (Fin 2) ℚ))

/-- Three times the inverse, as an integer matrix. -/
def negMatrixInv3 : Matrix Index Index ℤ :=
  fromBlocks (diagonal fun _ : Fin 4 => 1) 0 0
    (blockDiagonal fun _ : Fin 3 => (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ))

/-- Weights: three on the isolated components, two on the chain components. -/
def weight : Index → ℕ := Sum.elim (fun _ => 3) (fun _ => 2)

/-- Contact row of the shortest curve `P_i`: `B`, `F_i`, `V_i` once each
(manuscript line 3294). -/
def contactP (i : Fin 3) : Index → ℤ :=
  Sum.elim (fun j : Fin 4 => if j = 0 ∨ j = i.succ then 1 else 0)
    (fun uv : Fin 2 × Fin 3 => if uv = (1, i) then 1 else 0)

/-- Contact row of the shortest curve `T_i`: `F_j`, `F_k` (`j, k ≠ i`) and
`U_i` once each (manuscript line 3295). -/
def contactT (i : Fin 3) : Index → ℤ :=
  Sum.elim (fun j : Fin 4 => if j ≠ 0 ∧ j ≠ i.succ then 1 else 0)
    (fun uv : Fin 2 × Fin 3 => if uv = (0, i) then 1 else 0)

/-- The canonical source `q = weight - 2` of the accepted row conventions. -/
def canonicalSource : Index → ℤ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- Rational contact row of `P_i`. -/
def contactPQ (i : Fin 3) : Index → ℚ := fun v => (contactP i v : ℚ)

/-- Rational contact row of `T_i`. -/
def contactTQ (i : Fin 3) : Index → ℚ := fun v => (contactT i v : ℚ)

/-- Rational canonical source. -/
def canonicalSourceQ : Index → ℚ := fun v => (canonicalSource v : ℚ)

/-! ### Local instances of the pinned block-determinant lemmas

Instantiating the pinned lemmas directly at the concrete ten-element index
type makes the elaborator and the kernel unfold the determinant; stating them
once with this file's instances and abstract index types avoids that. -/

theorem det_fromBlocks_zero_int {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℤ) (D : Matrix n n ℤ) :
    (fromBlocks A 0 0 D).det = A.det * D.det :=
  det_fromBlocks_zero₂₁ _ _ _

theorem det_fromBlocks_zero_rat {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℚ) (D : Matrix n n ℚ) :
    (fromBlocks A 0 0 D).det = A.det * D.det :=
  det_fromBlocks_zero₂₁ _ _ _

theorem det_minusOne_borderedGram_rat {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℚ} (hA : IsUnit A) (p : ι → ℚ) :
    (borderedGram A p (-1)).det =
      (-1 : ℚ) ^ Fintype.card ι * A.det * (p ⬝ᵥ (A⁻¹ *ᵥ p) - 1) :=
  det_minusOne_borderedGram hA p

/-! ### Block structure, entries and determinant -/

/-- The block description is the definition (manuscript lines 3357–3358). -/
theorem negMatrix_blocks :
    negMatrix = fromBlocks (diagonal fun _ : Fin 4 => (3 : ℤ)) 0 0
      (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ)) := rfl

/-- Ten components (manuscript line 3339). -/
theorem card_index : Fintype.card Index = 10 := by
  simp [Index]

/-- Seven blocks: four isolated ones and three chains. -/
theorem card_blocks : Fintype.card (Fin 4 ⊕ Fin 3) = 7 := by
  simp

/-- The manuscript's component count `10 - 3 = 7` (line 3360). -/
theorem ten_sub_three : (10 : ℕ) - 3 = 7 := by norm_num

theorem negMatrix_symm : ∀ i j : Index, negMatrix i j = negMatrix j i := by decide

/-- The diagonal is the weight: `3` on `B, F_i` and `2` on `U_i, V_i`. -/
theorem negMatrix_diag : ∀ i : Index, negMatrix i i = (weight i : ℤ) := by decide

/-- Every off-diagonal entry is `0` or `-1`: the graph is simple. -/
theorem negMatrix_offDiag :
    ∀ i j : Index, i ≠ j → negMatrix i j = 0 ∨ negMatrix i j = -1 := by decide

/-- Six ordered adjacent pairs, i.e. three edges (manuscript line 3340). -/
theorem negMatrix_pair_count :
    ((Finset.univ : Finset (Index × Index)).filter
      fun ij => ij.1 ≠ ij.2 ∧ negMatrix ij.1 ij.2 ≠ 0).card = 6 := by decide

/-- No weight-two component is isolated (manuscript lines 3347, 3358–3359). -/
theorem negMatrix_no_isolated_node :
    ∀ i : Index, negMatrix i i = 2 → ∃ j, j ≠ i ∧ negMatrix i j ≠ 0 := by decide

/-- Every weight-three component is isolated: the `[3]` blocks. -/
theorem negMatrix_weight_three_isolated :
    ∀ i : Index, negMatrix i i = 3 → ∀ j, j ≠ i → negMatrix i j = 0 := by decide

/-- No `1 × 1` block equals `[2]`: an isolated component has weight three. -/
theorem no_isolated_a1_block :
    ∀ i : Index, (∀ j, j ≠ i → negMatrix i j = 0) → negMatrix i i = 3 := by decide

/-- The rational block description is the definition. -/
theorem negMatrixQ_blocks :
    negMatrixQ = fromBlocks (diagonal fun _ : Fin 4 => (3 : ℚ)) 0 0
      (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℚ)) := rfl

/-- The four `[3]` blocks contribute `3^4 = 81`. -/
theorem diagonal_three_det : (diagonal fun _ : Fin 4 => (3 : ℤ)).det = 81 := by
  rw [det_diagonal, Fin.prod_univ_four]
  norm_num

/-- The three `A_2` blocks contribute `3^3 = 27`. -/
theorem cartan_blocks_det :
    (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ)).det = 27 := by
  rw [det_blockDiagonal, Fin.prod_univ_three, det_fin_two_of]
  norm_num

theorem diagonal_three_detQ : (diagonal fun _ : Fin 4 => (3 : ℚ)).det = 81 := by
  rw [det_diagonal, Fin.prod_univ_four]
  norm_num

theorem cartan_blocks_detQ :
    (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℚ)).det = 27 := by
  rw [det_blockDiagonal, Fin.prod_univ_three, det_fin_two_of]
  norm_num

/-- `det A_D = 3^7 = 2187` over `ℤ` (manuscript line 3340). -/
theorem negMatrix_det : negMatrix.det = 2187 := by
  rw [negMatrix_blocks, det_fromBlocks_zero_int, diagonal_three_det, cartan_blocks_det]
  norm_num

/-- `det A_D = 3^7 = 2187` over `ℚ`. -/
theorem negMatrixQ_det : negMatrixQ.det = 2187 := by
  rw [negMatrixQ_blocks, det_fromBlocks_zero_rat, diagonal_three_detQ, cartan_blocks_detQ]
  norm_num

/-- The rational matrix is the entrywise cast of the integer matrix. -/
theorem negMatrixQ_eq_map : negMatrixQ = negMatrix.map (Int.cast : ℤ → ℚ) := by
  ext i j
  rcases i with i | ⟨a, k⟩ <;> rcases j with j | ⟨b, k'⟩
  · simp only [negMatrixQ, negMatrix, fromBlocks_apply₁₁, Matrix.map_apply, diagonal_apply]
    split_ifs <;> norm_num
  · simp [negMatrixQ, negMatrix]
  · simp [negMatrixQ, negMatrix]
  · simp only [negMatrixQ, negMatrix, fromBlocks_apply₂₂, Matrix.map_apply,
      blockDiagonal_apply]
    split_ifs
    · fin_cases a <;> fin_cases b <;> norm_num
    · norm_num

/-! ### The explicit inverse -/

theorem negMatrixQ_mul_inv : negMatrixQ * negMatrixInvQ = 1 := by
  have h2 : (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℚ) *
      (!![2 / 3, 1 / 3; 1 / 3, 2 / 3] : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    norm_num
  have h1 : (diagonal fun _ : Fin 4 => (3 : ℚ)) *
      (diagonal fun _ : Fin 4 => (1 / 3 : ℚ)) = 1 := by
    rw [diagonal_mul_diagonal]
    norm_num [diagonal_one]
  have h3 : (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) ℚ)) = 1 := rfl
  rw [negMatrixQ, negMatrixInvQ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, ← blockDiagonal_mul, h2]
  rw [h3, blockDiagonal_one, fromBlocks_one]

/-- The inverse of `A_D` is the displayed block matrix. -/
theorem negMatrixQ_inv : negMatrixQ⁻¹ = negMatrixInvQ :=
  Matrix.inv_eq_right_inv negMatrixQ_mul_inv

theorem negMatrixQ_isUnit : IsUnit negMatrixQ := by
  rw [Matrix.isUnit_iff_isUnit_det, negMatrixQ_det]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- The inverse is one third of the integer matrix `negMatrixInv3`. -/
theorem negMatrixInvQ_eq_smul :
    negMatrixInvQ = (1 / 3 : ℚ) • negMatrixInv3.map (Int.cast : ℤ → ℚ) := by
  ext i j
  rcases i with i | ⟨a, k⟩ <;> rcases j with j | ⟨b, k'⟩
  · simp only [negMatrixInvQ, negMatrixInv3, fromBlocks_apply₁₁, Matrix.smul_apply,
      Matrix.map_apply, diagonal_apply]
    split_ifs <;> norm_num
  · simp [negMatrixInvQ, negMatrixInv3]
  · simp [negMatrixInvQ, negMatrixInv3]
  · simp only [negMatrixInvQ, negMatrixInv3, fromBlocks_apply₂₂, Matrix.smul_apply,
      Matrix.map_apply, blockDiagonal_apply]
    split_ifs
    · fin_cases a <;> fin_cases b <;> norm_num
    · norm_num

/-! ### Quadratic values of the contact rows -/

theorem contactP_quadratic :
    ∀ i : Fin 3, contactP i ⬝ᵥ (negMatrixInv3 *ᵥ contactP i) = 4 := by decide

theorem contactT_quadratic :
    ∀ i : Fin 3, contactT i ⬝ᵥ (negMatrixInv3 *ᵥ contactT i) = 4 := by decide

theorem canonicalSource_quadratic :
    canonicalSource ⬝ᵥ (negMatrixInv3 *ᵥ canonicalSource) = 4 := by decide

theorem contactP_canonical_pairing :
    ∀ i : Fin 3, contactP i ⬝ᵥ (negMatrixInv3 *ᵥ canonicalSource) = 2 := by decide

theorem contactT_canonical_pairing :
    ∀ i : Fin 3, contactT i ⬝ᵥ (negMatrixInv3 *ᵥ canonicalSource) = 2 := by decide

/-- Casting an integer quadratic evaluation to `ℚ`. -/
theorem cast_bilinear {ι : Type*} [Fintype ι] (M : Matrix ι ι ℤ) (v w : ι → ℤ) :
    (fun i => (v i : ℚ)) ⬝ᵥ (M.map (Int.cast : ℤ → ℚ) *ᵥ fun i => (w i : ℚ)) =
      ((v ⬝ᵥ (M *ᵥ w) : ℤ) : ℚ) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Int.cast_sum, Int.cast_mul]

/-- The rational value of `xᵀ A_D⁻¹ y` is one third of the integer value. -/
theorem inv_bilinear_eq (x y : Index → ℤ) :
    (fun v => (x v : ℚ)) ⬝ᵥ (negMatrixQ⁻¹ *ᵥ fun v => (y v : ℚ)) =
      (1 / 3 : ℚ) * ((x ⬝ᵥ (negMatrixInv3 *ᵥ y) : ℤ) : ℚ) := by
  rw [negMatrixQ_inv, negMatrixInvQ_eq_smul, smul_mulVec_assoc, dotProduct_smul,
    cast_bilinear, smul_eq_mul]

/-- `pᵀ A_D⁻¹ p = 4/3` at every center `P_i` (manuscript line 3343). -/
theorem contactP_green (i : Fin 3) :
    contactPQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ contactPQ i) = 4 / 3 := by
  have h := inv_bilinear_eq (contactP i) (contactP i)
  rw [contactP_quadratic i] at h
  exact h.trans (by norm_num)

/-- `pᵀ A_D⁻¹ p = 4/3` at every center `T_i` (manuscript line 3343). -/
theorem contactT_green (i : Fin 3) :
    contactTQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ contactTQ i) = 4 / 3 := by
  have h := inv_bilinear_eq (contactT i) (contactT i)
  rw [contactT_quadratic i] at h
  exact h.trans (by norm_num)

/-- `qᵀ A_D⁻¹ q = 4/3` for the canonical source. -/
theorem canonicalSource_green :
    canonicalSourceQ ⬝ᵥ (negMatrixQ⁻¹ *ᵥ canonicalSourceQ) = 4 / 3 := by
  have h := inv_bilinear_eq canonicalSource canonicalSource
  rw [canonicalSource_quadratic] at h
  exact h.trans (by norm_num)

/-- Numerical content of `ℓ = L^2 = 1/3` (line 3340) under the formula
`L^2 = K_S^2 + qᵀ A_D⁻¹ q` (line 468) with `K_S^2 = -1` (line 3339). -/
theorem anticanonical_square_value :
    (-1 : ℚ) + canonicalSourceQ ⬝ᵥ (negMatrixQ⁻¹ *ᵥ canonicalSourceQ) = 1 / 3 := by
  rw [canonicalSource_green]
  norm_num

/-- `pᵀ A_D⁻¹ q = 2/3` at every center `P_i`. -/
theorem contactP_charge (i : Fin 3) :
    contactPQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ canonicalSourceQ) = 2 / 3 := by
  have h := inv_bilinear_eq (contactP i) canonicalSource
  rw [contactP_canonical_pairing i] at h
  exact h.trans (by norm_num)

/-- `pᵀ A_D⁻¹ q = 2/3` at every center `T_i`. -/
theorem contactT_charge (i : Fin 3) :
    contactTQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ canonicalSourceQ) = 2 / 3 := by
  have h := inv_bilinear_eq (contactT i) canonicalSource
  rw [contactT_canonical_pairing i] at h
  exact h.trans (by norm_num)

/-- Numerical content of `L·P = 1/3` (the case `r = 1` of line 3221) under
`pᵀ A_D⁻¹ q = 1 - L·P` (lines 617–620). -/
theorem degree_value (i : Fin 3) :
    1 - contactPQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ canonicalSourceQ) = 1 / 3 ∧
      1 - contactTQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ canonicalSourceQ) = 1 / 3 := by
  rw [contactP_charge, contactT_charge]
  norm_num

/-- Consistency of the three values with `pᵀA⁻¹p = 1 + (L·P)^2 / L^2`
(lines 612–616): `1 + (1/3)^2 / (1/3) = 4/3`. -/
theorem green_projection_check : (1 : ℚ) + (1 / 3) ^ 2 / (1 / 3) = 4 / 3 := by norm_num

/-! ### The bordered Gram matrix -/

/-- Signed bordered determinant at `P_i`, with `P^2 = -1` (line 3344). -/
theorem borderedGram_contactP_det (i : Fin 3) :
    (borderedGram negMatrixQ (contactPQ i) (-1)).det = 729 := by
  rw [det_minusOne_borderedGram_rat negMatrixQ_isUnit, card_index, negMatrixQ_det, contactP_green]
  norm_num

/-- Signed bordered determinant at `T_i`, with `P^2 = -1` (line 3344). -/
theorem borderedGram_contactT_det (i : Fin 3) :
    (borderedGram negMatrixQ (contactTQ i) (-1)).det = 729 := by
  rw [det_minusOne_borderedGram_rat negMatrixQ_isUnit, card_index, negMatrixQ_det, contactT_green]
  norm_num

/-- `|det ⟨D,P⟩| = 3^6 = 729` at every shortest center (line 3344). -/
theorem borderedGram_contact_absDet (p : Index → ℚ)
    (hp : (∃ i, p = contactPQ i) ∨ (∃ i, p = contactTQ i)) :
    |(borderedGram negMatrixQ p (-1)).det| = 729 := by
  rcases hp with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [borderedGram_contactP_det]
    norm_num
  · rw [borderedGram_contactT_det]
    norm_num

/-! ### Decimal disambiguation -/

theorem three_pow_seven : (3 : ℤ) ^ 7 = 2187 := by norm_num

theorem three_pow_seven_ne_37 : (3 : ℤ) ^ 7 ≠ 37 := by norm_num

theorem three_pow_six : (3 : ℤ) ^ 6 = 729 := by norm_num

theorem three_pow_six_ne_36 : (3 : ℤ) ^ 6 ≠ 36 := by norm_num

theorem sqrt_729 : (27 : ℕ) ^ 2 = 729 := by norm_num

/-! ### The index `27`, conditional on an actual unimodular lattice

Unifying `(BilinForm.toMatrix b B).det.natAbs = 1` at the concrete eleven-element
index type exceeds the elaborator's recursion limit, so unimodularity and the
Gram identification are packaged as predicates that are definitionally the
accepted statements (`isUnimodular_iff`, `sublatticeGramIs_iff` are `Iff.rfl`),
and the lattice arithmetic is done once over an abstract index type. -/

/-- Unimodularity of the ambient integral form, definitionally the accepted
`(BilinForm.toMatrix b B).det.natAbs = 1`. -/
def IsUnimodular {Λ ι : Type*} [AddCommGroup Λ] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Λ) (B : BilinForm ℤ Λ) : Prop :=
  (BilinForm.toMatrix b B).det.natAbs = 1

theorem isUnimodular_iff {Λ ι : Type*} [AddCommGroup Λ] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Λ) (B : BilinForm ℤ Λ) :
    IsUnimodular b B ↔ (BilinForm.toMatrix b B).det.natAbs = 1 := Iff.rfl

/-- The rational cast of the Gram matrix of the restricted form on a
sublattice basis is a given rational matrix; definitionally the accepted
`(BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).map (fun z => (z : ℚ)) = R`. -/
def SublatticeGramIs {M ι : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
    (B : BilinForm ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N) (R : Matrix ι ι ℚ) :
    Prop :=
  (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).map (fun z => (z : ℚ)) = R

theorem sublatticeGramIs_iff {M ι : Type*} [AddCommGroup M] [Fintype ι] [DecidableEq ι]
    (B : BilinForm ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N) (R : Matrix ι ι ℚ) :
    SublatticeGramIs B N bN R ↔
      (BilinForm.toMatrix bN (B.comp N.subtype N.subtype)).map (fun z => (z : ℚ)) = R :=
  Iff.rfl

/-- Abstract index step: a family with Gram determinant of absolute value `729`
in a unimodular lattice is independent and spans a sublattice of index `27`,
by the accepted `span_index_sq_of_gram_det` and `27 ^ 2 = 729`. -/
theorem span_index_eq_27_of_natAbs_det {Λ ι : Type*} [AddCommGroup Λ]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ Λ) (pairing : BilinForm ℤ Λ) (hunimod : IsUnimodular b pairing)
    (v : ι → Λ) (hd : (familyGram pairing v).det.natAbs = 729) :
    LinearIndependent ℤ v ∧
      (Submodule.span ℤ (Set.range v)).toAddSubgroup.index = 27 := by
  obtain ⟨hind, hsq⟩ := span_index_sq_of_gram_det b pairing hunimod v
    (by norm_num : (729 : ℕ) ≠ 0) hd
  refine ⟨hind, ?_⟩
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  exact hsq.trans (by norm_num)

/-- Abstract sublattice step through the accepted
`natAbs_det_gram_restriction_of_unimodular`. -/
theorem sublattice_index_eq_27_of_absDet {M ι : Type*} [AddCommGroup M]
    [Fintype ι] [DecidableEq ι]
    (B : BilinForm ℤ M) (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N)
    (hunimod : IsUnimodular b B) (R : Matrix ι ι ℚ) (hGram : SublatticeGramIs B N bN R)
    (habs : |R.det| = 729) : N.toAddSubgroup.index = 27 := by
  have habs' : |R.det| = ((729 : ℕ) : ℚ) := by
    rw [habs]
    norm_num
  have hd := natAbs_det_of_rational_matrix hGram habs'
  rw [natAbs_det_gram_restriction_of_unimodular B b N bN hunimod] at hd
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  exact hd.trans (by norm_num)

/-- If an actual unimodular integral lattice with a basis indexed by
`Index ⊕ Unit` contains a family whose Gram matrix is the bordered matrix at
a shortest center, that family is independent and its span has index `27`
(line 3345). No lattice is constructed here. -/
theorem span_index_eq_27 {Λ : Type*} [AddCommGroup Λ]
    (b : Basis (Index ⊕ Unit) ℤ Λ) (pairing : BilinForm ℤ Λ)
    (hunimod : IsUnimodular b pairing)
    (classes : Index → Λ) (P : Λ) (p : Index → ℚ)
    (hp : (∃ i, p = contactPQ i) ∨ (∃ i, p = contactTQ i))
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram negMatrixQ p (-1)) :
    LinearIndependent ℤ (Sum.elim classes (fun _ : Unit => P)) ∧
      (Submodule.span ℤ (Set.range (Sum.elim classes (fun _ : Unit => P)))).toAddSubgroup.index
        = 27 := by
  have habs : |(borderedGram negMatrixQ p (-1)).det| = ((729 : ℕ) : ℚ) := by
    rw [borderedGram_contact_absDet p hp]
    norm_num
  exact span_index_eq_27_of_natAbs_det b pairing hunimod _
    (natAbs_det_of_rational_matrix hGram habs)

/-- The same conclusion for an actual full-rank sublattice with its own basis
(line 3345), through the accepted index-square relation of `IndexDeterminant`. -/
theorem sublattice_index_eq_27 {M : Type*} [AddCommGroup M]
    (B : BilinForm ℤ M) (b : Basis (Index ⊕ Unit) ℤ M)
    (N : Submodule ℤ M) (bN : Basis (Index ⊕ Unit) ℤ N)
    (hunimod : IsUnimodular b B) (p : Index → ℚ)
    (hp : (∃ i, p = contactPQ i) ∨ (∃ i, p = contactTQ i))
    (hGram : SublatticeGramIs B N bN (borderedGram negMatrixQ p (-1))) :
    N.toAddSubgroup.index = 27 :=
  sublattice_index_eq_27_of_absDet B b N bN hunimod _ hGram (borderedGram_contact_absDet p hp)

/-! ### The graph read off the matrix -/

/-- Adjacency is a nonzero off-diagonal entry. -/
def dualGraph : SimpleGraph Index where
  Adj i j := i ≠ j ∧ negMatrix i j ≠ 0
  symm := by
    intro i j h
    exact ⟨h.1.symm, by rw [negMatrix_symm]; exact h.2⟩
  loopless := fun i h => h.1 rfl

instance dualGraph_instDecidableRelAdj : DecidableRel dualGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ negMatrix i j ≠ 0))

/-- `negMatrixQ` is the accepted weighted graph matrix of `dualGraph`. -/
theorem graphWeightMatrix_dualGraph :
    graphWeightMatrix dualGraph (fun v => (weight v : ℚ)) = negMatrixQ := by
  ext i j
  rw [graphWeightMatrix_apply, negMatrixQ_eq_map, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, negMatrix_diag]
    simp
  · rw [if_neg hij]
    by_cases hadj : dualGraph.Adj i j
    · rw [if_pos hadj]
      rcases negMatrix_offDiag i j hij with h | h
      · exact absurd h hadj.2
      · rw [h]
        norm_num
    · rw [if_neg hadj]
      have h0 : negMatrix i j = 0 := by
        by_contra h
        exact hadj ⟨hij, h⟩
      rw [h0]
      simp

theorem dualGraph_degree_sum : ∑ v, dualGraph.degree v = 6 := by
  have h : ∀ v : Index, dualGraph.degree v =
      ((Finset.univ : Finset Index).filter fun w => v ≠ w ∧ negMatrix v w ≠ 0).card := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    rfl
  simp only [h]
  decide

/-- Three edges (manuscript line 3340). -/
theorem dualGraph_card_edgeFinset : dualGraph.edgeFinset.card = 3 := by
  have h := dualGraph.sum_degrees_eq_twice_card_edges
  rw [dualGraph_degree_sum] at h
  omega

/-- The block of a component: its `Fin 4` label or its chain index. -/
def blockOf : Index → Fin 4 ⊕ Fin 3 := Sum.map id Prod.snd

theorem blockOf_of_adj : ∀ i j : Index, dualGraph.Adj i j → blockOf i = blockOf j := by
  decide

theorem eq_or_adj_of_blockOf :
    ∀ i j : Index, blockOf i = blockOf j → i = j ∨ dualGraph.Adj i j := by
  decide

theorem blockOf_surjective : Function.Surjective blockOf := by
  intro b
  rcases b with b | b
  · exact ⟨Sum.inl b, rfl⟩
  · exact ⟨Sum.inr (0, b), rfl⟩

theorem blockOf_of_reachable {i j : Index} (h : dualGraph.Reachable i j) :
    blockOf i = blockOf j := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (blockOf_of_adj _ _ hadj).trans ih

/-- The block label descends to connected components. -/
def componentBlock : dualGraph.ConnectedComponent → Fin 4 ⊕ Fin 3 :=
  SimpleGraph.ConnectedComponent.lift blockOf (fun _ _ p _ => blockOf_of_reachable ⟨p⟩)

theorem componentBlock_bijective : Function.Bijective componentBlock := by
  constructor
  · intro c c'
    refine SimpleGraph.ConnectedComponent.ind₂ (fun v w => ?_) c c'
    intro h
    simp only [componentBlock, SimpleGraph.ConnectedComponent.lift_mk] at h
    apply SimpleGraph.ConnectedComponent.sound
    rcases eq_or_adj_of_blockOf v w h with rfl | hadj
    · rfl
    · exact hadj.reachable
  · intro b
    obtain ⟨v, rfl⟩ := blockOf_surjective b
    exact ⟨dualGraph.connectedComponentMk v, rfl⟩

/-- Seven connected components (manuscript line 3360). -/
theorem card_connectedComponent : Nat.card dualGraph.ConnectedComponent = 7 := by
  rw [Nat.card_eq_of_bijective _ componentBlock_bijective, Nat.card_eq_fintype_card]
  simp

end EqualityNumbers

open EqualityNumbers

/-- **U-EQUALITY-NUMBERS.** The unconditional numerical clauses of manuscript
`cor:equality-lattice` (lines 3336–3361) for the explicit matrix `negMatrix`:
ten components, the four-`[3]`-three-`A_2` block structure, `det = 3^7 = 2187`
(not `37`), three edges and seven components of the graph read off the matrix
(`10 - 3 = 7`), no isolated weight-two component, `pᵀA_D⁻¹p = 4/3` at all six
shortest contact rows, `|det ⟨D,P⟩| = 3^6 = 729` (not `36`), and `27^2 = 729`.
The index `27` is `span_index_eq_27` / `sublattice_index_eq_27`, conditional
on an actual unimodular lattice. No geometric realization is claimed. -/
theorem u_equality_numbers :
    Fintype.card Index = 10 ∧
    negMatrix = fromBlocks (diagonal fun _ : Fin 4 => (3 : ℤ)) 0 0
      (blockDiagonal fun _ : Fin 3 => (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℤ)) ∧
    negMatrix.det = 3 ^ 7 ∧ negMatrixQ.det = 3 ^ 7 ∧
    (3 : ℤ) ^ 7 = 2187 ∧ (3 : ℤ) ^ 7 ≠ 37 ∧
    dualGraph.edgeFinset.card = 3 ∧
    Nat.card dualGraph.ConnectedComponent = 7 ∧ (10 : ℕ) - 3 = 7 ∧
    (∀ i : Index, negMatrix i i = 2 → ∃ j, j ≠ i ∧ negMatrix i j ≠ 0) ∧
    (∀ i : Fin 3, contactPQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ contactPQ i) = 4 / 3) ∧
    (∀ i : Fin 3, contactTQ i ⬝ᵥ (negMatrixQ⁻¹ *ᵥ contactTQ i) = 4 / 3) ∧
    (∀ i : Fin 3, |(borderedGram negMatrixQ (contactPQ i) (-1)).det| = 3 ^ 6) ∧
    (∀ i : Fin 3, |(borderedGram negMatrixQ (contactTQ i) (-1)).det| = 3 ^ 6) ∧
    (3 : ℤ) ^ 6 = 729 ∧ (3 : ℤ) ^ 6 ≠ 36 ∧ (27 : ℕ) ^ 2 = 729 := by
  refine ⟨card_index, negMatrix_blocks, ?_, ?_, three_pow_seven, three_pow_seven_ne_37,
    dualGraph_card_edgeFinset, card_connectedComponent, ten_sub_three,
    negMatrix_no_isolated_node, contactP_green, contactT_green, ?_, ?_,
    three_pow_six, three_pow_six_ne_36, sqrt_729⟩
  · rw [negMatrix_det]
    norm_num
  · rw [negMatrixQ_det]
    norm_num
  · intro i
    rw [borderedGram_contact_absDet _ (Or.inl ⟨i, rfl⟩)]
    norm_num
  · intro i
    rw [borderedGram_contact_absDet _ (Or.inr ⟨i, rfl⟩)]
    norm_num

end KltDP.Support
