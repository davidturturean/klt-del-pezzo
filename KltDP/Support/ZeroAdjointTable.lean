import KltDP.Lattices.SmallADEPartitions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The zero-adjoint square table

Support obligation U-ZERO-ADJOINT-TABLE for the proof of manuscript
`prop:zero-adjoint` (`source/manuscript.tex`, lines 1498–1540). This module is
a wrapper over the accepted arithmetic of `KltDP.Lattices.SmallADEPartitions`
together with the two explicit computations the proof displays: the `4 × 4`
core determinant and the positivity condition on `β`. No surface, divisor,
Picard group, intersection form or lattice is constructed or assumed.

Coverage of lines 1498–1540, sentence by sentence:
* "Every other exceptional component `A` satisfies `0 ≤ K_S·A ≤ 0`; hence
  `A² = -2` and it is disjoint from all four displayed curves" (lines
  1499–1504): **open** geometric clause, not covered here.
* "The three displayed exceptional components are isolated, with
  discrepancies `0, 1/3, (β-2)/β`" (lines 1505–1506): **open**.
* "Since `L·P = (6-β)/(3β) > 0`, one has `β = 3, 4, 5`" (lines 1506–1507):
  the identity `L·P = (6-β)/(3β)` is **open**; its consequence is
  `ell_pos_iff` (`0 < (6-β)/(3β) ↔ β < 6` for integers `β ≥ 3`) and
  `beta_eq_three_four_five`.
* "Also `K_S² = 3-β`, so `ρ(S) = β+7`" (line 1508): **open**; the bookkeeping
  `4 + (β+3) = β+7` is `picard_rank_split`.
* "The remaining exceptional curves form an ADE forest `F` of rank `β+3`
  with at least five connected components" (lines 1509–1510): **open** as a
  geometric statement; it is the hypothesis `c.rank = β + 3 ∧ 5 ≤ c.components`
  of the table theorems, with `F` recorded by its multiplicities
  `c : Counts` of `A₁, A₂, A₃, A₄, D₄`.
* "`|det Γ| = (6-β) det F`, since the matrix of its four-curve summand is
  `[[-2,0,0,1],[0,-3,0,1],[0,0,-β,1],[1,1,1,-1]]`, `det = β-6`" (lines
  1511–1519; the formula is line 1514, the matrix lines 1518–1519):
  `coreMatrix`, `coreMatrix_det : det = β - 6`,
  `coreMatrix_det_abs : |det| = 6 - β` and `coreMatrix_det_natAbs` for
  `3 ≤ β ≤ 5`; `gammaDet β c := (6 - β) * c.rootDet` is the manuscript's
  right-hand side by definition (`gammaDet_eq`). The identification of
  `gammaDet` with the determinant of an actual lattice `Γ` is **open**.
* "Unimodularity requires `|det Γ|` to be a square" (line 1521): **open**;
  the square condition is the hypothesis `gammaDet β c = I ^ 2`.
* "The possible rank partitions of `F` with at least five parts have largest
  part at most four. Using the determinants `2,3,4,5,4` of `A₁,…,D₄` leaves
  exactly the following rows" (lines 1522–1534): `gammaDet_square_iff`
  (the accepted `mem_betaSquareRows_iff`), `tableRows_project_eq`
  (the six displayed rows are exactly `betaSquareRows`), `tableRows_valid`
  (each row's `β`, `I`, `v₂(I)`, `t`, rank and component count as displayed).
* "Every listed `A₁` is an isolated exceptional node and is an orthogonal
  summand of `Γ`" (lines 1537–1538): **open**.
* "Every row has `t > v₂(I)`" (line 1538): `tableRows_valid` (row by row) and
  `gammaDet_square_factorization_lt_nodes` (the accepted
  `beta_square_factorization_lt_nodes`, for every `c`).
* "contradicting `lem:picard-index`, `thm:no-even-nodes`" (lines 1538–1539):
  **open**.
* `u_zero_adjoint_table` bundles the proved clauses.

Reuse: `Counts`, `rank`, `components`, `rootDet`, `betaSquareRows`,
`mem_betaSquareRows_iff`, `beta_square_factorization_lt_nodes` are the
accepted declarations; the pinned Mathlib Laplace expansion
`det_succ_row_zero`, `div_pos_iff`, and the factorization lemmas supply the
rest. The three two-adic valuations are re-proved locally because the
accepted versions are private.
-/

namespace KltDP.Support

open Matrix KltDP.Lattices.SmallADEPartitions
open scoped BigOperators

namespace ZeroAdjointTable

/-! ### The four-curve core -/

/-- The intersection matrix of `⟨C, B₁, B₂, P⟩` (manuscript lines 1516–1518). -/
def coreMatrix (beta : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-2, 0, 0, 1; 0, -3, 0, 1; 0, 0, -beta, 1; 1, 1, 1, -1]

/-- `det = β - 6` (manuscript line 1519), by Laplace expansion. -/
theorem coreMatrix_det (beta : ℤ) : (coreMatrix beta).det = beta - 6 := by
  simp only [coreMatrix, det_succ_row_zero, submatrix_apply, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.sum_univ_succ,
    Fin.val_zero, Fin.val_succ, Fin.zero_succAbove, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_succ, Finset.univ_unique, Finset.sum_singleton, Fin.val_eq_zero,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-- For `3 ≤ β ≤ 5` the core determinant is negative with absolute value `6 - β`. -/
theorem coreMatrix_det_abs (beta : ℤ) (h3 : 3 ≤ beta) (h5 : beta ≤ 5) :
    |(coreMatrix beta).det| = 6 - beta := by
  rw [coreMatrix_det, abs_of_neg (by omega)]
  ring

/-- The natural absolute value, matching the natural-number arithmetic of `gammaDet`. -/
theorem coreMatrix_det_natAbs (beta : ℕ) (h5 : beta ≤ 5) :
    ((coreMatrix beta).det).natAbs = 6 - beta := by
  rw [coreMatrix_det]
  omega

/-! ### Positivity of `(6 - β) / (3β)` -/

/-- `0 < (6-β)/(3β) ↔ β < 6` for integers `β ≥ 3` (manuscript lines 1506–1507);
the identification of the left side with `L·P` is not claimed. -/
theorem ell_pos_iff (beta : ℤ) (h3 : 3 ≤ beta) :
    (0 : ℚ) < (6 - (beta : ℚ)) / (3 * (beta : ℚ)) ↔ beta < 6 := by
  have hb : (3 : ℚ) ≤ (beta : ℚ) := by exact_mod_cast h3
  rw [div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · have : (beta : ℚ) < 6 := by linarith
      exact_mod_cast this
    · linarith
  · intro h
    have h' : (beta : ℚ) < 6 := by exact_mod_cast h
    exact Or.inl ⟨by linarith, by linarith⟩

/-- Hence `β ∈ {3, 4, 5}` (manuscript line 1507). -/
theorem beta_eq_three_four_five (beta : ℤ) (h3 : 3 ≤ beta) (h6 : beta < 6) :
    beta = 3 ∨ beta = 4 ∨ beta = 5 := by
  omega

/-- The natural-number form of the same trichotomy. -/
theorem beta_eq_three_four_five_nat (beta : ℕ) (h3 : 3 ≤ beta) (h6 : beta < 6) :
    beta = 3 ∨ beta = 4 ∨ beta = 5 := by
  omega

/-- Bookkeeping for "`ρ(S) = β + 7`, `F` of rank `β + 3`" (lines 1508–1509):
the four core curves and the forest fill the Picard rank. -/
theorem picard_rank_split (beta : ℕ) : 4 + (beta + 3) = beta + 7 := by
  omega

/-! ### The determinant `(6 - β) det F` and the square table -/

/-- The manuscript's `|det Γ| = (6-β) det F` as a natural number
(line 1514); its identification with an actual lattice determinant is open. -/
def gammaDet (beta : ℕ) (c : Counts) : ℕ := (6 - beta) * c.rootDet

theorem gammaDet_eq (beta : ℕ) (c : Counts) : gammaDet beta c = (6 - beta) * c.rootDet :=
  rfl

/-- The core factor of `gammaDet` is the absolute core determinant. -/
theorem gammaDet_eq_natAbs_mul (beta : ℕ) (h5 : beta ≤ 5) (c : Counts) :
    gammaDet beta c = ((coreMatrix beta).det).natAbs * c.rootDet := by
  rw [gammaDet_eq, coreMatrix_det_natAbs beta h5]

/-- Under the stated rank and component hypotheses, `gammaDet β c` is a square
`I ^ 2` exactly for the six accepted rows (lines 1522–1534). -/
theorem gammaDet_square_iff (beta I : ℕ) (c : Counts)
    (h3 : 3 ≤ beta) (h5 : beta ≤ 5) (hrank : c.rank = beta + 3) (hcomp : 5 ≤ c.components) :
    gammaDet beta c = I ^ 2 ↔ (beta, I, c) ∈ betaSquareRows := by
  rw [mem_betaSquareRows_iff]
  constructor
  · intro h
    exact ⟨h3, h5, hrank, hcomp, h⟩
  · rintro ⟨_, _, _, _, h⟩
    exact h

/-- Every square row has `t > v₂(I)` (line 1538), from the accepted
`beta_square_factorization_lt_nodes`. -/
theorem gammaDet_square_factorization_lt_nodes (beta I : ℕ) (c : Counts)
    (h3 : 3 ≤ beta) (h5 : beta ≤ 5) (hrank : c.rank = beta + 3) (hcomp : 5 ≤ c.components)
    (hsquare : gammaDet beta c = I ^ 2) : I.factorization 2 < c.a1 :=
  beta_square_factorization_lt_nodes c beta I h3 h5 hrank hcomp hsquare

/-! ### The displayed six rows -/

/-- One row of the table at lines 1529–1534: `β`, the forest `F` by its
multiplicities `⟨a₁, a₂, a₃, a₄, d₄⟩`, `I = √|det Γ|`, `v₂(I)`, `t = #A₁`. -/
structure Row where
  beta : ℕ
  counts : Counts
  index : ℕ
  twoAdic : ℕ
  nodes : ℕ
  deriving DecidableEq

/-- The six rows in manuscript order: `A₂+4A₁`, `7A₁`, `2A₂+3A₁`, `8A₁`,
`2A₂+4A₁`, `D₄+4A₁`. -/
def tableRows : List Row :=
  [⟨3, ⟨4, 1, 0, 0, 0⟩, 12, 2, 4⟩, ⟨4, ⟨7, 0, 0, 0, 0⟩, 16, 4, 7⟩,
   ⟨4, ⟨3, 2, 0, 0, 0⟩, 12, 2, 3⟩, ⟨5, ⟨8, 0, 0, 0, 0⟩, 16, 4, 8⟩,
   ⟨5, ⟨4, 2, 0, 0, 0⟩, 12, 2, 4⟩, ⟨5, ⟨4, 0, 0, 0, 1⟩, 8, 3, 4⟩]

/-- The `(β, I, F)` projections of the displayed rows are exactly the accepted
`betaSquareRows`. -/
theorem tableRows_project_eq :
    (tableRows.map fun r => (r.beta, r.index, r.counts)).toFinset = betaSquareRows := by
  decide

/-- The decidable clauses of every row: `t = #A₁`, rank `β + 3`, at least five
components, `(6-β) det F = I²`, `v₂ < t`, and membership in the accepted table. -/
theorem tableRows_decidable_valid : ∀ r ∈ tableRows,
    r.nodes = r.counts.a1 ∧ r.counts.rank = r.beta + 3 ∧ 5 ≤ r.counts.components ∧
      gammaDet r.beta r.counts = r.index ^ 2 ∧ r.twoAdic < r.nodes ∧
      (r.beta, r.index, r.counts) ∈ betaSquareRows := by
  decide

theorem factorization_eight : (8 : ℕ).factorization 2 = 3 := by
  change (2 ^ 3 : ℕ).factorization 2 = 3
  rw [Nat.prime_two.factorization_pow]
  simp

theorem factorization_twelve : (12 : ℕ).factorization 2 = 2 := by
  change (2 ^ 2 * 3 : ℕ).factorization 2 = 2
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ^ 2 ≠ 0) (by decide : (3 : ℕ) ≠ 0),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  simp

theorem factorization_sixteen : (16 : ℕ).factorization 2 = 4 := by
  change (2 ^ 4 : ℕ).factorization 2 = 4
  rw [Nat.prime_two.factorization_pow]
  simp

/-- The displayed `v₂(I)` column is the two-adic valuation of the index column. -/
theorem tableRows_twoAdic : ∀ r ∈ tableRows, r.index.factorization 2 = r.twoAdic := by
  intro r hr
  simp only [tableRows, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [factorization_eight, factorization_twelve, factorization_sixteen]

/-- All displayed columns of every row are correct: `I = 12,16,12,16,12,8`,
`v₂(I) = 2,4,2,4,2,3`, `t = 4,7,3,8,4,4`, and `t > v₂(I)`. -/
theorem tableRows_valid : ∀ r ∈ tableRows,
    r.nodes = r.counts.a1 ∧ r.counts.rank = r.beta + 3 ∧ 5 ≤ r.counts.components ∧
      gammaDet r.beta r.counts = r.index ^ 2 ∧ r.index.factorization 2 = r.twoAdic ∧
      r.twoAdic < r.nodes ∧ (r.beta, r.index, r.counts) ∈ betaSquareRows := by
  intro r hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := tableRows_decidable_valid r hr
  exact ⟨h1, h2, h3, h4, tableRows_twoAdic r hr, h5, h6⟩

/-- The three index values with their valuations and node counts, as
`(I, v₂(I), t)` triples. -/
theorem tableRows_columns :
    tableRows.map (fun r => (r.index, r.twoAdic, r.nodes)) =
      [(12, 2, 4), (16, 4, 7), (12, 2, 3), (16, 4, 8), (12, 2, 4), (8, 3, 4)] := by
  decide

end ZeroAdjointTable

open ZeroAdjointTable

/-- **U-ZERO-ADJOINT-TABLE.** The arithmetic clauses of the proof of
`prop:zero-adjoint` (lines 1498–1540): the core determinant `β - 6` and its
absolute value `6 - β`; `0 < (6-β)/(3β) ↔ β < 6`, hence `β ∈ {3,4,5}`; for
`β ∈ {3,4,5}`, a forest of rank `β + 3` with at least five components has
`(6-β) det F` a square `I²` exactly for the six accepted rows; those rows are
the six displayed rows with `I = 12,16,12,16,12,8`, `v₂(I) = 2,4,2,4,2,3`,
`t = 4,7,3,8,4,4`; and every square row has `t > v₂(I)`. The geometric
clauses listed in the module header remain open. -/
theorem u_zero_adjoint_table :
    (∀ beta : ℤ, (coreMatrix beta).det = beta - 6) ∧
    (∀ beta : ℤ, 3 ≤ beta → beta ≤ 5 → |(coreMatrix beta).det| = 6 - beta) ∧
    (∀ beta : ℤ, 3 ≤ beta →
      ((0 : ℚ) < (6 - (beta : ℚ)) / (3 * (beta : ℚ)) ↔ beta < 6)) ∧
    (∀ beta : ℤ, 3 ≤ beta → beta < 6 → beta = 3 ∨ beta = 4 ∨ beta = 5) ∧
    (∀ (beta I : ℕ) (c : Counts), 3 ≤ beta → beta ≤ 5 → c.rank = beta + 3 →
      5 ≤ c.components → (gammaDet beta c = I ^ 2 ↔ (beta, I, c) ∈ betaSquareRows)) ∧
    (tableRows.map fun r => (r.beta, r.index, r.counts)).toFinset = betaSquareRows ∧
    (∀ r ∈ tableRows,
      r.nodes = r.counts.a1 ∧ r.counts.rank = r.beta + 3 ∧ 5 ≤ r.counts.components ∧
        gammaDet r.beta r.counts = r.index ^ 2 ∧ r.index.factorization 2 = r.twoAdic ∧
        r.twoAdic < r.nodes ∧ (r.beta, r.index, r.counts) ∈ betaSquareRows) ∧
    tableRows.map (fun r => (r.index, r.twoAdic, r.nodes)) =
      [(12, 2, 4), (16, 4, 7), (12, 2, 3), (16, 4, 8), (12, 2, 4), (8, 3, 4)] ∧
    (∀ (beta I : ℕ) (c : Counts), 3 ≤ beta → beta ≤ 5 → c.rank = beta + 3 →
      5 ≤ c.components → gammaDet beta c = I ^ 2 → I.factorization 2 < c.a1) :=
  ⟨coreMatrix_det, coreMatrix_det_abs, ell_pos_iff, beta_eq_three_four_five,
    gammaDet_square_iff, tableRows_project_eq, tableRows_valid, tableRows_columns,
    gammaDet_square_factorization_lt_nodes⟩

end KltDP.Support
