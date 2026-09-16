import KltDP.LinearAlgebra.NegativeGramDimension
import KltDP.LinearAlgebra.RootedTreePositiveDefinite
import KltDP.LinearAlgebra.Stieltjes

/-!
# Actual orthogonal copies of a negative family

The negative Gram matrix of two actual mutually orthogonal families is
their block diagonal matrix. Positive definiteness of the two original
blocks proves positive definiteness of the union, its linear independence,
and its span dimension. An actual positive ambient vector then gives a
strict bound on the number of vectors in the doubled family.

This is the bilinear assembly needed for the two disjoint lifted copies in
the no-even-node argument. It does not construct those copies, a cover,
intersection products, an ample class or the geometric Picard-rank formula.
Neither positive definiteness of the doubled matrix nor independence nor
its dimension bound is assumed.

Reuse: pinned Mathlib's matrix blocks and finite-dimensional span formulas,
the project's strict Schur positivity adapter, and NegativeGramDimension.
The current official Mathlib PosDef source was also inspected; its updated
interfaces require no port for this assembly. All dependencies stay pinned.
-/

namespace KltDP.LinearAlgebra

open Matrix CanonicalCorrection Module Submodule

section Pairing

variable {R V ι κ : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The actual cross-pairings vanish in both orders, so the negative Gram
matrix of the union of the two families is their actual block diagonal. -/
theorem negativeGram_sum_eq_fromBlocks (B : LinearMap.BilinForm R V)
    (v : ι → V) (w : κ → V)
    (hvw : ∀ i j, B (v i) (w j) = 0) (hwv : ∀ j i, B (w j) (v i) = 0) :
    negativeGram B (Sum.elim v w) =
      Matrix.fromBlocks (negativeGram B v) 0 0 (negativeGram B w) := by
  ext i j
  cases i <;> cases j <;> simp [negativeGram, hvw, hwv]

end Pairing

section Rational

variable {V ι κ : Type*} [AddCommGroup V] [Module ℚ V]
  [Fintype ι] [Fintype κ]

/-- Strict positivity of the actual two diagonal blocks implies strict
positivity of their block diagonal, including empty index types. -/
theorem posDef_fromBlocks_zero (A : Matrix ι ι ℚ) (D : Matrix κ κ ℚ)
    (hA : A.PosDef) (hD : D.PosDef) : (Matrix.fromBlocks A 0 0 D).PosDef := by
  classical
  letI : Invertible D := (isUnit_of_posDef hD).invertible
  have h := posDef_fromBlocks_of_schur A (0 : Matrix ι κ ℚ) hD
    (by simpa only [Matrix.zero_mul, sub_zero] using hA)
  simpa only [Matrix.conjTranspose_zero] using h

/-- Positive definiteness of the two actual negative Gram matrices and
actual mutual orthogonality prove it for their union. -/
theorem orthogonal_sum_negativeGram_posDef (B : LinearMap.BilinForm ℚ V)
    (v : ι → V) (w : κ → V)
    (hv : (negativeGram B v).PosDef) (hw : (negativeGram B w).PosDef)
    (hvw : ∀ i j, B (v i) (w j) = 0) (hwv : ∀ j i, B (w j) (v i) = 0) :
    (negativeGram B (Sum.elim v w)).PosDef := by
  rw [negativeGram_sum_eq_fromBlocks B v w hvw hwv]
  exact posDef_fromBlocks_zero _ _ hv hw

/-- The union is linearly independent; no independence of either copy or
of their union has to be supplied separately. -/
theorem orthogonal_sum_linearIndependent (B : LinearMap.BilinForm ℚ V)
    (v : ι → V) (w : κ → V)
    (hv : (negativeGram B v).PosDef) (hw : (negativeGram B w).PosDef)
    (hvw : ∀ i j, B (v i) (w j) = 0) (hwv : ∀ j i, B (w j) (v i) = 0) :
    LinearIndependent ℚ (Sum.elim v w) :=
  negativeGram_posDef_linearIndependent B (Sum.elim v w)
    (orthogonal_sum_negativeGram_posDef B v w hv hw hvw hwv)

omit [Fintype κ] in
/-- Two actual copies of the same negative Gram matrix span exactly twice
the number of original vectors. The ambient space need not be finite dimensional. -/
theorem orthogonal_copies_span_finrank (B : LinearMap.BilinForm ℚ V)
    (A : Matrix ι ι ℚ) (hA : A.PosDef) (left right : ι → V)
    (hleft : negativeGram B left = A) (hright : negativeGram B right = A)
    (hlr : ∀ i j, B (left i) (right j) = 0)
    (hrl : ∀ j i, B (right j) (left i) = 0) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (Sum.elim left right))) =
      2 * Fintype.card ι := by
  have hli := orthogonal_sum_linearIndependent B left right
    (hleft.symm ▸ hA) (hright.symm ▸ hA) hlr hrl
  rw [finrank_span_eq_card hli, Fintype.card_sum, two_mul]

omit [Fintype κ] in
/-- The actual two orthogonal copies have strictly fewer vectors than the
ambient dimension whenever there is a vector with positive square. -/
theorem orthogonal_copies_card_lt_finrank [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (A : Matrix ι ι ℚ) (hA : A.PosDef)
    (left right : ι → V)
    (hleft : negativeGram B left = A) (hright : negativeGram B right = A)
    (hlr : ∀ i j, B (left i) (right j) = 0)
    (hrl : ∀ j i, B (right j) (left i) = 0)
    (hpositive : ∃ x : V, 0 < B x x) :
    2 * Fintype.card ι < Module.finrank ℚ V := by
  have h := negativeGram_posDef_card_lt_finrank B (Sum.elim left right)
    (orthogonal_sum_negativeGram_posDef B left right
      (hleft.symm ▸ hA) (hright.symm ▸ hA) hlr hrl) hpositive
  simpa only [Fintype.card_sum, two_mul] using h

end Rational

end KltDP.LinearAlgebra
