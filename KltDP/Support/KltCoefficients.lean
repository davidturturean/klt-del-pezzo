import KltDP.LinearAlgebra.Stieltjes

/-!
# Support obligation U-KLT-COEFFICIENTS: `(-2)` is not synonymous with discrepancy zero

Manuscript `source/manuscript.tex` lines 314–326: "A coefficient attached to a
`(-2)`-curve need not vanish when that curve is in a connected exceptional
divisor containing a curve of smaller self-intersection. We therefore
distinguish self-intersection from discrepancy throughout." The coefficient
vector `λ` of the manuscript is defined by the row equation `A λ = q` with
`A = (-D_i·D_j)` the positive-definite negative intersection matrix and
`q_i = -2 - D_i² = b_i - 2` for a component of self-intersection `-b_i`.

This module proves the two arithmetic facts behind that sentence, with no
geometric object involved:

* on the two-vertex chain with weights `(3, 2)` the unique solution of the row
  equation gives the weight-two vertex the positive coefficient `1/5`, so a
  `(-2)`-curve attached to a `(-3)`-curve has positive coefficient;
* for a connected block consisting only of weight-two vertices the right-hand
  side is `q = 0`, and positive definiteness of `A` forces `λ = 0`. The vanishing
  is a consequence of the whole block equation `A λ = 0`, not of the weight of an
  individual vertex.

The identification of `λ` with the actual discrepancy coefficients of the
minimal resolution (F04, Proposition 2.4) is a separate geometric obligation.
-/

namespace KltDP.Support

open Matrix KltDP.LinearAlgebra

/-- The manuscript's right-hand side `q_i = b_i - 2` for a component of
self-intersection `-b_i`. -/
def canonicalRightHandSide {ι 𝕜 : Type*} [Field 𝕜] (b : ι → 𝕜) : ι → 𝕜 :=
  fun i => b i - 2

/-- A block all of whose vertices have weight two has `q = 0`. -/
theorem canonicalRightHandSide_eq_zero_of_allWeightTwo {ι 𝕜 : Type*} [Field 𝕜]
    {b : ι → 𝕜} (hb : ∀ i, b i = 2) : canonicalRightHandSide b = 0 := by
  funext i
  simp [canonicalRightHandSide, hb i]

variable {ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [StarRing 𝕜] [TrivialStar 𝕜] [Fintype ι] [DecidableEq ι]

/-- A positive-definite row equation `A λ = 0` has only the zero solution. -/
theorem coefficients_eq_zero_of_posDef {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    {lam : ι → 𝕜} (hrow : A *ᵥ lam = 0) : lam = 0 := by
  have hunit : IsUnit A := isUnit_of_posDef hA
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunit
  calc lam = (A⁻¹ * A) *ᵥ lam := by rw [Matrix.nonsing_inv_mul A hdet, one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ lam) := by rw [mulVec_mulVec]
    _ = 0 := by rw [hrow, mulVec_zero]

/-- **All-weight-two block.** If every vertex of a positive-definite block has
weight two, every coefficient solving the block equation vanishes. -/
theorem coefficients_eq_zero_of_allWeightTwo {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    {b lam : ι → 𝕜} (hb : ∀ i, b i = 2)
    (hrow : A *ᵥ lam = canonicalRightHandSide b) : lam = 0 :=
  coefficients_eq_zero_of_posDef hA
    (by rw [hrow, canonicalRightHandSide_eq_zero_of_allWeightTwo hb])

/-- The negative intersection matrix of a `(-3)`-curve meeting a `(-2)`-curve once. -/
def chainThreeTwo : Matrix (Fin 2) (Fin 2) ℚ := !![3, -1; -1, 2]

/-- Its right-hand side `q = (3 - 2, 2 - 2) = (1, 0)`. -/
theorem chainThreeTwo_rhs :
    canonicalRightHandSide (![3, 2] : Fin 2 → ℚ) = ![1, 0] := by
  funext i
  fin_cases i <;> simp [canonicalRightHandSide] <;> norm_num

/-- The row equation on the `(3, 2)` chain has the unique solution `(2/5, 1/5)`. -/
theorem chainThreeTwo_solution (lam : Fin 2 → ℚ)
    (h : chainThreeTwo *ᵥ lam = ![1, 0]) : lam = ![2 / 5, 1 / 5] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [chainThreeTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i
  · simp; linarith
  · simp; linarith

/-- The solution indeed satisfies the row equation. -/
theorem chainThreeTwo_mulVec :
    chainThreeTwo *ᵥ ![2 / 5, 1 / 5] = ![1, 0] := by
  funext i
  fin_cases i <;> simp [chainThreeTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- **A weight-two vertex with positive coefficient.** On the `(3, 2)` chain the
coefficient of the weight-two vertex is `1/5 > 0` although its weight is two. -/
theorem weightTwo_coefficient_pos (lam : Fin 2 → ℚ)
    (h : chainThreeTwo *ᵥ lam = canonicalRightHandSide ![3, 2]) :
    (![3, 2] : Fin 2 → ℚ) 1 = 2 ∧ 0 < lam 1 := by
  rw [chainThreeTwo_rhs] at h
  rw [chainThreeTwo_solution lam h]
  norm_num

/-- **U-KLT-COEFFICIENTS**, arithmetic clause: weight two does not force a zero
coefficient (the `(3,2)` chain), while an all-weight-two positive-definite block
has zero coefficients because of the block equation. -/
theorem u_klt_coefficients :
    (∀ lam : Fin 2 → ℚ, chainThreeTwo *ᵥ lam = canonicalRightHandSide ![3, 2] →
      (![3, 2] : Fin 2 → ℚ) 1 = 2 ∧ 0 < lam 1) ∧
    (∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ ℚ) (b lam : κ → ℚ),
      A.PosDef → (∀ i, b i = 2) → A *ᵥ lam = canonicalRightHandSide b → lam = 0) :=
  ⟨weightTwo_coefficient_pos,
    fun _ _ _ _ _ _ hA hb hrow => coefficients_eq_zero_of_allWeightTwo hA hb hrow⟩

end KltDP.Support
