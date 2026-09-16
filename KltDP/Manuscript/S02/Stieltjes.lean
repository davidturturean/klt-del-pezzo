import KltDP.LinearAlgebra.Stieltjes

/-!
# Manuscript Lemma 2.1: positivity of a Stieltjes inverse

Source: `source/manuscript.tex`, lines 359–365, label `lem:stieltjes`.
`Matrix.PosDef` includes symmetry over `ℝ` and `ℚ`, since their star is
trivial. The graph below has an edge precisely at each nonzero off-diagonal
entry, by `nonzeroOffDiagonalGraph_adj_iff`.

The reusable proof works over any ordered field with trivial star. Therefore
the rational specialization is proved directly over `ℚ`, with no scalar
extension and no geometric characteristic hypothesis.
-/

namespace KltDP.Manuscript.S02

open KltDP.LinearAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both assertions of manuscript Lemma 2.1, over the real numbers. -/
theorem stieltjesInverse (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) :
    (∀ i j, 0 ≤ A⁻¹ i j) ∧
      ((nonzeroOffDiagonalGraph A).Connected → ∀ i j, 0 < A⁻¹ i j) :=
  ⟨stieltjes_inverse_nonnegative hA hOff,
    fun hConn => stieltjes_inverse_positive hA hOff hConn.preconnected⟩

/-- The rational version used for intersection matrices in the manuscript. -/
theorem stieltjesInverse_rat (A : Matrix ι ι ℚ) (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) :
    (∀ i j, 0 ≤ A⁻¹ i j) ∧
      ((nonzeroOffDiagonalGraph A).Connected → ∀ i j, 0 < A⁻¹ i j) :=
  ⟨stieltjes_inverse_nonnegative hA hOff,
    fun hConn => stieltjes_inverse_positive hA hOff hConn.preconnected⟩

end KltDP.Manuscript.S02
