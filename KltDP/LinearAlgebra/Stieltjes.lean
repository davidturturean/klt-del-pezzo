import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic

/-!
# Inverse positivity for Stieltjes matrices

These results are purely algebraic, apply over both `ℚ` and `ℝ`, and do not
depend on a geometric interpretation of a matrix. Positive definiteness uses
mathlib's standard `Matrix.PosDef`; the ordered scalar field has trivial star.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
  [StarRing 𝕜] [TrivialStar 𝕜]

omit [IsStrictOrderedRing 𝕜] in
/-- Positive definiteness implies invertibility over any ordered field with
trivial star. In particular, no scalar extension is needed for rational
positive-definite matrices. -/
theorem isUnit_of_posDef [DecidableEq ι] {A : Matrix ι ι 𝕜}
    (hA : A.PosDef) : IsUnit A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hne
  have hpos : 0 < dotProduct (x - y) (A *ᵥ (x - y)) := by
    simpa only [star_trivial] using hA.2 (x - y) (sub_ne_zero.mpr hne)
  rw [Matrix.mulVec_sub, hxy, sub_self, dotProduct_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The finite-dimensional maximum principle for a positive-definite matrix
with nonpositive off-diagonal entries: a nonnegative image has a nonnegative
preimage. The proof splits the preimage into its positive and negative parts. -/
theorem nonneg_of_mulVec_nonneg {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) {x : ι → 𝕜}
    (hx : ∀ i, 0 ≤ (A *ᵥ x) i) : ∀ i, 0 ≤ x i := by
  classical
  let v : ι → 𝕜 := fun i => min (x i) 0
  let w : ι → 𝕜 := fun i => max (x i) 0
  have hv : ∀ i, v i ≤ 0 := fun i => min_le_right _ _
  have hw : ∀ i, 0 ≤ w i := fun i => le_max_right _ _
  have hvw : ∀ i, v i * w i = 0 := by
    intro i
    by_cases hi : x i ≤ 0
    · simp [v, w, min_eq_left hi, max_eq_right hi]
    · have hi' : 0 ≤ x i := le_of_lt (lt_of_not_ge hi)
      simp [v, w, min_eq_right hi', max_eq_left hi']
  have hxvw : x = v + w := by
    funext i
    simpa only [Pi.add_apply, v, w, add_zero] using (min_add_max (x i) 0).symm
  have hcross : 0 ≤ dotProduct v (A *ᵥ w) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      have hz : v i * (A i i * w i) = 0 := by
        calc
          v i * (A i i * w i) = A i i * (v i * w i) := by ring
          _ = 0 := by rw [hvw, mul_zero]
      rw [hz]
    · exact mul_nonneg_of_nonpos_of_nonpos (hv i)
        (mul_nonpos_of_nonpos_of_nonneg (hOff i j hij) (hw j))
  have hnonpos : dotProduct v (A *ᵥ x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hv i) (hx i)
  have hvzero : v = 0 := by
    by_contra hvne
    have hpos : 0 < dotProduct v (A *ᵥ v) := by
      simpa only [star_trivial] using hA.2 v hvne
    rw [hxvw, Matrix.mulVec_add, dotProduct_add] at hnonpos
    exact (not_le_of_gt (add_pos_of_pos_of_nonneg hpos hcross)) hnonpos
  intro i
  have hi : min (x i) 0 = 0 := congrFun hvzero i
  exact (min_eq_right_iff.mp hi)

/-- The inverse of a Stieltjes matrix is entrywise nonnegative. This includes
the empty matrix, and is valid directly over the rational numbers. -/
theorem stieltjes_inverse_nonnegative [DecidableEq ι] {A : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hOff : ∀ i j, i ≠ j → A i j ≤ 0) :
    ∀ i j, 0 ≤ A⁻¹ i j := by
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  intro i j
  have hx := nonneg_of_mulVec_nonneg hA hOff
    (x := A⁻¹ *ᵥ Pi.single j 1) (by
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
      intro k
      by_cases hkj : k = j
      · subst k
        simp
      · simp [Pi.single_apply, hkj])
  simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply] using hx i

/-- Applying a Stieltjes inverse preserves coordinatewise nonnegativity. -/
theorem stieltjes_inverse_mulVec_nonnegative [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) {b : ι → 𝕜}
    (hb : ∀ i, 0 ≤ b i) : ∀ i, 0 ≤ (A⁻¹ *ᵥ b) i := by
  intro i
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (stieltjes_inverse_nonnegative hA hOff i j) (hb j)

/-- The graph of the nonzero off-diagonal entries. The relation is symmetrized
so that the definition applies to any matrix; for a symmetric matrix this is
exactly the usual graph of its nonzero off-diagonal entries. -/
def nonzeroOffDiagonalGraph (A : Matrix ι ι 𝕜) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => A i j ≠ 0

omit [Fintype ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem nonzeroOffDiagonalGraph_adj_iff {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (i j : ι) :
    (nonzeroOffDiagonalGraph A).Adj i j ↔ i ≠ j ∧ A i j ≠ 0 := by
  have hsym : A j i = A i j := by
    simpa only [star_trivial] using hA.apply i j
  simp only [nonzeroOffDiagonalGraph, SimpleGraph.fromRel_adj, hsym, or_self]

omit [StarRing 𝕜] [TrivialStar 𝕜] in
/-- A zero coordinate of a nonnegative vector with nonnegative image forces
zero at each coordinate joined to it by a nonzero matrix entry. No
positive-definiteness hypothesis is needed for this local assertion. -/
theorem eq_zero_of_nonzero_entry_of_eq_zero {A : Matrix ι ι 𝕜}
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) {x : ι → 𝕜}
    (hx : ∀ i, 0 ≤ x i) (hAx : ∀ i, 0 ≤ (A *ᵥ x) i)
    {i j : ι} (hi : x i = 0) (hij : A i j ≠ 0) : x j = 0 := by
  classical
  have hterm : ∀ k, A i k * x k ≤ 0 := by
    intro k
    by_cases hik : i = k
    · subst k
      rw [hi, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i k hik) (hx k)
  have hsum : ∑ k, A i k * x k = 0 :=
    le_antisymm (Finset.sum_nonpos fun k _ => hterm k) (hAx i)
  have hzero : A i j * x j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hterm k)).mp hsum j
      (Finset.mem_univ j)
  exact (mul_eq_zero.mp hzero).resolve_left hij

/-- The strict inverse-positivity assertion is local to a connected component:
an inverse entry is positive whenever its row and column are joined by a path
of nonzero off-diagonal entries. This also proves positivity of every diagonal
entry, without a connectivity assumption on the whole matrix. -/
theorem stieltjes_inverse_positive_of_reachable [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) {i j : ι}
    (hpath : (nonzeroOffDiagonalGraph A).Reachable i j) :
    0 < A⁻¹ i j := by
  classical
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  let x : ι → 𝕜 := A⁻¹ *ᵥ Pi.single j 1
  have hAx : A *ᵥ x = Pi.single j 1 := by
    change A *ᵥ (A⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hAx_nonneg : ∀ k, 0 ≤ (A *ᵥ x) k := by
    rw [hAx]
    intro k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [Pi.single_apply, hkj]
  have hx : ∀ k, 0 ≤ x k := nonneg_of_mulVec_nonneg hA hOff hAx_nonneg
  have propagate : ∀ {a b : ι}, (nonzeroOffDiagonalGraph A).Reachable a b →
      x a = 0 → x b = 0 := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact id
    | @cons a c b hac p ih =>
      intro ha
      exact ih (eq_zero_of_nonzero_entry_of_eq_zero hOff hx hAx_nonneg ha
        ((nonzeroOffDiagonalGraph_adj_iff hA.1 a c).mp hac).2)
  have hxi_ne : x i ≠ 0 := by
    intro hi
    have hj : x j = 0 := propagate hpath hi
    have hterms : ∀ k, A j k * x k ≤ 0 := by
      intro k
      by_cases hjk : j = k
      · subst k
        rw [hj, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (hOff j k hjk) (hx k)
    have hnonpos : (A *ᵥ x) j ≤ 0 :=
      Finset.sum_nonpos fun k _ => hterms k
    rw [hAx] at hnonpos
    have h10 : (1 : 𝕜) ≤ 0 := by simpa using hnonpos
    exact (not_le_of_gt (zero_lt_one : (0 : 𝕜) < 1)) h10
  have hxi : 0 < x i := lt_of_le_of_ne (hx i) hxi_ne.symm
  change 0 < (A⁻¹ *ᵥ Pi.single j 1) i at hxi
  simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply] using hxi

/-- A Stieltjes inverse is strictly positive on every entry when its graph is
connected. Preconnectedness suffices: the empty case is vacuous. -/
theorem stieltjes_inverse_positive [DecidableEq ι] {A : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hConn : (nonzeroOffDiagonalGraph A).Preconnected) :
    ∀ i j, 0 < A⁻¹ i j :=
  fun i j => stieltjes_inverse_positive_of_reachable hA hOff (hConn i j)

/-- Positive source coefficients give strictly positive inverse coefficients
even for a disconnected Stieltjes matrix. -/
theorem stieltjes_inverse_mulVec_positive [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) {b : ι → 𝕜}
    (hb : ∀ i, 0 < b i) : ∀ i, 0 < (A⁻¹ *ᵥ b) i := by
  intro i
  have hdiag : 0 < A⁻¹ i i :=
    stieltjes_inverse_positive_of_reachable hA hOff (.refl i)
  exact lt_of_lt_of_le (mul_pos hdiag (hb i))
    (Finset.single_le_sum (fun j _ =>
      mul_nonneg (stieltjes_inverse_nonnegative hA hOff i j) (hb j).le)
      (Finset.mem_univ i))

end KltDP.LinearAlgebra
