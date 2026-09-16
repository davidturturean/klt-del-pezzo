import KltDP.LinearAlgebra.NegativeSubspaceDimension
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Support obligation U-NEF-POSITIVE-SPAN: the nonzero nef orthogonal-space obstruction

Plan contract (`U-NEF-POSITIVE-SPAN`): "A nonzero nef numerical class cannot be
orthogonal to a two-dimensional span having a positive-square vector. Apply to
the `C, P` matrix determinant `2 - m² < 0` when `m ≥ 2`."

Arithmetic clauses proved here, with no geometric object:

* the Gram matrix of a `(-2)`-curve `C` and a `(-1)`-curve `P` meeting with
  multiplicity `m` is `[[-2, m], [m, -1]]`, of determinant `2 - m²`, which is
  negative exactly when `m ≥ 2`;
* for `m ≥ 2` the explicit vector `C + P` of that span has square `2m - 3 ≥ 1`,
  so the span contains a positive-square vector (indefinite plane);
* the plane mechanism: if `L` has nonnegative square and is orthogonal to a
  vector `v` of positive square, every `L + t v` with `t ≠ 0` has positive
  square, so the span of `L` and `v` is not negative semidefinite.

The Hodge index theorem (signature `(1, ρ - 1)`), which turns these facts into
the manuscript's contradiction for a nonzero nef class, is F06 and remains open.
-/

namespace KltDP.Support

open Matrix

/-- The Gram matrix of `C` (`C² = -2`), `P` (`P² = -1`) with `C·P = m`. -/
def cpGram (m : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![-2, m; m, -1]

theorem cpGram_det (m : ℤ) : (cpGram m).det = 2 - m ^ 2 := by
  simp [cpGram, Matrix.det_fin_two]
  ring

/-- `det = 2 - m² < 0` exactly when `m ≥ 2` (for a natural multiplicity `m`). -/
theorem cpGram_det_neg_iff (m : ℕ) : (cpGram m).det < 0 ↔ 2 ≤ m := by
  rw [cpGram_det]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    interval_cases m <;> norm_num at h
  · intro h
    have : (2 : ℤ) ≤ m := by exact_mod_cast h
    nlinarith

/-- The square of `x C + y P` in the span: `-2x² + 2mxy - y²`. -/
def cpSquare (m x y : ℤ) : ℤ := -2 * x ^ 2 + 2 * m * x * y - y ^ 2

theorem cpSquare_eq_mulVec (m x y : ℤ) :
    cpSquare m x y = ![x, y] ⬝ᵥ (cpGram m *ᵥ ![x, y]) := by
  simp [cpSquare, cpGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- For `m ≥ 2`, the vector `C + P` has square `2m - 3 ≥ 1`: the plane is indefinite. -/
theorem cpSquare_one_one (m : ℕ) (hm : 2 ≤ m) : 1 ≤ cpSquare m 1 1 ∧ cpSquare m 1 1 = 2 * m - 3 := by
  have : (2 : ℤ) ≤ m := by exact_mod_cast hm
  constructor
  · simp [cpSquare]; omega
  · simp [cpSquare]; ring

/-- For `m ≤ 1` the plane is negative definite: every nonzero `(x, y)` has negative square. -/
theorem cpSquare_neg_of_le_one (m : ℕ) (hm : m ≤ 1) (x y : ℤ) (h : (x, y) ≠ (0, 0)) :
    cpSquare m x y < 0 := by
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [hc.1, hc.2])
  have hm' : (m : ℤ) = 0 ∨ (m : ℤ) = 1 := by omega
  have hpos : 0 < x ^ 2 ∨ 0 < y ^ 2 := by
    rcases hne with hx | hy
    · exact Or.inl (by positivity)
    · exact Or.inr (by positivity)
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hxy : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  rcases hm' with hm' | hm' <;> simp only [cpSquare, hm'] <;> rcases hpos with hp | hp <;> nlinarith

/-- **The plane mechanism.** If `L` has nonnegative square and is orthogonal to `v`
with `B v v > 0`, then every `L + t v` with `t ≠ 0` has positive square, so the span
of `L` and `v` is not negative semidefinite. The signature statement that makes this
contradict nefness of a nonzero `L` is the Hodge index theorem (F06). -/
theorem square_add_smul_pos {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hsymm : ∀ x y, B x y = B y x)
    (L v : V) (hL : 0 ≤ B L L) (horth : B L v = 0) (hv : 0 < B v v) (t : ℚ) (ht : t ≠ 0) :
    0 < B (L + t • v) (L + t • v) := by
  have h : B (L + t • v) (L + t • v) = B L L + 2 * t * B L v + t ^ 2 * B v v := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm v L]
    ring
  rw [h, horth]
  have : 0 < t ^ 2 * B v v := mul_pos (by positivity) hv
  linarith

/-- **U-NEF-POSITIVE-SPAN**, arithmetic clause. -/
theorem u_nef_positive_span :
    (∀ m : ℤ, (cpGram m).det = 2 - m ^ 2) ∧
    (∀ m : ℕ, (cpGram m).det < 0 ↔ 2 ≤ m) ∧
    (∀ m : ℕ, 2 ≤ m → 1 ≤ cpSquare m 1 1) ∧
    (∀ m : ℕ, m ≤ 1 → ∀ x y : ℤ, (x, y) ≠ (0, 0) → cpSquare m x y < 0) :=
  ⟨cpGram_det, cpGram_det_neg_iff, fun m hm => (cpSquare_one_one m hm).1, cpSquare_neg_of_le_one⟩

end KltDP.Support
