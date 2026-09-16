import KltDP.LinearAlgebra.Discrepancy

/-!
# Support obligation U-GRAPH-BRIDGE: weights of the extra original components

Manuscript `source/manuscript.tex` lines 2790–2819 (proof of Theorem 9.3
`thm:forest-exclusion`): "For another original component `A` of weight `b = -A²`, let
`u = (C + B₁ + B₂)·A ≥ 0`. The adjoint identity gives `R·A = b - 2 + u`. The elementary
discrepancy bound and the strict discrepancy-sum inequality of the actual `(-1)`-curve
`R` therefore imply `1 > Σ_i λ_i (R·D_i) ≥ (b-2)²/b`. For `b ≥ 4` the last expression is
at least one, a contradiction. Thus every additional original weight is two or three.
Every additional weight-three vertex contributes at least `1/3` to that same sum, so
there are at most two of them."

Arithmetic clauses proved here: `(b-2)²/b ≥ 1` exactly when `b ≥ 4` (for `b ≥ 2`);
from `λ_A ≥ (b-2)/b` (the accepted `elementary_discrepancy_bound`), `R·A ≥ b - 2` and
nonnegative terms, the strict sum bound `Σ λ_i (R·D_i) < 1` forces `b ∈ {2, 3}`; and a
weight-three vertex contributes at least `1/3`, so fewer than three of them fit below one.

Not proved here: the adjoint identity for actual curves, the strict discrepancy-sum
inequality of an actual `(-1)`-curve, the valency-three bound (Lemma 4.4), and the
transport of labels, weights, edges and rational parameters from the actual
intersection pairing (F25, Theorem 8.1).
-/

namespace KltDP.Support

open scoped BigOperators

/-- `(b - 2)² / b ≥ 1 ↔ b ≥ 4` for natural weights `b ≥ 2`. -/
theorem weight_square_ratio_ge_one_iff (b : ℕ) (hb : 2 ≤ b) :
    (1 : ℚ) ≤ ((b : ℚ) - 2) ^ 2 / b ↔ 4 ≤ b := by
  have hpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  rw [le_div_iff₀ hpos, one_mul]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    interval_cases b <;> norm_num at h
  · intro h
    have : (4 : ℚ) ≤ b := by exact_mod_cast h
    nlinarith

/-- A single component of weight `b ≥ 2` with coefficient `λ ≥ (b-2)/b` and degree
`d ≥ b - 2` contributes at least `(b-2)²/b`. -/
theorem contribution_ge_ratio (b : ℕ) (hb : 2 ≤ b) (lam d : ℚ)
    (hlam : ((b : ℚ) - 2) / b ≤ lam) (hd : (b : ℚ) - 2 ≤ d) :
    ((b : ℚ) - 2) ^ 2 / b ≤ lam * d := by
  have hpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb2 : (0 : ℚ) ≤ (b : ℚ) - 2 := by
    have : (2 : ℚ) ≤ b := by exact_mod_cast hb
    linarith
  have hratio : (0 : ℚ) ≤ ((b : ℚ) - 2) / b := div_nonneg hb2 (le_of_lt hpos)
  calc ((b : ℚ) - 2) ^ 2 / b = (((b : ℚ) - 2) / b) * ((b : ℚ) - 2) := by
        field_simp
        ring
    _ ≤ lam * d := mul_le_mul hlam hd hb2 (le_trans hratio hlam)

/-- **Every additional original weight is two or three.** If the strict sum
`Σ_i λ_i d_i < 1` holds with all terms nonnegative, and a component `A` of weight
`b ≥ 2` has `λ_A ≥ (b-2)/b` and `d_A ≥ b - 2`, then `b ≤ 3`. -/
theorem weight_le_three {ι : Type*} (s : Finset ι) (lam d : ι → ℚ)
    (hnonneg : ∀ i ∈ s, 0 ≤ lam i * d i) (hsum : ∑ i ∈ s, lam i * d i < 1)
    (A : ι) (hA : A ∈ s) (b : ℕ) (hb : 2 ≤ b)
    (hlam : ((b : ℚ) - 2) / b ≤ lam A) (hd : (b : ℚ) - 2 ≤ d A) : b ≤ 3 := by
  by_contra h
  push_neg at h
  have h4 : 4 ≤ b := by omega
  have hterm : ((b : ℚ) - 2) ^ 2 / b ≤ lam A * d A := contribution_ge_ratio b hb _ _ hlam hd
  have hge : (1 : ℚ) ≤ ((b : ℚ) - 2) ^ 2 / b := (weight_square_ratio_ge_one_iff b hb).mpr h4
  have hle : lam A * d A ≤ ∑ i ∈ s, lam i * d i :=
    Finset.single_le_sum hnonneg hA
  linarith

/-- A weight-three component contributes at least `1/3`. -/
theorem weight_three_contribution (lam d : ℚ) (hlam : (1 : ℚ) / 3 ≤ lam) (hd : 1 ≤ d) :
    (1 : ℚ) / 3 ≤ lam * d := by
  nlinarith

/-- **At most two additional weight-three vertices.** -/
theorem card_weight_three_le_two {ι : Type*} (s : Finset ι) (lam d : ι → ℚ)
    (hnonneg : ∀ i ∈ s, 0 ≤ lam i * d i) (hsum : ∑ i ∈ s, lam i * d i < 1)
    (T : Finset ι) (hT : T ⊆ s) (hthree : ∀ i ∈ T, (1 : ℚ) / 3 ≤ lam i * d i) :
    T.card ≤ 2 := by
  have h1 : (T.card : ℚ) * (1 / 3) ≤ ∑ i ∈ T, lam i * d i := by
    have := Finset.sum_le_sum hthree
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  have h2 : ∑ i ∈ T, lam i * d i ≤ ∑ i ∈ s, lam i * d i :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun i hi _ => hnonneg i hi)
  have h3 : (T.card : ℚ) < 3 := by linarith
  have : T.card < 3 := by exact_mod_cast h3
  omega

/-- **U-GRAPH-BRIDGE**, arithmetic clause. -/
theorem u_graph_bridge :
    (∀ b : ℕ, 2 ≤ b → ((1 : ℚ) ≤ ((b : ℚ) - 2) ^ 2 / b ↔ 4 ≤ b)) ∧
    (∀ {ι : Type} (s : Finset ι) (lam d : ι → ℚ), (∀ i ∈ s, 0 ≤ lam i * d i) →
      ∑ i ∈ s, lam i * d i < 1 → ∀ A ∈ s, ∀ b : ℕ, 2 ≤ b →
        ((b : ℚ) - 2) / b ≤ lam A → (b : ℚ) - 2 ≤ d A → b ≤ 3) ∧
    (∀ {ι : Type} (s : Finset ι) (lam d : ι → ℚ), (∀ i ∈ s, 0 ≤ lam i * d i) →
      ∑ i ∈ s, lam i * d i < 1 → ∀ T : Finset ι, T ⊆ s →
        (∀ i ∈ T, (1 : ℚ) / 3 ≤ lam i * d i) → T.card ≤ 2) :=
  ⟨weight_square_ratio_ge_one_iff,
    fun s lam d hn hs A hA b hb hl hd => weight_le_three s lam d hn hs A hA b hb hl hd,
    fun s lam d hn hs T hT h3 => card_weight_three_le_two s lam d hn hs T hT h3⟩

end KltDP.Support
