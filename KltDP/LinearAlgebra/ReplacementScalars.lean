import Mathlib.Tactic

/-!
# Scalar inequalities for surface replacements

These lemmas isolate the ordered-field algebra in manuscript Theorems 4.5 and
4.6. They apply independently of geometry. They do not assert that any divisor
or morphism realizing their inputs exists.
-/

namespace KltDP.LinearAlgebra

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The coefficient used in a one-component replacement is positive. -/
theorem replacement_coefficient_pos {h η : 𝕜} (hh : h < 1) (hη : η < 1) :
    0 < (1 - η) / (1 - h) :=
  div_pos (sub_pos.mpr hη) (sub_pos.mpr hh)

/-- This includes the negative coefficient on the nonminimal resolution. -/
theorem neg_replacement_coefficient_lt_one {h η : 𝕜} (hh : h < 1) (hη : η < 1) :
    -((1 - η) / (1 - h)) < 1 := by
  have hc := replacement_coefficient_pos hh hη
  linarith

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The polynomial identity controlling the square gain. -/
theorem replacement_square_numerator (g h η τ μ : 𝕜) :
    g * (1 - η) ^ 2 - μ ^ 2 * (1 - h) =
      g * (1 - η - τ * μ) ^ 2 +
      2 * g * τ * μ * (1 - η - τ * μ) +
      μ ^ 2 * (h + g * τ ^ 2 - 1) := by
  ring

/-- Strict gain also when the removed discrepancy coefficient is zero. -/
theorem replacement_square_gain_pos {g h η τ μ : 𝕜}
    (hg : 0 < g) (hh : h < 1) (hτ : 0 < τ) (hμ : 0 ≤ μ)
    (hℓ : 0 < 1 - η - τ * μ) (henergy : 1 < h + g * τ ^ 2) :
    0 < (1 - η) ^ 2 / (1 - h) - μ ^ 2 / g := by
  have hnum : 0 < g * (1 - η) ^ 2 - μ ^ 2 * (1 - h) := by
    rw [replacement_square_numerator]
    have hfirst : 0 < g * (1 - η - τ * μ) ^ 2 :=
      mul_pos hg (sq_pos_of_pos hℓ)
    have hsecond : 0 ≤ 2 * g * τ * μ * (1 - η - τ * μ) := by positivity
    have hthird : 0 ≤ μ ^ 2 * (h + g * τ ^ 2 - 1) := by
      exact mul_nonneg (sq_nonneg μ) (le_of_lt (sub_pos.mpr henergy))
    linarith
  have heq : (1 - η) ^ 2 / (1 - h) - μ ^ 2 / g =
      (g * (1 - η) ^ 2 - μ ^ 2 * (1 - h)) / (g * (1 - h)) := by
    field_simp [ne_of_gt hg, ne_of_gt (sub_pos.mpr hh)]
    ring
  rw [heq]
  exact div_pos hnum (mul_pos hg (sub_pos.mpr hh))

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The polynomial identity controlling the degree of the deleted curve. -/
theorem replacement_degree_numerator (g h η τ μ : 𝕜) :
    g * τ * (1 - η) - μ * (1 - h) =
      g * τ * (1 - η - τ * μ) + μ * (h + g * τ ^ 2 - 1) := by
  ring

theorem replacement_deleted_degree_pos {g h η τ μ : 𝕜}
    (hg : 0 < g) (hh : h < 1) (hτ : 0 < τ) (hμ : 0 ≤ μ)
    (hℓ : 0 < 1 - η - τ * μ) (henergy : 1 < h + g * τ ^ 2) :
    0 < τ * ((1 - η) / (1 - h)) - μ / g := by
  have hnum : 0 < g * τ * (1 - η) - μ * (1 - h) := by
    rw [replacement_degree_numerator]
    have hfirst : 0 < g * τ * (1 - η - τ * μ) := mul_pos (mul_pos hg hτ) hℓ
    have hsecond : 0 ≤ μ * (h + g * τ ^ 2 - 1) :=
      mul_nonneg hμ (le_of_lt (sub_pos.mpr henergy))
    linarith
  have heq : τ * ((1 - η) / (1 - h)) - μ / g =
      (g * τ * (1 - η) - μ * (1 - h)) / (g * (1 - h)) := by
    field_simp [ne_of_gt hg, ne_of_gt (sub_pos.mpr hh)]
    ring
  rw [heq]
  exact div_pos hnum (mul_pos hg (sub_pos.mpr hh))

/-- Nonterminal square gain in the isolated-node exchange. -/
theorem isolated_exchange_square_gain_pos {h η : 𝕜}
    (hh : 1 / 2 < h) (hhη : h ≤ η) (hη : η < 1) :
    0 < 2 - η ^ 2 / h := by
  have hpos : 0 < h := by linarith
  have hηpos : 0 < η := lt_of_lt_of_le hpos hhη
  have hsq : η ^ 2 < 1 := by nlinarith
  have hquot : η ^ 2 / h < 2 := (div_lt_iff₀ hpos).2 (by nlinarith)
  linarith

/-- The terminal blowup introduces a positive coefficient increment. -/
theorem isolated_exchange_increment_pos {h η : 𝕜}
    (hh : 1 / 2 < h) (hη : η < 1) :
    0 < (2 * h - η) / (4 * h - 1) := by
  apply div_pos <;> linarith

/-- Comparison with the original discrepancy preserves its strict upper bound. -/
theorem isolated_exchange_increment_lt {h η : 𝕜}
    (hh : 1 / 2 < h) (hhη : h ≤ η) :
    (2 * h - η) / (4 * h - 1) < η := by
  apply (div_lt_iff₀ (by linarith : 0 < 4 * h - 1)).2
  have hp : 0 < 2 * h * (2 * η - 1) := by
    apply mul_pos <;> linarith
  nlinarith

theorem isolated_exchange_terminal_gain_pos {h η : 𝕜}
    (hh : 1 / 2 < h) (hhη : h ≤ η) (hη : η < 1) :
    0 < 2 * (2 * η * (1 - η) + 2 * h - 1) / (4 * h - 1) := by
  have hηpos : 0 < η := by linarith
  have hprod : 0 < 2 * η * (1 - η) :=
    mul_pos (mul_pos (by norm_num) hηpos) (sub_pos.mpr hη)
  apply div_pos <;> nlinarith

end OrderedField

end KltDP.LinearAlgebra
