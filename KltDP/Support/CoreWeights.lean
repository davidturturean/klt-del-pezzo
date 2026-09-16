import KltDP.Support.CountZeroContact

/-!
# Support obligation U-CORE-WEIGHTS: from two higher contacts to `β ∈ {3, 4, 5}`

Manuscript `source/manuscript.tex` lines 2359–2415 (proof of Theorem 8.1
`thm:adjoint-reduction`). Plan contract (`U-CORE-WEIGHTS`): "after proving exactly
one simple weight-two contact and two simple higher-weight contacts on a shortest
curve of a minimal counterexample, derive `C` leaf/isolated, core disjointness,
higher vertices in different connected components, and weights `(3, β)`,
`β ∈ {3, 4, 5}`"; strategy: "use discrepancy lower bounds and `1/b₁ + 1/b₂ > 1/2`;
prove the elementary integer classification with `b₁, b₂ ≥ 3`."

Arithmetic clauses proved here:

* each higher-weight contact of weight `b ≥ 3` contributes at least
  `(b - 2)/b ≥ 1/3` to the discrepancy sum (the accepted
  `KltDP.LinearAlgebra.elementary_discrepancy_bound` supplies `(b-2)/b ≤ λ`);
  two such contributions below one give `1/b₁ + 1/b₂ > 1/2`, equivalently
  `b₁ b₂ < 2(b₁ + b₂)`;
* the integer classification: for `b₁, b₂ ≥ 3` with `b₁ b₂ < 2(b₁ + b₂)`, the
  smaller weight is `3` and the larger is `3`, `4` or `5`;
* three contributions of at least `1/3` are impossible below one, so there are
  at most two higher-weight contacts;
* the count consequences (`s_C = 0` or `s_C ≤ 1`) are the accepted
  `KltDP.Support.sC_of_countChange_neg`.

The geometric clauses (simplicity of contacts, the excess-contact lemma,
adjacent-contact adjoints, the two-contact ruling, core disjointness and
component separation) are Theorems 4.5–7.5 and remain open.
-/

namespace KltDP.Support

/-- `(b - 2)/b ≥ 1/3` for every weight `b ≥ 3`. -/
theorem higher_weight_contribution_ge_third (b : ℕ) (hb : 3 ≤ b) :
    (1 : ℚ) / 3 ≤ ((b : ℚ) - 2) / b := by
  have hb' : (3 : ℚ) ≤ b := by exact_mod_cast hb
  have hpos : (0 : ℚ) < b := by linarith
  rw [div_le_div_iff₀ (by norm_num) hpos]
  linarith

/-- Three higher-weight contacts would contribute at least one. -/
theorem three_higher_contacts_impossible (b₁ b₂ b₃ : ℕ) (h₁ : 3 ≤ b₁) (h₂ : 3 ≤ b₂) (h₃ : 3 ≤ b₃) :
    ¬ (((b₁ : ℚ) - 2) / b₁ + ((b₂ : ℚ) - 2) / b₂ + ((b₃ : ℚ) - 2) / b₃ < 1) := by
  have := higher_weight_contribution_ge_third b₁ h₁
  have := higher_weight_contribution_ge_third b₂ h₂
  have := higher_weight_contribution_ge_third b₃ h₃
  intro h
  linarith

/-- Two contributions below one give `b₁ b₂ < 2 (b₁ + b₂)` (equivalently `1/b₁ + 1/b₂ > 1/2`). -/
theorem product_lt_of_two_contacts (b₁ b₂ : ℕ) (h₁ : 3 ≤ b₁) (h₂ : 3 ≤ b₂)
    (h : ((b₁ : ℚ) - 2) / b₁ + ((b₂ : ℚ) - 2) / b₂ < 1) :
    b₁ * b₂ < 2 * (b₁ + b₂) := by
  have p₁ : (0 : ℚ) < b₁ := by exact_mod_cast (by omega : 0 < b₁)
  have p₂ : (0 : ℚ) < b₂ := by exact_mod_cast (by omega : 0 < b₂)
  rw [div_add_div _ _ (ne_of_gt p₁) (ne_of_gt p₂), div_lt_one (mul_pos p₁ p₂)] at h
  have hz : ((b₁ : ℤ) - 2) * b₂ + (b₁ : ℤ) * ((b₂ : ℤ) - 2) < (b₁ : ℤ) * b₂ := by
    exact_mod_cast h
  have : (b₁ : ℤ) * b₂ < 2 * ((b₁ : ℤ) + b₂) := by linarith
  exact_mod_cast this

/-- The elementary integer classification: `b₁, b₂ ≥ 3` and `b₁ b₂ < 2(b₁ + b₂)` force
`min = 3` and `max ∈ {3, 4, 5}`. -/
theorem core_weights_classification (b₁ b₂ : ℕ) (h₁ : 3 ≤ b₁) (h₂ : 3 ≤ b₂)
    (h : b₁ * b₂ < 2 * (b₁ + b₂)) :
    min b₁ b₂ = 3 ∧ (max b₁ b₂ = 3 ∨ max b₁ b₂ = 4 ∨ max b₁ b₂ = 5) := by
  have hcase : b₁ = 3 ∨ b₂ = 3 := by
    by_contra hc
    push_neg at hc
    have h₁' : 4 ≤ b₁ := by omega
    have h₂' : 4 ≤ b₂ := by omega
    nlinarith
  rcases hcase with rfl | rfl
  · have : b₂ < 6 := by omega
    refine ⟨by omega, ?_⟩
    interval_cases b₂ <;> simp
  · have : b₁ < 6 := by omega
    refine ⟨by omega, ?_⟩
    interval_cases b₁ <;> simp

/-- **U-CORE-WEIGHTS**, arithmetic clause: two higher-weight contacts with
discrepancy contributions below one have weights `(3, β)` with `β ∈ {3, 4, 5}`, a
third higher-weight contact is impossible, and a negative singular-count change
with at most two higher contacts forces the deleted weight-two curve to be a
leaf or isolated. -/
theorem u_core_weights :
    (∀ b₁ b₂ : ℕ, 3 ≤ b₁ → 3 ≤ b₂ → ((b₁ : ℚ) - 2) / b₁ + ((b₂ : ℚ) - 2) / b₂ < 1 →
      min b₁ b₂ = 3 ∧ (max b₁ b₂ = 3 ∨ max b₁ b₂ = 4 ∨ max b₁ b₂ = 5)) ∧
    (∀ b₁ b₂ b₃ : ℕ, 3 ≤ b₁ → 3 ≤ b₂ → 3 ≤ b₃ →
      ¬ (((b₁ : ℚ) - 2) / b₁ + ((b₂ : ℚ) - 2) / b₂ + ((b₃ : ℚ) - 2) / b₃ < 1)) ∧
    (∀ sC j : ℕ, countChange sC j < 0 → j ≤ 2 → (j ≤ 1 → sC = 0) ∧ (j = 2 → sC ≤ 1)) :=
  ⟨fun b₁ b₂ h₁ h₂ h => core_weights_classification b₁ b₂ h₁ h₂ (product_lt_of_two_contacts b₁ b₂ h₁ h₂ h),
    three_higher_contacts_impossible, sC_of_countChange_neg⟩

end KltDP.Support
