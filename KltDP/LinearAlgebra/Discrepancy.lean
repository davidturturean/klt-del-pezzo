import KltDP.LinearAlgebra.Stieltjes

/-!
# Discrepancy bounds and integral contact constraints

This file proves the ordered-field algebra behind manuscript
`lem:elementary-discrepancy` and `lem:excess-contact`. It does not assume a
geometric interpretation of any vector or matrix. In particular, an application
to a resolution must separately supply its intersection matrix, row equation,
integral contact multiplicities, and strict discrepancy budget.

The coordinate lower bound follows directly from the row equation; neither a
Schur complement nor positive definiteness is needed for that bound. Positivity
of a Stieltjes inverse is used only in the specialization of excess-contact
existence.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {ι κ 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Nonpositive off-diagonal terms bound each row of a nonnegative solution by
its diagonal contribution. -/
theorem rowEquation_le_diagonal [Fintype ι] {A : Matrix ι ι 𝕜}
    {q coeff : ι → 𝕜} (hrow : A *ᵥ coeff = q)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (hcoeff : ∀ i, 0 ≤ coeff i) (i : ι) :
    q i ≤ A i i * coeff i := by
  classical
  have hsum : (∑ j, A i j * coeff j) ≤
      ∑ j, if j = i then A i i * coeff i else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j = i
    · subst j
      simp
    · simpa only [if_neg hji] using
        mul_nonpos_of_nonpos_of_nonneg (hOff i j (Ne.symm hji)) (hcoeff j)
  have hcoord : (A *ᵥ coeff) i ≤ A i i * coeff i := by
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] using hsum
  simpa only [hrow] using hcoord

/-- Division by a positive diagonal entry gives a coefficient lower bound. -/
theorem div_diagonal_le_of_rowEquation [Fintype ι] {A : Matrix ι ι 𝕜}
    {q coeff : ι → 𝕜} (hrow : A *ᵥ coeff = q)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (hcoeff : ∀ i, 0 ≤ coeff i)
    (i : ι) (hdiag : 0 < A i i) : q i / A i i ≤ coeff i := by
  apply (div_le_iff₀ hdiag).2
  simpa only [mul_comm] using rowEquation_le_diagonal hrow hOff hcoeff i

/-- The algebraic elementary discrepancy bound, with canonical source vector
`q i = A i i - 2`. It holds at every positive diagonal entry, so includes the
manuscript's specialization to an integer weight at least three. -/
theorem elementary_discrepancy_bound [Fintype ι] {A : Matrix ι ι 𝕜}
    {coeff : ι → 𝕜} (hrow : A *ᵥ coeff = fun i => A i i - 2)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (hcoeff : ∀ i, 0 ≤ coeff i)
    (i : ι) (hdiag : 0 < A i i) : (A i i - 2) / A i i ≤ coeff i :=
  div_diagonal_le_of_rowEquation hrow hOff hcoeff i hdiag

/-- An entrywise nonnegative matrix preserves coordinatewise inequalities. -/
theorem mulVec_mono_of_entrywise_nonnegative [Fintype κ]
    {B : Matrix ι κ 𝕜} (hB : ∀ i j, 0 ≤ B i j) {x y : κ → 𝕜}
    (hxy : ∀ j, x j ≤ y j) : ∀ i, (B *ᵥ x) i ≤ (B *ᵥ y) i := by
  intro i
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hxy j) (hB i j)

/-- Dotting with a nonnegative vector preserves coordinatewise inequalities. -/
theorem dotProduct_mono_right_of_nonnegative [Fintype ι]
    {p x y : ι → 𝕜} (hp : ∀ i, 0 ≤ p i) (hxy : ∀ i, x i ≤ y i) :
    dotProduct p x ≤ dotProduct p y :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hp i)

/-- The two quadratic inequalities force an excess coordinate. This statement
uses only entrywise nonnegativity of `B`, and so is independent of an inverse
or geometric realization. -/
theorem exists_excess_of_quadratic_budget [Fintype ι] {B : Matrix ι ι 𝕜}
    (hB : ∀ i j, 0 ≤ B i j) {p q : ι → 𝕜} (hp : ∀ i, 0 ≤ p i)
    (hprojection : 1 ≤ dotProduct p (B *ᵥ p))
    (hbudget : dotProduct p (B *ᵥ q) < 1) : ∃ i, q i < p i := by
  classical
  by_contra hnot
  push_neg at hnot
  have hmono := dotProduct_mono_right_of_nonnegative hp
    (mulVec_mono_of_entrywise_nonnegative hB hnot)
  exact (not_lt_of_ge hprojection) (lt_of_le_of_lt hmono hbudget)

/-- Excess-coordinate existence for the inverse of a Stieltjes matrix. The
projection inequality and discrepancy budget remain explicit hypotheses. -/
theorem exists_excess_of_stieltjes_budget [Fintype ι] [DecidableEq ι]
    [StarRing 𝕜] [TrivialStar 𝕜] {A : Matrix ι ι 𝕜}
    (hA : A.PosDef) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    {p q : ι → 𝕜} (hp : ∀ i, 0 ≤ p i)
    (hprojection : 1 ≤ dotProduct p (A⁻¹ *ᵥ p))
    (hbudget : dotProduct p (A⁻¹ *ᵥ q) < 1) : ∃ i, q i < p i :=
  exists_excess_of_quadratic_budget (stieltjes_inverse_nonnegative hA hOff)
    hp hprojection hbudget

/-- Every summand in a nonnegative discrepancy budget is strictly less than
one. Contact multiplicities are natural numbers; coefficients lie in any
ordered field. -/
theorem contact_contribution_lt_one [Fintype ι] {p : ι → ℕ} {coeff : ι → 𝕜}
    (hcoeff : ∀ i, 0 ≤ coeff i) (hbudget : (∑ i, (p i : 𝕜) * coeff i) < 1) (i : ι) :
    (p i : 𝕜) * coeff i < 1 :=
  lt_of_le_of_lt (Finset.single_le_sum
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hcoeff j)) (Finset.mem_univ i)) hbudget

/-- Two distinct contacts also satisfy the strict budget jointly. -/
theorem two_contact_contributions_lt_one [Fintype ι] {p : ι → ℕ} {coeff : ι → 𝕜}
    (hcoeff : ∀ i, 0 ≤ coeff i) (hbudget : (∑ i, (p i : 𝕜) * coeff i) < 1)
    {i j : ι} (hij : i ≠ j) : (p i : 𝕜) * coeff i + (p j : 𝕜) * coeff j < 1 :=
  lt_of_le_of_lt (Finset.add_le_sum
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hcoeff k))
    (Finset.mem_univ i) (Finset.mem_univ j) hij) hbudget

/-- A nonzero bounded integral contact is simple. The coefficient bound is
the elementary discrepancy bound at weight `q + 2`. -/
theorem bounded_contact_eq_one {p q : ℕ} {coeff : 𝕜}
    (hp : 0 < p) (hpq : p ≤ q)
    (hlower : (q : 𝕜) / ((q : 𝕜) + 2) ≤ coeff)
    (hbudget : (p : 𝕜) * coeff < 1) : p = 1 := by
  by_contra hne
  have hp2 : 2 ≤ p := by omega
  have hp2' : (2 : 𝕜) ≤ (p : 𝕜) := by exact_mod_cast hp2
  have hq2 : (2 : 𝕜) ≤ (q : 𝕜) := by exact_mod_cast (le_trans hp2 hpq)
  have hden : 0 < (q : 𝕜) + 2 := by positivity
  have hhalf : (1 : 𝕜) / 2 ≤ coeff := by
    apply le_trans _ hlower
    apply (le_div_iff₀ hden).2
    nlinarith
  have hcoeff0 : 0 ≤ coeff := le_trans (by norm_num) hhalf
  have hmul := mul_le_mul_of_nonneg_right hp2' hcoeff0
  nlinarith

/-- A higher-weight integral excess contact has weight three and multiplicity
two. Natural subtraction is legitimate because the weight is at least three.
No geometric assertions are included in the hypotheses or conclusion. -/
theorem higher_weight_excess_contact_rigidity {b p : ℕ} {coeff : 𝕜}
    (hb : 3 ≤ b) (hexcess : b - 2 < p)
    (hlower : ((b : 𝕜) - 2) / (b : 𝕜) ≤ coeff)
    (hbudget : (p : 𝕜) * coeff < 1) : b = 3 ∧ p = 2 := by
  have hb3 : b = 3 := by
    by_contra hne
    have hb4 : 4 ≤ b := by omega
    have hb4' : (4 : 𝕜) ≤ (b : 𝕜) := by exact_mod_cast hb4
    have hden : 0 < (b : 𝕜) := by exact_mod_cast (show 0 < b by omega)
    have hhalf : (1 : 𝕜) / 2 ≤ coeff := by
      apply le_trans _ hlower
      apply (le_div_iff₀ hden).2
      nlinarith
    have hcoeff0 : 0 ≤ coeff := le_trans (by norm_num) hhalf
    have hp2 : (2 : 𝕜) ≤ (p : 𝕜) := by
      exact_mod_cast (show 2 ≤ p by omega)
    have hmul := mul_le_mul_of_nonneg_right hp2 hcoeff0
    nlinarith
  refine ⟨hb3, ?_⟩
  have hthird : (1 : 𝕜) / 3 ≤ coeff := by
    convert hlower using 1; norm_num [hb3]
  have hcoeff0 : 0 ≤ coeff := le_trans (by norm_num) hthird
  by_contra hne
  have hp3 : (3 : 𝕜) ≤ (p : 𝕜) := by
    exact_mod_cast (show 3 ≤ p by omega)
  have hmul := mul_le_mul_of_nonneg_right hp3 hcoeff0
  nlinarith

/-- There is at most one higher-weight excess contact under a nonnegative
global discrepancy budget. This uses both distinct summands, rather than only
the separate one-coordinate bounds. -/
theorem higher_weight_excess_contact_unique [Fintype ι]
    {b p : ι → ℕ} {coeff : ι → 𝕜}
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hlower : ∀ i, ((b i : 𝕜) - 2) / (b i : 𝕜) ≤ coeff i)
    (hbudget : (∑ i, (p i : 𝕜) * coeff i) < 1)
    {i j : ι} (hi : 3 ≤ b i) (hexcess_i : b i - 2 < p i)
    (hj : 3 ≤ b j) (hexcess_j : b j - 2 < p j) : i = j := by
  by_contra hij
  obtain ⟨hbi, hpi⟩ := higher_weight_excess_contact_rigidity hi hexcess_i
    (hlower i) (contact_contribution_lt_one hcoeff hbudget i)
  obtain ⟨hbj, hpj⟩ := higher_weight_excess_contact_rigidity hj hexcess_j
    (hlower j) (contact_contribution_lt_one hcoeff hbudget j)
  have hthird_i : (1 : 𝕜) / 3 ≤ coeff i := by
    convert hlower i using 1; norm_num [hbi]
  have hthird_j : (1 : 𝕜) / 3 ≤ coeff j := by
    convert hlower j using 1; norm_num [hbj]
  have hpair := two_contact_contributions_lt_one hcoeff hbudget hij
  rw [hpi, hpj] at hpair
  norm_num at hpair
  nlinarith

end KltDP.LinearAlgebra
