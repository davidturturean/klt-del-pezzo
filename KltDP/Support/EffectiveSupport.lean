import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Support obligation U-EFFECTIVE-SUPPORT: effective divisor support and the negativity mechanism

Plan contract (`U-EFFECTIVE-SUPPORT`): "If an effective integral divisor `Z` has zero
degree against a nef divisor, every prime component is null. If it has no exterior
components it is supported on the actual exceptional set. An effective divisor on a
negative-definite support cannot have nonnegative degree against all its
components [unless it is zero]."

Arithmetic clauses proved here, with degrees abstracted:

* `Σ a_i d_i = 0` with `a_i > 0` and `d_i ≥ 0` (nef degrees) forces every `d_i = 0`;
* if `Z = Σ a_i D_i` with `a_i ≥ 0` on a family with negative-definite Gram matrix
  `G` (the accepted convention: the negative matrix `-G` is `PosDef`), and
  `Z·D_i = (G a)_i ≥ 0` for all `i`, then `a = 0`: indeed
  `Z·Z = Σ a_i (Z·D_i) ≥ 0` while negative definiteness gives `Z·Z < 0` for `a ≠ 0`.

The identification of `d_i` and `G` with actual degrees and the actual
intersection matrix of the exceptional set, and the support statement for divisors
without exterior components, are the geometric obligations F02, F03, F06.
-/

namespace KltDP.Support

open Matrix
open scoped BigOperators

variable {ι 𝕜 : Type*} [Fintype ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Nef degree zero forces null components.** -/
theorem components_null_of_sum_eq_zero (a d : ι → 𝕜) (ha : ∀ i, 0 < a i) (hd : ∀ i, 0 ≤ d i)
    (h : ∑ i, a i * d i = 0) : ∀ i, d i = 0 := by
  have hterm : ∀ i, 0 ≤ a i * d i := fun i => mul_nonneg (le_of_lt (ha i)) (hd i)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).mp h
  intro i
  have := hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (ne_of_gt (ha i))
  · exact h0

/-- With the support restricted to a finite set `s` of components. -/
theorem components_null_of_sum_eq_zero_finset (s : Finset ι) (a d : ι → 𝕜)
    (ha : ∀ i ∈ s, 0 < a i) (hd : ∀ i ∈ s, 0 ≤ d i)
    (h : ∑ i ∈ s, a i * d i = 0) : ∀ i ∈ s, d i = 0 := by
  have hterm : ∀ i ∈ s, 0 ≤ a i * d i := fun i hi => mul_nonneg (le_of_lt (ha i hi)) (hd i hi)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h
  intro i hi
  rcases mul_eq_zero.mp (hzero i hi) with h0 | h0
  · exact absurd h0 (ne_of_gt (ha i hi))
  · exact h0

variable [StarRing 𝕜] [TrivialStar 𝕜]

/-- **The negativity mechanism.** If `-G` is positive definite (negative-definite
support), `a ≥ 0` coefficientwise, and `G a ≥ 0` coefficientwise (nonnegative degree
against every component), then `a = 0`. -/
theorem coefficients_eq_zero_of_negDef_of_degrees_nonneg (G : Matrix ι ι 𝕜)
    (hG : (-G).PosDef) (a : ι → 𝕜) (ha : ∀ i, 0 ≤ a i)
    (hdeg : ∀ i, 0 ≤ (G *ᵥ a) i) : a = 0 := by
  by_contra hne
  have hpos : 0 < dotProduct a ((-G) *ᵥ a) := by
    simpa only [star_trivial] using hG.2 a hne
  have hnonneg : 0 ≤ dotProduct a (G *ᵥ a) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hdeg i))
  rw [Matrix.neg_mulVec, dotProduct_neg] at hpos
  linarith

/-- **U-EFFECTIVE-SUPPORT**, arithmetic clauses. -/
theorem u_effective_support :
    (∀ (a d : ι → 𝕜), (∀ i, 0 < a i) → (∀ i, 0 ≤ d i) → ∑ i, a i * d i = 0 → ∀ i, d i = 0) ∧
    (∀ (G : Matrix ι ι 𝕜), (-G).PosDef → ∀ (a : ι → 𝕜), (∀ i, 0 ≤ a i) →
      (∀ i, 0 ≤ (G *ᵥ a) i) → a = 0) :=
  ⟨components_null_of_sum_eq_zero, coefficients_eq_zero_of_negDef_of_degrees_nonneg⟩

end KltDP.Support
