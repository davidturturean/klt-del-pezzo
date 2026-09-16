import Mathlib.Tactic

/-!
# Support obligation U-SECTION-COUNT: section-only ruling bounds including `s = 1`

Manuscript `source/manuscript.tex` lines 2242–2264 (proof of Theorem 7.5
`thm:two-contact-ruling`, all-section case), using the count formula of Lemma 7.1
(`lem:forest-count`): `#π₀(D) = s + Σ_t (r_t - a_t) - q_h`.

Arithmetic clauses proved here, with the fiber data abstracted to integers:

* **`s ≥ 2`.** The distinguished fiber contributes `r_0 - a_0 = 2 - s`; every other
  one-exterior-component fiber contributes at most `2 - s ≤ 0`; each of the exactly
  `s - 1` two-exterior-component fibers contributes at most `1`; `q_h ≥ 0`. Hence
  `#π₀(D) ≤ s + (2 - s) + (s - 1) = s + 1`, and `s ≤ 6` gives `#π₀(D) ≤ 7`.
* **`s = 1`.** At most three reducible fibers occur, each contributing at most `1`,
  so `#π₀(D) ≤ 1 + 3 = 4`. This case is treated separately: the bound
  `2 - s ≤ 0` used above fails for `s = 1`.

Not proved here: the count formula itself for the actual ruling (Lemma 7.1), the
incidence facts `a_t = s`, `r_t ≤ 2`, `r_0 = 2`, the exact number `s - 1` of
two-exterior-component fibers, `s ≤ 6` from Lemma 4.4, positivity of `s`, and the
three-edge bound for `s = 1` (F17, F25, U-FIBER-FACTS, U-REDUCIBLE-FINITE).
-/

namespace KltDP.Support

open scoped BigOperators

/-- **Case `s ≥ 2`.** With the distinguished fiber `t₀`, other one-exterior-component
fibers `O`, and `s - 1` two-exterior-component fibers `W` (pairwise disjoint), the
count `s + Σ c_t - q_h` is at most `s + 1`. -/
theorem section_count_le_succ {ι : Type*} [DecidableEq ι] (s : ℕ) (hs : 2 ≤ s)
    (t₀ : ι) (O W : Finset ι) (c : ι → ℤ) (q : ℤ) (hq : 0 ≤ q)
    (ht₀O : t₀ ∉ O) (ht₀W : t₀ ∉ W) (hOW : Disjoint O W)
    (hc₀ : c t₀ = 2 - (s : ℤ)) (hO : ∀ t ∈ O, c t ≤ 2 - (s : ℤ)) (hW : ∀ t ∈ W, c t ≤ 1)
    (hWcard : W.card = s - 1) :
    (s : ℤ) + ∑ t ∈ insert t₀ (O ∪ W), c t - q ≤ (s : ℤ) + 1 := by
  have hnot : t₀ ∉ O ∪ W := by simp [ht₀O, ht₀W]
  rw [Finset.sum_insert hnot, Finset.sum_union hOW, hc₀]
  have hOsum : ∑ t ∈ O, c t ≤ 0 := by
    calc ∑ t ∈ O, c t ≤ ∑ t ∈ O, (2 - (s : ℤ)) := Finset.sum_le_sum hO
      _ = O.card • (2 - (s : ℤ)) := by rw [Finset.sum_const]
      _ ≤ 0 := by
        rw [nsmul_eq_mul]
        have : (2 : ℤ) - s ≤ 0 := by
          have : (2 : ℤ) ≤ s := by exact_mod_cast hs
          linarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have hWsum : ∑ t ∈ W, c t ≤ (s : ℤ) - 1 := by
    calc ∑ t ∈ W, c t ≤ ∑ t ∈ W, (1 : ℤ) := Finset.sum_le_sum hW
      _ = W.card := by simp
      _ = (s : ℤ) - 1 := by
        rw [hWcard]
        have : 1 ≤ s := by omega
        push_cast [Nat.cast_sub this]
        ring
  linarith

/-- With `s ≤ 6` (Lemma 4.4), the all-section count is at most seven. -/
theorem section_count_le_seven {ι : Type*} [DecidableEq ι] (s : ℕ) (hs : 2 ≤ s) (hs6 : s ≤ 6)
    (t₀ : ι) (O W : Finset ι) (c : ι → ℤ) (q : ℤ) (hq : 0 ≤ q)
    (ht₀O : t₀ ∉ O) (ht₀W : t₀ ∉ W) (hOW : Disjoint O W)
    (hc₀ : c t₀ = 2 - (s : ℤ)) (hO : ∀ t ∈ O, c t ≤ 2 - (s : ℤ)) (hW : ∀ t ∈ W, c t ≤ 1)
    (hWcard : W.card = s - 1) :
    (s : ℤ) + ∑ t ∈ insert t₀ (O ∪ W), c t - q ≤ 7 := by
  have := section_count_le_succ s hs t₀ O W c q hq ht₀O ht₀W hOW hc₀ hO hW hWcard
  have : (s : ℤ) ≤ 6 := by exact_mod_cast hs6
  linarith

/-- **Case `s = 1`.** At most three reducible fibers, each contributing at most one:
the count is at most four. -/
theorem section_count_one {ι : Type*} (T : Finset ι) (hT : T.card ≤ 3) (c : ι → ℤ)
    (hc : ∀ t ∈ T, c t ≤ 1) (q : ℤ) (hq : 0 ≤ q) :
    (1 : ℤ) + ∑ t ∈ T, c t - q ≤ 4 := by
  have : ∑ t ∈ T, c t ≤ T.card := by
    calc ∑ t ∈ T, c t ≤ ∑ t ∈ T, (1 : ℤ) := Finset.sum_le_sum hc
      _ = T.card := by simp
  have : (T.card : ℤ) ≤ 3 := by exact_mod_cast hT
  linarith

/-- **U-SECTION-COUNT**, arithmetic clause. -/
theorem u_section_count :
    (∀ {ι : Type} [DecidableEq ι] (s : ℕ), 2 ≤ s → s ≤ 6 →
      ∀ (t₀ : ι) (O W : Finset ι) (c : ι → ℤ) (q : ℤ), 0 ≤ q →
        t₀ ∉ O → t₀ ∉ W → Disjoint O W →
        c t₀ = 2 - (s : ℤ) → (∀ t ∈ O, c t ≤ 2 - (s : ℤ)) → (∀ t ∈ W, c t ≤ 1) →
        W.card = s - 1 →
        (s : ℤ) + ∑ t ∈ insert t₀ (O ∪ W), c t - q ≤ (s : ℤ) + 1 ∧
        (s : ℤ) + ∑ t ∈ insert t₀ (O ∪ W), c t - q ≤ 7) ∧
    (∀ {ι : Type} (T : Finset ι), T.card ≤ 3 → ∀ (c : ι → ℤ), (∀ t ∈ T, c t ≤ 1) →
      ∀ q : ℤ, 0 ≤ q → (1 : ℤ) + ∑ t ∈ T, c t - q ≤ 4) :=
  ⟨fun s hs hs6 t₀ O W c q hq h1 h2 h3 h4 h5 h6 h7 =>
    ⟨section_count_le_succ s hs t₀ O W c q hq h1 h2 h3 h4 h5 h6 h7,
      section_count_le_seven s hs hs6 t₀ O W c q hq h1 h2 h3 h4 h5 h6 h7⟩,
    fun T hT c hc q hq => section_count_one T hT c hc q hq⟩

end KltDP.Support
