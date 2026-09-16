/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Independence from a negative pairing and a positive functional

This bounded adaptation follows the positive/negative coefficient argument in
`LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero`, Mathlib commit
`0a52a37b7f2fec42206095e832902a281edf9f3f`,
`Mathlib/LinearAlgebra/QuadraticForm/Dual.lean`, lines 164–195.
That theorem is absent from the project's pinned Mathlib. Here the form is
negative definite only on the original family's span; no symmetry, finite
dimensionality, or finiteness of the index type is required.
-/

namespace KltDP.LinearAlgebra.NegativePairingPositiveFunctional

open scoped BigOperators

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {ι : Type v}

private lemma positive_part_sub_negative_part (r : ℚ) :
    max r 0 - max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), sub_zero]
  · have hr' : r ≤ 0 := le_of_lt (lt_of_not_ge hr)
    rw [max_eq_right hr', max_eq_left (neg_nonneg.mpr hr')]
    simp

/-- A negative definite span with nonnegative pairings between different family
members admits no relation when a linear functional is positive on each member. -/
theorem linearIndependent (B : LinearMap.BilinForm ℚ V) (ℓ : V →ₗ[ℚ] ℚ)
    (v : ι → V)
    (hnegative : ∀ c ∈ Submodule.span ℚ (Set.range v), c ≠ 0 → B c c < 0)
    (hoff : Pairwise fun i j => 0 ≤ B (v i) (v j))
    (hpositive : ∀ i, 0 < ℓ (v i)) : LinearIndependent ℚ v := by
  classical
  refine linearIndependent_iff'.mpr fun s c hc => ?_
  let p : ι → ℚ := fun i => max (c i) 0
  let q : ι → ℚ := fun i => max (-c i) 0
  let u : V := ∑ i ∈ s, p i • v i
  let w : V := ∑ i ∈ s, q i • v i
  have hp (i : ι) : 0 ≤ p i := le_max_right _ _
  have hq (i : ι) : 0 ≤ q i := le_max_right _ _
  have hpq (i : ι) : p i - q i = c i := positive_part_sub_negative_part (c i)
  have huw : u = w := by
    apply sub_eq_zero.mp
    calc
      u - w = ∑ i ∈ s, (p i - q i) • v i := by
        simp only [u, w, sub_smul, Finset.sum_sub_distrib]
      _ = ∑ i ∈ s, c i • v i := by simp only [hpq]
      _ = 0 := hc
  have hmix : 0 ≤ B u w := by
    dsimp only [u, w]
    rw [LinearMap.map_sum₂]
    simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    by_cases hij : i = j
    · subst j
      by_cases hci : 0 ≤ c i
      · simp [q, max_eq_right (neg_nonpos.mpr hci)]
      · simp [p, max_eq_right (le_of_lt (lt_of_not_ge hci))]
    · exact mul_nonneg (hq j) (mul_nonneg (hp i) (hoff hij))
  have hu_mem : u ∈ Submodule.span ℚ (Set.range v) := by
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hu : u = 0 := by
    by_cases hu0 : u = 0
    · exact hu0
    · have hnonnegative : 0 ≤ B u u := by simpa only [huw] using hmix
      exact False.elim ((not_lt_of_ge hnonnegative) (hnegative u hu_mem hu0))
  have hw : w = 0 := huw.symm.trans hu
  have H (a : ι → ℚ) (ha : ∀ i, 0 ≤ a i)
      (hzero : ∑ i ∈ s, a i • v i = 0) : ∀ i ∈ s, a i = 0 := by
    have hsum : ∑ i ∈ s, a i * ℓ (v i) = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg ℓ hzero
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => mul_nonneg (ha i) (le_of_lt (hpositive i)))).mp hsum
    intro i hi
    exact (mul_eq_zero.mp (hterms i hi)).resolve_right (ne_of_gt (hpositive i))
  intro i hi
  have hpi := H p hp hu i hi
  have hqi := H q hq hw i hi
  simpa only [hpi, hqi, sub_self] using (hpq i).symm

end KltDP.LinearAlgebra.NegativePairingPositiveFunctional
