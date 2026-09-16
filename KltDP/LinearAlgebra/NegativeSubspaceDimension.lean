import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Negative families and a positive vector

The dimension contradiction at the end of the isolated-node cover argument
needs an actual positive vector, together with the actual negative family.
It does not require a second invocation of the Hodge index theorem.

These are bilinear-space lemmas only. They construct no surface, cover,
ample class, or exceptional curve. Pinned Mathlib supplies finite linear
combinations, their span, linear independence, and the strict dimension
bound for a proper submodule; all are imported without a source port.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Module Submodule
open scoped BigOperators

universe u v w

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A subspace on which the form is nonpositive cannot contain a positive
vector, and consequently has strictly smaller dimension. -/
theorem nonpositive_submodule_finrank_lt [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (W : Submodule K V)
    (hW : ∀ x ∈ W, B x x ≤ 0) (hpositive : ∃ x : V, 0 < B x x) :
    Module.finrank K W < Module.finrank K V := by
  apply Submodule.finrank_lt
  intro htop
  obtain ⟨x, hx⟩ := hpositive
  have hxW : x ∈ W := by rw [htop]; trivial
  exact (not_le_of_gt hx) (hW x hxW)

/-- Strict negativity for every nonzero coefficient vector gives linear
independence of the actual vectors, rather than requiring it separately. -/
theorem linearIndependent_of_negative_combinations
    {ι : Type w} [Fintype ι] (B : LinearMap.BilinForm K V) (v : ι → V)
    (hnegative : ∀ c : ι → K, c ≠ 0 →
      B (∑ i, c i • v i) (∑ i, c i • v i) < 0) :
    LinearIndependent K v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hczero : c = 0 := by
    by_contra hn
    have h := hnegative c hn
    rw [hc, map_zero] at h
    exact (lt_irrefl 0) h
  exact congrFun hczero i

/-- The span of a strictly negative family has fewer dimensions than an
ambient bilinear space containing an actual positive vector. -/
theorem negative_combinations_card_lt_finrank [FiniteDimensional K V]
    {ι : Type w} [Fintype ι] (B : LinearMap.BilinForm K V) (v : ι → V)
    (hnegative : ∀ c : ι → K, c ≠ 0 →
      B (∑ i, c i • v i) (∑ i, c i • v i) < 0)
    (hpositive : ∃ x : V, 0 < B x x) :
    Fintype.card ι < Module.finrank K V := by
  have hli := linearIndependent_of_negative_combinations B v hnegative
  rw [← finrank_span_eq_card hli]
  apply nonpositive_submodule_finrank_lt B _ _ hpositive
  intro x hx
  rw [← Fintype.range_linearCombination] at hx
  obtain ⟨c, rfl⟩ := hx
  by_cases hc : c = 0
  · subst c
    simp only [map_zero, LinearMap.zero_apply, le_refl]
  · exact (hnegative c hc).le

/-- In particular a strictly negative family cannot have the full ambient
dimension when a positive vector exists. -/
theorem negative_combinations_card_ne_finrank [FiniteDimensional K V]
    {ι : Type w} [Fintype ι] (B : LinearMap.BilinForm K V) (v : ι → V)
    (hnegative : ∀ c : ι → K, c ≠ 0 →
      B (∑ i, c i • v i) (∑ i, c i • v i) < 0)
    (hpositive : ∃ x : V, 0 < B x x) :
    Fintype.card ι ≠ Module.finrank K V :=
  ne_of_lt (negative_combinations_card_lt_finrank B v hnegative hpositive)

end KltDP.LinearAlgebra
