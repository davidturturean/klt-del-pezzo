import KltDP.Geometry.ModuleCohomologyRanks
import KltDP.LinearAlgebra.AlternatingDimensionSum
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Euler additivity for bounded finite-dimensional actual cohomology

The Euler value is the alternating `finsum` of dimensions of the original
base-field cohomology modules. For a coefficient module whose cohomology
vanishes above a supplied bound, it equals the corresponding finite sum.
The additivity theorem additionally assumes finite-dimensionality of every
actual cohomology group; no finrank interpretation is asserted without it.

Additivity follows from the previously proved linear long exact sequence,
rank-nullity and cancellation of the adjacent connecting-image dimensions.
Neither an Euler equality nor a cohomological exactness premise is added.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The finite alternating sum through degree `N` of actual base-field
cohomology dimensions. -/
def truncatedEuler (M : X.Modules) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)

/-- The alternating finite-support sum of actual cohomology dimensions.
The following theorems supply boundedness and finite-dimensionality when
this expression is used as the cohomological Euler characteristic. -/
def eulerCharacteristic (M : X.Modules) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)

theorem cohomologyDimension_eq_zero_of_subsingleton (M : X.Modules) (n : ℕ)
    [Subsingleton (H M n)] : cohomologyDimension f M n = 0 := by
  haveI : Subsingleton ((baseFunctor f n).obj M) :=
    inferInstanceAs (Subsingleton (H M n))
  exact Module.finrank_zero_of_subsingleton

/-- A genuine vanishing bound gives the finite sum for the same Euler value. -/
theorem eulerCharacteristic_eq_truncatedEuler (M : X.Modules) (N : ℕ)
    (hvanish : ∀ n, N < n → Subsingleton (H M n)) :
    eulerCharacteristic f M = truncatedEuler f M N := by
  unfold eulerCharacteristic truncatedEuler
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply Finset.mem_range.mpr
  by_contra hnot
  have hN : N < n := by omega
  letI : Subsingleton (H M n) := hvanish n hN
  have hz := cohomologyDimension_eq_zero_of_subsingleton f M n
  exact hn (by simp only [hz, Nat.cast_zero, mul_zero])

/-- The finite sum is independent of a chosen cohomological vanishing bound. -/
theorem truncatedEuler_eq_of_vanishing_bounds (M : X.Modules) (N N' : ℕ)
    (hN : ∀ n, N < n → Subsingleton (H M n))
    (hN' : ∀ n, N' < n → Subsingleton (H M n)) :
    truncatedEuler f M N = truncatedEuler f M N' :=
  (eulerCharacteristic_eq_truncatedEuler f M N hN).symm.trans
    (eulerCharacteristic_eq_truncatedEuler f M N' hN')

/-- The actual long exact sequence implies the finite Euler identity once
its upper connecting-map target vanishes. -/
theorem truncatedEuler_additive
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : ℕ)
    (hfinite₁ : ∀ n, FiniteDimensional k ((baseFunctor f n).obj S.X₁))
    (hfinite₂ : ∀ n, FiniteDimensional k ((baseFunctor f n).obj S.X₂))
    (hfinite₃ : ∀ n, FiniteDimensional k ((baseFunctor f n).obj S.X₃))
    [Subsingleton (H S.X₁ (N + 1))] :
    truncatedEuler f S.X₂ N = truncatedEuler f S.X₁ N + truncatedEuler f S.X₃ N := by
  unfold truncatedEuler
  apply KltDP.LinearAlgebra.AlternatingDimensionSum.alternating_sum_additive_of_boundary_zero
    (fun n => (cohomologyDimension f S.X₁ n : ℤ))
    (fun n => (cohomologyDimension f S.X₂ n : ℤ))
    (fun n => (cohomologyDimension f S.X₃ n : ℤ))
    (fun n => (connectingRank f S hS n : ℤ)) 0 ?_ ?_ N rfl ?_
  · letI := hfinite₁ 0
    letI := hfinite₂ 0
    letI := hfinite₃ 0
    simpa only [zero_add] using cohomology_dimension_rank_zero f S hS
  · intro n
    letI := hfinite₁ (n + 1)
    letI := hfinite₂ (n + 1)
    letI := hfinite₃ (n + 1)
    exact cohomology_dimension_rank_succ f S hS n
  · change (connectingRank f S hS N : ℤ) = 0
    simp only [connectingRank_eq_zero f S hS N, Nat.cast_zero]

/-- Euler characteristic is additive in an actual scheme-module short exact
sequence with finite-dimensional cohomology and an explicit vanishing bound. -/
theorem eulerCharacteristic_additive
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : ℕ)
    (hfinite₁ : ∀ n, FiniteDimensional k ((baseFunctor f n).obj S.X₁))
    (hfinite₂ : ∀ n, FiniteDimensional k ((baseFunctor f n).obj S.X₂))
    (hfinite₃ : ∀ n, FiniteDimensional k ((baseFunctor f n).obj S.X₃))
    (hvanish₁ : ∀ n, N < n → Subsingleton (H S.X₁ n))
    (hvanish₂ : ∀ n, N < n → Subsingleton (H S.X₂ n))
    (hvanish₃ : ∀ n, N < n → Subsingleton (H S.X₃ n)) :
    eulerCharacteristic f S.X₂ = eulerCharacteristic f S.X₁ +
      eulerCharacteristic f S.X₃ := by
  rw [eulerCharacteristic_eq_truncatedEuler f S.X₁ N hvanish₁,
    eulerCharacteristic_eq_truncatedEuler f S.X₂ N hvanish₂,
    eulerCharacteristic_eq_truncatedEuler f S.X₃ N hvanish₃]
  letI : Subsingleton (H S.X₁ (N + 1)) := hvanish₁ (N + 1) (Nat.lt_succ_self N)
  exact truncatedEuler_additive f S hS N hfinite₁ hfinite₂ hfinite₃

end KltDP.Geometry.ModuleCohomology
