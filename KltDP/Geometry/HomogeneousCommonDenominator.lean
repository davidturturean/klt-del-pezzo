import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# One positive homogeneous degree and denominator for finitely many fractions

Given homogeneous numerator/denominator pairs, multiply by the other
denominators. One final selected coordinate makes the common degree
positive, including an empty family. Its evaluation is one, so every
original quotient is preserved. The common denominator stays nonzero.
-/

noncomputable section

open scoped BigOperators

namespace KltDP.Geometry.HomogeneousCommonDenominator

variable {R K σ ι : Type*} [CommRing R] [Field K] [Fintype ι]

/-- Finitely many equal-degree homogeneous fractions have one actual
nonzero homogeneous denominator and one positive common degree. -/
theorem exists_common (φ : MvPolynomial σ R →+* K) (j : σ)
    (hj : φ (MvPolynomial.X j) = 1) (d : ι → ℕ)
    (p q : ι → MvPolynomial σ R)
    (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hq : ∀ i, (q i).IsHomogeneous (d i))
    (hq0 : ∀ i, φ (q i) ≠ 0) :
    ∃ (D : ℕ) (P : ι → MvPolynomial σ R) (Q : MvPolynomial σ R),
      0 < D ∧ (∀ i, (P i).IsHomogeneous D) ∧ Q.IsHomogeneous D ∧
      φ Q ≠ 0 ∧ ∀ i, φ (P i) / φ Q = φ (p i) / φ (q i) := by
  classical
  refine ⟨(∑ i, d i) + 1,
    (fun i => p i * (∏ h ∈ Finset.univ.erase i, q h) * MvPolynomial.X j),
    (∏ i, q i) * MvPolynomial.X j, Nat.zero_lt_succ _, ?_, ?_, ?_, ?_⟩
  · intro i
    have hprod := MvPolynomial.IsHomogeneous.prod (Finset.univ.erase i) q d
      (fun h _ => hq h)
    simpa only [Finset.add_sum_erase Finset.univ d (Finset.mem_univ i)] using
      ((hp i).mul hprod).mul (MvPolynomial.isHomogeneous_X R j)
  · exact (MvPolynomial.IsHomogeneous.prod Finset.univ q d
      (fun i _ => hq i)).mul (MvPolynomial.isHomogeneous_X R j)
  · simp only [map_mul, map_prod, hj, mul_one]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i)
  · intro i
    simp only [map_mul, map_prod, hj, mul_one]
    rw [← Finset.mul_prod_erase Finset.univ (fun h => φ (q h)) (Finset.mem_univ i)]
    exact mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.mpr (fun h _ => hq0 h))

end KltDP.Geometry.HomogeneousCommonDenominator
