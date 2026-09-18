import KltDP.Examples.FrobeniusDiscrepancyPrimeSeparation
import Mathlib.Tactic.Linarith

/-!
The coefficients of the explicit original rational divisor are computed at
the graph, each special fibre, and every other original prime. Actual prime
separation makes the fibre sum multiplicity one and gives coefficient zero
on every old exceptional component. At n > 2 every coefficient exceeds -1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves FrobeniusMultiCentreExceptionalPrime
open FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

private theorem fiber_sum_at_graph :
    (∑ i : Fin n, Finsupp.single (fiberPrimeCurve q n a ha hproj i) (1 : ℤ))
      (graphPrimeCurve q n a ha hproj) = 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun i _ =>
    Finsupp.single_eq_of_ne (graph_ne_fiber q n a ha hproj i).symm

private theorem fiber_sum_at_fiber (i : Fin n) :
    (∑ j : Fin n, Finsupp.single (fiberPrimeCurve q n a ha hproj j) (1 : ℤ))
      (fiberPrimeCurve q n a ha hproj i) = 1 := by
  classical
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply,
    (fiber_injective q n a ha hproj).eq_iff]

/-- The original graph occurs with exactly the stated rational coefficient. -/
theorem candidate_graph :
    candidate q n a ha hproj (graphPrimeCurve q n a ha hproj) =
      (let p : ℚ := ((q + 1 : ℕ) : ℚ);
       let r : ℚ := (n : ℚ) - 2;
       -((p * r - 2) / (p * r))) := by
  simp only [candidate, Finsupp.sub_apply, Finsupp.smul_apply,
    rationalizeWeilDivisor_apply, Finsupp.single_eq_same,
    fiber_sum_at_graph, Int.cast_one, Int.cast_zero, smul_eq_mul,
    mul_one, mul_zero, sub_zero]

/-- Each original special fibre occurs once, with the stated rational coefficient. -/
theorem candidate_fiber (i : Fin n) :
    candidate q n a ha hproj (fiberPrimeCurve q n a ha hproj i) =
      (let p : ℚ := ((q + 1 : ℕ) : ℚ);
       -((p - 2) / p)) := by
  simp only [candidate, Finsupp.sub_apply, Finsupp.smul_apply,
    rationalizeWeilDivisor_apply,
    Finsupp.single_eq_of_ne (graph_ne_fiber q n a ha hproj i),
    fiber_sum_at_fiber, Int.cast_one, Int.cast_zero, smul_eq_mul,
    mul_one, mul_zero, zero_sub]

/-- Every prime outside the original graph and original strict special fibres
has coefficient zero. -/
theorem candidate_eq_zero_of_ne (C : (sourceSurface q n a ha hproj).PrimeCurve)
    (hG : C ≠ graphPrimeCurve q n a ha hproj)
    (hF : ∀ i : Fin n, C ≠ fiberPrimeCurve q n a ha hproj i) :
    candidate q n a ha hproj C = 0 := by
  classical
  have hs :
      (∑ i : Fin n, Finsupp.single (fiberPrimeCurve q n a ha hproj i) (1 : ℤ)) C = 0 := by
    rw [Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun i _ => Finsupp.single_eq_of_ne (hF i).symm
  simp only [candidate, Finsupp.sub_apply, Finsupp.smul_apply,
    rationalizeWeilDivisor_apply, Finsupp.single_eq_of_ne hG.symm,
    hs, Int.cast_zero, smul_zero, sub_zero]

/-- The actual prime support is contained in the original graph and special fibres. -/
theorem candidate_support_subset :
    ((candidate q n a ha hproj).support :
        Set (sourceSurface q n a ha hproj).PrimeCurve) ⊆
      {graphPrimeCurve q n a ha hproj} ∪ Set.range (fiberPrimeCurve q n a ha hproj) := by
  intro C hC
  by_contra hnot
  have hG : C ≠ graphPrimeCurve q n a ha hproj := by
    intro h
    exact hnot (Or.inl h)
  have hF : ∀ i : Fin n, C ≠ fiberPrimeCurve q n a ha hproj i := by
    intro i h
    exact hnot (Or.inr ⟨i, h.symm⟩)
  exact (Finsupp.mem_support_iff.mp hC) (candidate_eq_zero_of_ne q n a ha hproj C hG hF)

/-- Every original old exceptional component has coefficient exactly zero. -/
theorem candidate_old_exceptional_eq_zero (i : Fin n) (j : Fin q) :
    candidate q n a ha hproj (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj) = 0 :=
  candidate_eq_zero_of_ne q n a ha hproj _
    (graph_ne_old q n a ha hproj i j).symm
    (fun l => (fiber_ne_old q n a ha hproj i j l).symm)

/-- Every original prime coefficient of the explicit rational divisor is greater than -1. -/
theorem candidate_coeff_gt_neg_one (hn : 2 < n)
    (C : (sourceSurface q n a ha hproj).PrimeCurve) :
    (-1 : ℚ) < candidate q n a ha hproj C := by
  classical
  have hp : (0 : ℚ) < ((q + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_pos q
  have hn' : (2 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hr : (0 : ℚ) < (n : ℚ) - 2 := by linarith
  have hgraph :
      ((((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2) - 2) /
        (((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2))) < 1 :=
    (div_lt_one (mul_pos hp hr)).mpr (by linarith)
  have hfiber : ((((q + 1 : ℕ) : ℚ) - 2) / ((q + 1 : ℕ) : ℚ)) < 1 :=
    (div_lt_one hp).mpr (by linarith)
  by_cases hG : C = graphPrimeCurve q n a ha hproj
  · subst C
    rw [candidate_graph]
    exact neg_lt_neg hgraph
  · by_cases hF : ∃ i : Fin n, C = fiberPrimeCurve q n a ha hproj i
    · obtain ⟨i, rfl⟩ := hF
      rw [candidate_fiber]
      exact neg_lt_neg hfiber
    · rw [candidate_eq_zero_of_ne q n a ha hproj C hG (fun i h => hF ⟨i, h⟩)]
      norm_num

end KltDP.Examples.FrobeniusDiscrepancyBounds
