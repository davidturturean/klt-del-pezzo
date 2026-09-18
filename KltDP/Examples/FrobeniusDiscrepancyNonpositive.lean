import KltDP.Examples.FrobeniusDiscrepancyBounds

/-!
# Nonpositive coefficients of the original Frobenius discrepancy

Primality gives p ≥ 2, including characteristic two. The original integer
condition n > 2 gives n - 2 ≥ 1 over the rationals. The actual graph and
special-fibre coefficients are therefore nonpositive; every other prime
has coefficient zero. No positivity of the anticanonical divisor is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry FrobeniusMultiCentreSurface
open FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreContractingNef

/-- Every original prime has nonpositive discrepancy candidate coefficient,
for all of the original characteristics and all n > 2. -/
theorem candidate_coeff_nonpos
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
    (hn : 2 < n) (C : (sourceSurface q n a ha hproj).PrimeCurve) :
    candidate q n a ha hproj C ≤ 0 := by
  classical
  have hp : (2 : ℚ) ≤ ((q + 1 : ℕ) : ℚ) := by
    exact_mod_cast (Fact.out : (q + 1).Prime).two_le
  have hn' : (3 : ℚ) ≤ n := by
    exact_mod_cast (show 3 ≤ n from hn)
  have hr : (1 : ℚ) ≤ (n : ℚ) - 2 := by linarith
  have hpr : (2 : ℚ) ≤ ((q + 1 : ℕ) : ℚ) * ((n : ℚ) - 2) := by
    nlinarith
  by_cases hG : C = graphPrimeCurve q n a ha hproj
  · subst C
    rw [candidate_graph]
    exact neg_nonpos.mpr (div_nonneg (by linarith) (by linarith))
  · by_cases hF : ∃ i : Fin n, C = fiberPrimeCurve q n a ha hproj i
    · obtain ⟨i, rfl⟩ := hF
      rw [candidate_fiber]
      exact neg_nonpos.mpr (div_nonneg (by linarith) (by linarith))
    · rw [candidate_eq_zero_of_ne q n a ha hproj C hG (fun i h => hF ⟨i, h⟩)]

end KltDP.Examples.FrobeniusDiscrepancyBounds

#print axioms KltDP.Examples.FrobeniusDiscrepancyBounds.candidate_coeff_nonpos
