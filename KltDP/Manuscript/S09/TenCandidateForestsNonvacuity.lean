import KltDP.Manuscript.S09.TenCandidateForests
import KltDP.LinearAlgebra.TenForestNonvacuity

/-!
# Occurrence witnesses for the complete candidate-forest conclusion

The actual finite graphs from `TenForestNonvacuity` satisfy every original
hypothesis. Applying the named theorem to those same graphs gives all of
its marked graph, matrix and invariant data. The pre-existing realization
witness identifies the unique output row. No geometric occurrence is
asserted, and no new candidate graph or determinant is assumed here.
-/

namespace KltDP.Manuscript.S09

open Matrix SimpleGraph KltDP.LinearAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Apply the named theorem to the exact original hypothesis conjunction
used by the actual occurrence witnesses. This conjunction contains only
source inputs, with no classification or determinant conclusion. -/
theorem tenCandidateForests_of_originalHypotheses
    {G : SimpleGraph V} [DecidableRel G.Adj] {weight : V → ℕ} {coeff : V → ℚ}
    {C B D : V} {β : ℕ}
    (h : TenForestOriginalHypotheses G weight coeff C B D β) :
    β ≠ 5 ∧ ∃! row : TenForestRow,
      TenCandidateForestData row G weight coeff C B D β := by
  rcases h with ⟨hβ, hcard, hG, hC, hB, hD, hother, hextra, hCB, hCD, hBD,
    hseparate, hdegC, hdeg, hedges, hboundary, hA, hsolve, hcoeff, hv, hbudget, hproj⟩
  exact tenCandidateForests G weight coeff C B D β hβ hcard hG hC hB hD hother
    hextra hCB hCD hBD hseparate hdegC hdeg hedges hboundary hA hsolve hcoeff hv hbudget hproj

/-- Every one of the ten labels occurs on an actual finite weighted forest
satisfying all original hypotheses and the complete named conclusion.
The same graph and adjacency decision procedure occur in both conjuncts. -/
theorem tenCandidateForests_all_rows_nonvacuous (row : TenForestRow) :
    ∃ (G : SimpleGraph (Fin (row.beta + 7))) (adj : DecidableRel G.Adj)
      (weight : Fin (row.beta + 7) → ℕ) (coeff : Fin (row.beta + 7) → ℚ)
      (C B D : Fin (row.beta + 7)),
      letI : DecidableRel G.Adj := adj
      TenForestOriginalHypotheses G weight coeff C B D row.beta ∧
        TenCandidateForestData row G weight coeff C B D row.beta := by
  obtain ⟨G, adj, weight, coeff, C, B, D, hsource, hreal⟩ :=
    ten_forest_all_rows_nonvacuous row
  letI : DecidableRel G.Adj := adj
  obtain ⟨_, actual, hdata, _⟩ := tenCandidateForests_of_originalHypotheses hsource
  have hrow : actual = row := hdata.1.unique hreal
  subst actual
  exact ⟨G, adj, weight, coeff, C, B, D, hsource, hdata⟩

end KltDP.Manuscript.S09
