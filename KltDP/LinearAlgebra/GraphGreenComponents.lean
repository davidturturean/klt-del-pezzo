import KltDP.LinearAlgebra.BetaThreeCoreContact
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Green entries of actual graph components

The matrix is the actual diagonal-minus-adjacency matrix. The zero entries
between different connected components are derived by the pinned Mathlib
block-inverse theorem. Canonical coefficients and the marked energy then
split over actual components, without a block decomposition as a premise.

The diagonal Green bound includes its equality case: equality holds exactly
at an isolated vertex. This is the rigidity used in the C/D/E classification.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V] [Field 𝕜]

/-- The component of an actual vertex defines a triangular two-block
partition of the actual weighted graph matrix. -/
theorem graphWeightMatrix_component_triangular
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜) (root : V) :
    (graphWeightMatrix G weight).BlockTriangular
      (fun v => if G.Reachable root v then (0 : ℕ) else 1) := by
  classical
  intro i j hij
  by_cases hi : G.Reachable root i
  · simp only [if_pos hi] at hij
    exact (Nat.not_lt_zero _ hij).elim
  · by_cases hj : G.Reachable root j
    · have hne : i ≠ j := by intro h; subst j; exact hi hj
      have hnadj : ¬ G.Adj i j := by
        intro hadj
        exact hi (hj.trans hadj.symm.reachable)
      simp only [graphWeightMatrix_apply, if_neg hne, if_neg hnadj]
    · simp only [if_neg hi, if_neg hj] at hij
      exact (Nat.lt_irrefl 1 hij).elim

/-- Entries of the full inverse vanish between genuinely disconnected
vertices. Invertibility is enough; positivity is not needed here. -/
theorem graph_inverse_eq_zero_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : IsUnit (graphWeightMatrix G weight)) {i j : V}
    (hij : ¬ G.Reachable i j) : (graphWeightMatrix G weight)⁻¹ i j = 0 := by
  classical
  letI : Invertible (graphWeightMatrix G weight) := hA.invertible
  have htri := Matrix.blockTriangular_inv_of_blockTriangular
    (graphWeightMatrix_component_triangular G weight j)
  apply htri
  have hji : ¬ G.Reachable j i := fun h => hij h.symm
  simp only [if_neg hji, if_pos (SimpleGraph.Reachable.refl j)]
  norm_num

/-- When every other vertex of a component has weight two, its root's
canonical coefficient is its own source times the diagonal Green entry.
The source elsewhere in the graph is unrestricted. -/
theorem graph_single_source_coefficient
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (root : V)
    (hother : ∀ v, G.Reachable root v → v ≠ root → weight v = 2) :
    coeff root = (weight root - 2) * (graphWeightMatrix G weight)⁻¹ root root := by
  classical
  let A := graphWeightMatrix G weight
  letI : Invertible A := hA.invertible
  have hcoeff : A⁻¹ *ᵥ (fun i => weight i - 2) = coeff := by
    rw [← hrow, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  rw [← hcoeff]
  change (∑ v, A⁻¹ root v * (weight v - 2)) = _
  rw [Finset.sum_eq_single root]
  · ring
  · intro v _ hvr
    by_cases hrv : G.Reachable root v
    · rw [hother v hrv hvr, sub_self, mul_zero]
    · rw [graph_inverse_eq_zero_of_not_reachable G weight hA hrv, zero_mul]
  · simp

/-- A wholly weight-two component has zero canonical coefficients even
when other components carry nonzero canonical source. -/
theorem graph_canonical_component_coefficient_zero
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (root : V) (hcanonical : ∀ v, G.Reachable root v → weight v = 2) :
    coeff root = 0 := by
  rw [graph_single_source_coefficient G weight coeff hA hrow root
    (fun v hv _ => hcanonical v hv),
    hcanonical root (SimpleGraph.Reachable.refl root), sub_self, zero_mul]

/-- The energy of three marked vertices in three actual components is the
sum of the three diagonal Green entries of the full inverse. -/
theorem graph_separated_marked_energy
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : IsUnit (graphWeightMatrix G weight)) (C B D : V)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hBD : ¬ G.Reachable B D) :
    dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) =
      (graphWeightMatrix G weight)⁻¹ C C +
        (graphWeightMatrix G weight)⁻¹ B B +
          (graphWeightMatrix G weight)⁻¹ D D := by
  have hBC : ¬ G.Reachable B C := fun h => hCB h.symm
  have hDC : ¬ G.Reachable D C := fun h => hCD h.symm
  have hDB : ¬ G.Reachable D B := fun h => hBD h.symm
  rw [threeMarkedSource_dotProduct]
  simp only [threeMarkedSource, Matrix.mulVec_add, Pi.add_apply,
    Matrix.mulVec_single_one, Matrix.transpose_apply,
    graph_inverse_eq_zero_of_not_reachable G weight hA hCB,
    graph_inverse_eq_zero_of_not_reachable G weight hA hCD,
    graph_inverse_eq_zero_of_not_reachable G weight hA hBC,
    graph_inverse_eq_zero_of_not_reachable G weight hA hBD,
    graph_inverse_eq_zero_of_not_reachable G weight hA hDC,
    graph_inverse_eq_zero_of_not_reachable G weight hA hDB, add_zero, zero_add]

section Ordered

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]

/-- The nonzero off-diagonal graph of the actual graph matrix is exactly
the supplied graph. This identifies the strict Stieltjes positivity graph. -/
theorem graphWeightMatrix_nonzero_graph
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef) :
    nonzeroOffDiagonalGraph (graphWeightMatrix G weight) = G := by
  ext i j
  rw [nonzeroOffDiagonalGraph_adj_iff hA.1]
  by_cases hij : i = j
  · subst j
    simp
  · simp only [graphWeightMatrix_apply, if_neg hij, hij, true_and]
    by_cases hadj : G.Adj i j <;> simp [hadj, hij]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] in
/-- The diagonal row of the actual inverse is an exact neighbor sum. -/
theorem graph_inverse_diagonal_row
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : IsUnit (graphWeightMatrix G weight)) (root : V) :
    weight root * (graphWeightMatrix G weight)⁻¹ root root -
      (∑ u ∈ G.neighborFinset root, (graphWeightMatrix G weight)⁻¹ u root) = 1 := by
  let A := graphWeightMatrix G weight
  letI : Invertible A := hA.invertible
  have hrow : A *ᵥ (A⁻¹ *ᵥ Pi.single root 1) = Pi.single root 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have h := congrFun hrow root
  rw [graphWeightMatrix_mulVec_apply] at h
  simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply, Pi.single_eq_same] using h

/-- Every diagonal Green entry is at least the reciprocal of its actual
positive vertex weight. -/
theorem graph_inverse_diagonal_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef) (root : V)
    (hweight : 0 < weight root) :
    1 / weight root ≤ (graphWeightMatrix G weight)⁻¹ root root := by
  have hrow := graph_inverse_diagonal_row G weight (isUnit_of_posDef hA) root
  have hsum : 0 ≤ ∑ u ∈ G.neighborFinset root,
      (graphWeightMatrix G weight)⁻¹ u root :=
    Finset.sum_nonneg fun u _ =>
      stieltjes_inverse_nonnegative hA (graphWeightMatrix_offDiagonal G weight) u root
  apply (div_le_iff₀ hweight).mpr
  nlinarith only [hrow, hsum]

/-- Equality in the diagonal Green lower bound is equivalent to actual
isolation. An incident edge gives a strictly positive inverse contribution. -/
theorem graph_inverse_diagonal_eq_iff_isolated
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → 𝕜)
    (hA : (graphWeightMatrix G weight).PosDef) (root : V)
    (hweight : 0 < weight root) :
    (graphWeightMatrix G weight)⁻¹ root root = 1 / weight root ↔
      ∀ u, ¬ G.Adj root u := by
  have hrow := graph_inverse_diagonal_row G weight (isUnit_of_posDef hA) root
  constructor
  · intro heq u hadj
    have hzero : (∑ v ∈ G.neighborFinset root,
        (graphWeightMatrix G weight)⁻¹ v root) = 0 := by
      rw [heq, mul_one_div_cancel hweight.ne'] at hrow
      linarith only [hrow]
    have hle := Finset.single_le_sum
      (fun v (_ : v ∈ G.neighborFinset root) =>
        stieltjes_inverse_nonnegative hA (graphWeightMatrix_offDiagonal G weight) v root)
      ((G.mem_neighborFinset root u).mpr hadj)
    have hpath : (nonzeroOffDiagonalGraph (graphWeightMatrix G weight)).Reachable u root := by
      rw [graphWeightMatrix_nonzero_graph G weight hA]
      exact hadj.symm.reachable
    have hpos := stieltjes_inverse_positive_of_reachable hA
      (graphWeightMatrix_offDiagonal G weight) hpath
    rw [hzero] at hle
    exact (not_le_of_gt hpos) hle
  · intro hisolated
    have hsum : (∑ u ∈ G.neighborFinset root,
        (graphWeightMatrix G weight)⁻¹ u root) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      exact (hisolated u ((G.mem_neighborFinset root u).mp hu)).elim
    rw [hsum, sub_zero] at hrow
    apply (eq_div_iff hweight.ne').mpr
    simpa only [mul_comm] using hrow

end Ordered

end KltDP.LinearAlgebra
