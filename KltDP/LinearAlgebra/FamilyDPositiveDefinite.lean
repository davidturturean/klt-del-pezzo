import KltDP.LinearAlgebra.FamilyDNonvacuity
import KltDP.LinearAlgebra.FamilyDSourceReduction
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Positive definite family-D witnesses satisfying the source reduction

The actual rational quadratic form of each constructed ten-vertex graph
is the sum of its positive Euclidean square and nonnegative squares. This
proves positive definiteness without a determinant enumeration.

A cycle would have at least three edges, so the already proved two-edge
bound gives acyclicity. Actual reachability is controlled by the closed
canonical edge and the four isolated vertices. These facts instantiate
every hypothesis of `familyD_source_determinants` at both concrete graphs.

This is algebraic nonvacuity for that source reduction. No geometric surface,
exceptional divisor, or Picard-lattice realization is asserted.

Reuse: pinned `Matrix.PosDef`, `Finset.sum_pos'`, `sq_pos_of_ne_zero`,
`Walk.IsCycle.three_le_length`, and `Walk.IsTrail.length_le_card_edgeFinset`
supply the generic positivity and cycle facts. Current official Mathlib and
the cached positive-definite-tree library were reviewed; the latter's
integer-positivity adapter has a different input and needs no port here.
-/

namespace KltDP.LinearAlgebra.FamilyDNonvacuity

open Matrix SimpleGraph
open scoped BigOperators

/-- Symmetry comes from the actual undirected adjacency relation. -/
theorem gram_isHermitian (secondEdge : Bool) : (gram secondEdge).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  by_cases hij : i = j
  · subst j
    simp [gram, graphWeightMatrix_diagonal]
  · have hadj : (graph secondEdge).Adj j i ↔ (graph secondEdge).Adj i j :=
      ⟨fun h => h.symm, fun h => h.symm⟩
    simp only [gram, graphWeightMatrix_apply, if_neg hij, if_neg (Ne.symm hij),
      star_trivial, hadj]

private theorem finTen_sum (f : Fin 10 → ℚ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 +
      (f 5 + (f 6 + (f 7 + (f 8 + f 9)))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl

set_option maxHeartbeats 2000000 in
/-- An exact polynomial identity for every rational vector, with no finite
sampling of vectors or determinant computation. -/
theorem quadratic_form (secondEdge : Bool) (x : Fin 10 → ℚ) :
    dotProduct x (gram secondEdge *ᵥ x) =
      dotProduct x x + (x 0 - x 1) ^ 2 +
        2 * ((x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2) +
        (if secondEdge then (x 6 - x 7) ^ 2 else (x 6) ^ 2 + (x 7) ^ 2) +
        (x 8) ^ 2 + (x 9) ^ 2 := by
  cases secondEdge <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
      finTen_sum, weight, heavyVertices, Finset.mem_insert, Finset.mem_singleton,
      graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, Nat.cast_ofNat] <;>
    norm_num <;> ring

/-- Both actual D1 and D2 exceptional matrices are positive definite. -/
theorem gram_posDef (secondEdge : Bool) : (gram secondEdge).PosDef := by
  refine ⟨gram_isHermitian secondEdge, ?_⟩
  intro x hx
  have hpositive : 0 < ∑ i : Fin 10, (x i)^2 := by
    apply Finset.sum_pos'
    · intro i _
      exact sq_nonneg (x i)
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hbase : 0 < dotProduct x x := by
    simpa only [dotProduct, pow_two] using hpositive
  have hrest : 0 ≤ (x 0 - x 1) ^ 2 +
      2 * ((x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2) +
      (if secondEdge then (x 6 - x 7) ^ 2 else (x 6) ^ 2 + (x 7) ^ 2) +
      (x 8) ^ 2 + (x 9) ^ 2 := by
    cases secondEdge <;> positivity
  rw [show star x = x from star_trivial x, quadratic_form]
  linarith only [hbase, hrest]

/-- The actual edge bound rules out all cycles, using the minimum cycle
length and the injectivity of a trail's edge list. -/
theorem graph_isAcyclic (secondEdge : Bool) : (graph secondEdge).IsAcyclic := by
  intro v c hc
  have hmin := hc.three_le_length
  have hmax := hc.isTrail.length_le_card_edgeFinset
  have hbound := edge_card_le_two secondEdge
  omega

/-- The actual canonical connected component consists exactly of 0 and 1. -/
theorem canonical_reachable (secondEdge : Bool) (j : Fin 10) :
    (graph secondEdge).Reachable 0 j ↔ j = 0 ∨ j = 1 :=
  reachable_iff_of_mutual_singleton_neighbors (graph secondEdge) 0 1
    (canonical_adj secondEdge) (canonical_neighbors secondEdge).1
    (canonical_neighbors secondEdge).2 j

/-- Reachability from any of the four higher-weight vertices is equality,
proved from its actual isolation and the walk constructors. -/
theorem heavy_reachable (secondEdge : Bool) (i : Fin 10) (hi : i ∈ heavyVertices)
    (j : Fin 10) : (graph secondEdge).Reachable i j ↔ j = i := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact False.elim (heavy_isolated secondEdge i hi _ h)
  · intro h
    subst j
    exact SimpleGraph.Reachable.refl i

/-- The marked vertices belong to three different actual components. -/
theorem marked_components_separate (secondEdge : Bool) :
    ¬ (graph secondEdge).Reachable 0 2 ∧
      ¬ (graph secondEdge).Reachable 0 3 ∧
      ¬ (graph secondEdge).Reachable 2 3 := by
  rw [canonical_reachable, canonical_reachable,
    heavy_reachable secondEdge 2 (by decide)]
  decide

theorem canonical_component_weights (secondEdge : Bool) :
    ∀ j, (graph secondEdge).Reachable 0 j → weight j = 2 := by
  intro j hj
  rcases (canonical_reachable secondEdge j).mp hj with rfl | rfl
  · exact weight_values.1
  · exact weight_values.2.1

/-- Each actual isolated higher-weight component has exactly its one source
vertex; the condition on every other reachable vertex follows directly. -/
theorem heavy_single_source (secondEdge : Bool) (i : Fin 10) (hi : i ∈ heavyVertices) :
    ∀ j, (graph secondEdge).Reachable i j → j ≠ i → weight j = 2 := by
  intro j hj hne
  exact False.elim (hne ((heavy_reachable secondEdge i hi j).mp hj))

/-- The actual canonical row solution satisfies the source volume bound. -/
theorem source_budget (secondEdge : Bool) :
    -1 + dotProduct canonicalSource canonicalCoeff ≤
      1 - dotProduct marked canonicalCoeff := by
  have h := scalar_values secondEdge
  simp only [inverse_canonical] at h
  linarith only [h.1, h.2.1]

/-- The projection identity for the actual row solution and full inverse. -/
theorem source_projection (secondEdge : Bool) :
    (-1 + dotProduct canonicalSource canonicalCoeff) *
        (dotProduct marked ((gram secondEdge)⁻¹ *ᵥ marked) - 1) =
      (1 - dotProduct marked canonicalCoeff) ^ 2 := by
  simpa only [inverse_canonical] using projection_identity secondEdge

/-- The source-reduction conclusion holds for both explicit graphs.
Positive definiteness, acyclicity, actual component separation, the row
equation and both scalar hypotheses are proved above. The conclusion is
assembled from the actual inverse-source values and determinants. -/
theorem source_reduction_applies (secondEdge : Bool) :
    (1 - dotProduct marked canonicalCoeff = 1 / 3 ∧
      -1 + dotProduct canonicalSource canonicalCoeff = 1 / 3 ∧
      (gram secondEdge).det = 3888 ∧
      (borderedGram (gram secondEdge) marked (-1)).det = 1296) ∨
    (1 - dotProduct marked canonicalCoeff = 1 / 3 ∧
      -1 + dotProduct canonicalSource canonicalCoeff = 1 / 3 ∧
      (gram secondEdge).det = 2916 ∧
      (borderedGram (gram secondEdge) marked (-1)).det = 972) := by
  have hvalues := scalar_values secondEdge
  simp only [inverse_canonical] at hvalues
  have hdet := exceptional_det secondEdge
  have hborder := bordered_det secondEdge
  cases secondEdge
  · exact Or.inl ⟨hvalues.1, hvalues.2.1, hdet, hborder⟩
  · exact Or.inr ⟨hvalues.1, hvalues.2.1, hdet, hborder⟩

end KltDP.LinearAlgebra.FamilyDNonvacuity
