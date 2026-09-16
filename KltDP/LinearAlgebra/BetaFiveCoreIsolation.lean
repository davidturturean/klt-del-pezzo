import KltDP.LinearAlgebra.GraphPathConcavity
import KltDP.LinearAlgebra.BetaThreeCoreContact

/-!
# Isolation of both distinguished higher-weight vertices when beta is five

The actual full canonical row equation with nonnegative coefficients gives
the usual diagonal lower bounds. An actual canonical neighbor improves a
weight-three root to coefficient at least 2/5 and a weight-five root to
coefficient at least 2/3. Either bound contradicts positive marked length
when combined with the other core's diagonal lower bound.

Only the actual one-heavy-vertex component hypotheses identify a neighbor
as canonical. No Green cap, scalar classification, or isolation is assumed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V 𝕜 : Type*} [Fintype V] [DecidableEq V]
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Keeping one actual neighbor term in the full canonical row equation
gives a stronger bound than discarding the entire nonnegative neighbor sum. -/
theorem graph_neighbor_row_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (v u : V) (hvu : G.Adj v u) :
    weight v - 2 + coeff u ≤ weight v * coeff v := by
  have hsum := Finset.single_le_sum
    (fun i (_ : i ∈ G.neighborFinset v) => hcoeff i)
    ((G.mem_neighborFinset v u).mpr hvu)
  have hv := congrFun hrow v
  rw [graphWeightMatrix_mulVec_apply] at hv
  linarith only [hsum, hv]

/-- The neighboring canonical row turns the previous inequality into an
improved lower bound at the higher-weight root, without any leaf premise. -/
theorem graph_canonical_neighbor_coefficient_inequality
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i) (v u : V)
    (hvu : G.Adj v u) (hu : weight u = 2) :
    2 * (weight v - 2) ≤ (2 * weight v - 1) * coeff v := by
  have hv := graph_neighbor_row_lower_bound G weight coeff hrow hcoeff v u hvu
  have hu' := graph_neighbor_le_twice G weight coeff hrow hcoeff u v hu hvu.symm
  nlinarith only [hv, hu']

/-- In beta five, an edge at either distinguished higher-weight component
contradicts positive length. Component separation and invertibility are
not needed for this local consequence of the actual rows. -/
theorem beta_five_core_isolated
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (C B D : V)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hB : weight B = 3) (hD : weight D = 5)
    (hlength : 0 < 1 - coeff C - coeff B - coeff D)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2) :
    (∀ v, ¬ G.Adj B v) ∧ (∀ v, ¬ G.Adj D v) := by
  have hb := graph_coefficient_lower_bound G weight coeff hrow hcoeff B
    (by rw [hB]; norm_num)
  have hd := graph_coefficient_lower_bound G weight coeff hrow hcoeff D
    (by rw [hD]; norm_num)
  rw [hB] at hb
  rw [hD] at hd
  norm_num at hb hd
  constructor
  · intro v hv
    have hv2 := hBsingle v hv.reachable (Ne.symm hv.ne)
    have hbetter := graph_canonical_neighbor_coefficient_inequality
      G weight coeff hrow hcoeff B v hv hv2
    rw [hB] at hbetter
    linarith only [hbetter, hd, hcoeff C, hlength]
  · intro v hv
    have hv2 := hDsingle v hv.reachable (Ne.symm hv.ne)
    have hbetter := graph_canonical_neighbor_coefficient_inequality
      G weight coeff hrow hcoeff D v hv hv2
    rw [hD] at hbetter
    linarith only [hbetter, hb, hcoeff C, hlength]

/-- Source-facing form, with length expressed using the actual marked
vector. Isolation gives the exact core coefficients from the original
rows, and the only remaining contribution to length is the coefficient
at C. The final upper bound uses its given nonnegativity. -/
theorem beta_five_core_source_rigidity
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → 𝕜)
    (C B D : V)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hB : weight B = 3) (hD : weight D = 5)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2) :
    (∀ v, ¬ G.Adj B v) ∧ (∀ v, ¬ G.Adj D v) ∧
      coeff B = 1 / 3 ∧ coeff D = 3 / 5 ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 15 - coeff C ∧
      1 - dotProduct (threeMarkedSource C B D) coeff ≤ 1 / 15 := by
  have hlength' : 0 < 1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hlength
    linarith only [hlength]
  obtain ⟨hBi, hDi⟩ := beta_five_core_isolated G weight coeff C B D hrow hcoeff
    hB hD hlength' hBsingle hDsingle
  have hb := graph_isolated_row G weight coeff (fun i => weight i - 2) hrow B hBi
  have hd := graph_isolated_row G weight coeff (fun i => weight i - 2) hrow D hDi
  dsimp only at hb hd
  rw [hB] at hb
  rw [hD] at hd
  have hb' : coeff B = 1 / 3 := by linarith only [hb]
  have hd' : coeff D = 3 / 5 := by linarith only [hd]
  have hell : 1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 15 - coeff C := by
    rw [threeMarkedSource_dotProduct, hb', hd']
    ring
  refine ⟨hBi, hDi, hb', hd', hell, ?_⟩
  rw [hell]
  linarith only [hcoeff C]

end KltDP.LinearAlgebra
