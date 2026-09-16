import KltDP.Examples.FrobeniusTowerGraphIdentity

/-!
# The Picard relation of the graph identity, and the `B` row of Proposition 10.1

The Picard form of `totalGraphDivisor_eq`, by the accepted generic `cartierPicardHom_fiber_relation`,
exactly as the accepted `totalFiberDivisor_picard` derives the fibre row from
`totalFiberDivisor_eq`.  Kept in its own module so that a failure here cannot cost the Cartier-level
identity of `FrobeniusTowerGraphIdentity`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerGraphPicard

open KltDP.Geometry
open FrobeniusProjectivePoints
open FrobeniusExceptionalCartier FrobeniusGlobalBlowupStages
open FrobeniusGraphPicardClassIntegral FrobeniusGraphStrictCartier
open FrobeniusOldExceptionalLaterCartier
open FrobeniusTowerGraphIdentity FrobeniusTowerGraphPullback

variable {k : Type u} [Field k]

local instance graphPicardProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance graphPicardInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-- The Picard relation between the classes of the actual Cartier divisors. -/
theorem totalGraphDivisor_picard (N m : ℕ) :
    cartierPicardHom _ (totalGraphDivisor (k := k) (N + 1) (m + (N + 1))) =
      cartierPicardHom _ (graphStrictDivisor (N + 1) m) +
        ∑ j : Fin N, (j.val + 1) • cartierPicardHom _ (oldFinalDivisor (N + 1) j.val (by omega)) +
        (N + 1) • cartierPicardHom _ (stepExceptionalDivisor N) :=
  cartierPicardHom_fiber_relation _ _ _ _
    (fun j : Fin N => oldFinalDivisor (N + 1) j.val (by omega)) (N + 1)
    (totalGraphDivisor_eq N m)

end KltDP.Examples.FrobeniusTowerGraphPicard

namespace KltDP.Examples

open KltDP.Geometry FrobeniusTowerGraphPullback FrobeniusTowerGraphIdentity
  FrobeniusGraphStrictCartier FrobeniusOldExceptionalLaterCartier FrobeniusExceptionalCartier

/-- **F29, Proposition 10.1, the `B` row (Cartier level).** On stage `N+1` of the origin contact
tower of the graph `Γ : v = u^{m+N+1}` of `P¹ × P¹`, the total transform of the graph, as an
effective Cartier divisor, is `B̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem f29_tower_graph_relation (k : Type u) [Field k] (N m : ℕ) :
    totalGraphDivisor (k := k) (N + 1) (m + (N + 1)) =
      graphStrictDivisor (N + 1) m +
        ∑ j : Fin N, (j.val + 1) • oldFinalDivisor (N + 1) j.val (by omega) +
        (N + 1) • stepExceptionalDivisor N :=
  totalGraphDivisor_eq N m

theorem f29_tower_graph_relation_universe_check (k : Type u) [Field k] : True := by
  have := f29_tower_graph_relation.{u} k
  trivial

end KltDP.Examples
