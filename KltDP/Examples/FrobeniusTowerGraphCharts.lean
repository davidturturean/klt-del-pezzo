import KltDP.Examples.FrobeniusTowerFiberPullback
import KltDP.Examples.FrobeniusGraphPicardClassFrames
import KltDP.Examples.FrobeniusStrictTransformInvertible
import KltDP.Examples.FrobeniusStrictTransformSecondChartFrame
import KltDP.Examples.FrobeniusStrictTransformSecondChartAlgebra

/-!
# The pullback of the graph equation on the two Rees opens of the origin tower

BRIEF37 instructs: establish **on which opens the identity `π^*Γ = B̃ + Σ_j E_j^tot` is an equality
of ideals before writing any divisor-level statement**, and records the known obstacle as the second
Rees open, where the strict graph's generator `1 - u'^{m+1} v^m` is not a unit.

This module settles that question, and the answer is that **the second Rees open is not an obstacle
and no separate chart is needed**: the same three-piece cover that carries the accepted fibre
identity (`firstAffineOpen`, `secondAffineOpen`, the centre complement) carries the graph identity
too.  The non-unit factor sits on *both* sides — it is exactly the strict graph, which the
right-hand side carries as `B̃`, whereas in the fibre case the strict fibre is absent from that open
and the corresponding factor is `1`.

The two computations, both from accepted inputs:

* on the selected chart open of stage `N` the graph equation pulls back to `u^N · (v - u^m)`
  (`between_appLE_graph_first'`), by the accepted `stageTotalEquation_factorization`; the residual
  factor is the accepted `firstAmbientEquation N m`, which generates the strict graph there
  (`strictIdeal_firstAffineOpen`);
* on the second Rees open of the last blowup of stage `n+1` it pulls back to
  `(u/v)^n · v^{n+1} · (1 - u'^{m+1} v^m)` (`between_appLE_graph_second'`), by the accepted
  `stageTotalEquation_factorization` and `secondTotalEquation_factorization`; the last factor is the
  accepted `secondAmbientEquation n m` (`between_appLE_graph_second_strictGenerator`), which
  generates the strict graph there (`strictIdeal_secondAffineOpen`).

Read against the accepted `between_appLE_first'` (`u^{N+1} v`) and `between_appLE_second'`
(`(u/v)^n v^{n+1}`) for the fibre, these exhibit the graph identity as the fibre identity with the
unit factor `1` on the second open replaced by the strict-graph generator.

No divisor-level statement is made here; that needs the base divisor of `FrobeniusGraphZeroCartier`
and the stage induction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerGraphCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusBlowupContact FrobeniusBlowupSmooth FrobeniusBlowupChartIteration
open FrobeniusExceptionalFinalConfiguration FrobeniusExceptionalSuccessorChart
open FrobeniusGlobalBlowupStages
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformSecondChart
open FrobeniusStrictTransformSecondChartAlgebra FrobeniusStrictTransformSecondChartFrame
open FrobeniusTowerFiberPullback

variable {k : Type u} [Field k]

/-! ### The selected chart open -/

set_option maxHeartbeats 4000000 in
/-- The graph equation pulls back through the selected chart of stage `N` by the accepted
`stageSubstitution N`. -/
theorem between_appLE_graph_first (N p : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le N)).appLE (productOpen 0 0)
        (firstAffineOpen N).1 (firstAffineOpen_le_preimage N) (diagonalSection p 0) =
      (((projectiveProductInitial (k := k)).stage N).chart.appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv
          (stageSubstitution N (vCoord - uCoord ^ p))) :=
  appLE_of_chart_square _ (productChart 0 0) _ (CommRingCat.ofHom (stageSubstitution N))
    (chart_between_square N) (firstAffineOpen_le_preimage N) (vCoord - uCoord ^ p)

set_option maxHeartbeats 4000000 in
/-- **`π_N^*(v - u^{m+N}) = u^N · (v - u^m)` on the selected chart open of stage `N`**: the
exceptional factor of the total transform, with the accepted strict-graph generator
`firstAmbientEquation N m` as its residual factor. -/
theorem between_appLE_graph_first' (N m : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le N)).appLE (productOpen 0 0)
        (firstAffineOpen N).1 (firstAffineOpen_le_preimage N) (diagonalSection (m + N) 0) =
      (((projectiveProductInitial (k := k)).stage N).chart.appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord) ^ N *
        firstAmbientEquation N m := by
  rw [between_appLE_graph_first, stageTotalEquation_factorization]
  change (((projectiveProductInitial (k := k)).stage N).chart.appIso ⊤).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom
      (uCoord ^ N * (vCoord - uCoord ^ m))) = _
  rw [map_mul, map_pow, map_mul, map_pow]
  rfl

/-! ### The second Rees open of the last blowup -/

set_option maxHeartbeats 4000000 in
/-- The graph equation pulls back through the second Rees chart by the accepted composite
`chartBaseMap ∘ stageSubstitution n`. -/
theorem between_appLE_graph_second (n p : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE (productOpen 0 0)
        (secondAffineOpen n).1 (secondAffineOpen_le_preimage n) (diagonalSection p 0) =
      secondSectionsEquiv n
        (chartBaseMap (centerIdeal (k := k)) centerV
          (stageSubstitution n (vCoord - uCoord ^ p))) := by
  rw [secondSectionsEquiv_apply]
  exact appLE_of_chart_square (secondStageChart n) (productChart 0 0) _
    (CommRingCat.ofHom ((chartBaseMap (centerIdeal (k := k)) centerV).comp (stageSubstitution n)))
    (secondChart_between_square n) (secondAffineOpen_le_preimage n) (vCoord - uCoord ^ p)

set_option maxHeartbeats 4000000 in
/-- **`π_{n+1}^*(v - u^{(m+1)+n}) = (u/v)^n · v^{n+1} · (1 - u'^{m+1} v^m)` on the second Rees open
of the last blowup of stage `n+1`.**  The last factor is the residual equation of the strict graph;
it is a unit only near `P`, and this is precisely why the identity still holds on this open — the
right-hand side of the tower identity carries the same factor as `B̃`, where in the fibre case the
strict fibre is absent and the factor is `1`. -/
theorem between_appLE_graph_second' (n m : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE (productOpen 0 0)
        (secondAffineOpen n).1 (secondAffineOpen_le_preimage n) (diagonalSection ((m + 1) + n) 0) =
      secondSectionsEquiv n oldRatio ^ n * secondSectionsEquiv n vEquation ^ (n + 1) *
        secondSectionsEquiv n (secondResidualEquation m) := by
  rw [between_appLE_graph_second, stageTotalEquation_factorization, map_mul, map_pow,
    secondTotalEquation_factorization, ← vEquation_mul_oldRatio, map_mul, map_pow, map_mul, map_mul]
  ring

/-- The same, with the accepted `secondAmbientEquation n m`: the generator of the strict graph on
the second Rees open (`strictIdeal_secondAffineOpen`) is exactly the extra factor. -/
theorem between_appLE_graph_second_strictGenerator (n m : ℕ) :
    (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE (productOpen 0 0)
        (secondAffineOpen n).1 (secondAffineOpen_le_preimage n) (diagonalSection ((m + 1) + n) 0) =
      secondSectionsEquiv n oldRatio ^ n * secondSectionsEquiv n vEquation ^ (n + 1) *
        secondAmbientEquation n m :=
  between_appLE_graph_second' n m

end KltDP.Examples.FrobeniusTowerGraphCharts
