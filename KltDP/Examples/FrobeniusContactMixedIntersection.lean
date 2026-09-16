import KltDP.Examples.FrobeniusContactSelfIntersectionValues

/-!
# The graph-fibre intersection is the residual contact order

On the single-origin stage `N = n + 1`, the graph has original exponent `p = m + N`.
The actual strict-fibre class is `b - Σ E_j`. The proved graph degrees of `b` and `Σ E_j`
are `p` and `N`, so `B · F̃ = m`. The actual class comparisons and the accepted symmetric
surface pairing give `F̃ · B = m`. In particular, both degrees vanish at residual exponent zero.

The original stage-projectivity and algebraic-closure hypotheses remain explicit. This module
does not identify the single-origin tower with a simultaneous multi-centre construction.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Examples.FrobeniusContactMixedIntersection

open KltDP.Geometry KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageExceptionalSelfIntersection
open FrobeniusStrictTransformPairing FrobeniusStrictTransformPicardStep
open FrobeniusFiberPicard FrobeniusFiberZeroInvertible
open FrobeniusContactClassPairing FrobeniusContactSelfIntersectionValues FrobeniusRulingPairingValues

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The graph's degree against the actual strict-fibre class is the residual exponent `m`. -/
theorem graphStrictPairing_fiberPicardClass_eq (m : ℕ) :
    graphStrictPairing n hproj m
      (fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) = (m : ℤ) := by
  rw [fiberPicardClass_tower, fiberTotalClass_eq_secondFiberTotalClass, map_sub,
    graphStrictPairing_secondFiberTotalClass_eq, graphStrictPairing_sum_totalExceptional]
  ring

/-- The two actual graph-fibre restriction degrees agree by the proved symmetric pairing. -/
theorem graphStrict_fiber_pairing_symm (m : ℕ) :
    graphStrictPairing n hproj m
        (fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) =
      fiberStrictPairing n hproj (strictCurvePicardClass (n + 1) m) := by
  rw [graphStrictPairing_eq_contactPairing, fiberStrictPairing_eq_contactPairing]
  exact pairing_symm (stageSurface (n + 1) hproj) (stageRegular n hproj) _ _

/-- The fibre's degree against the actual strict-graph class is the residual exponent `m`. -/
theorem fiberStrictPairing_strictCurvePicardClass_eq (m : ℕ) :
    fiberStrictPairing n hproj (strictCurvePicardClass (n + 1) m) = (m : ℤ) :=
  (graphStrict_fiber_pairing_symm n hproj m).symm.trans
    (graphStrictPairing_fiberPicardClass_eq n hproj m)

/-- At the terminal residual exponent zero, both graph-fibre intersection degrees vanish. -/
theorem contactTower_terminal_graph_fiber_zero :
    graphStrictPairing n hproj 0
        (fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) = 0 ∧
      fiberStrictPairing n hproj (strictCurvePicardClass (n + 1) 0) = 0 :=
  ⟨graphStrictPairing_fiberPicardClass_eq n hproj 0,
    fiberStrictPairing_strictCurvePicardClass_eq n hproj 0⟩

end KltDP.Examples.FrobeniusContactMixedIntersection
