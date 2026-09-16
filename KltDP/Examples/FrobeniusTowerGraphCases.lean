import KltDP.Examples.FrobeniusTowerGraphPullback
import KltDP.Examples.FrobeniusTowerGraphCharts
import KltDP.Examples.FrobeniusGraphStrictCartier
import KltDP.Examples.FrobeniusTowerCartierIdentity

/-!
# The two Rees-open cases of the graph identity `π^*Γ = B̃ + Σ_j E_j^tot`

Part of item 3 of BRIEF38: the two cases of the three-piece cover that BRIEF37's chart identities
feed directly. The right-hand side

  `graphTowerRHS (n+1) m = B̃ · Π_{j<n} C_j^{j+1} · P^{n+1}`

differs from the accepted fibre `towerRHS` only in its first factor (`strictTransformIdeal` in place
of `fiberStrictIdeal`); the exceptional bookkeeping (`oldIdealAt`, `stepExceptionalIdeal`) is
curve-independent and is reused from `FrobeniusTowerCartierIdentity` unchanged.

* `graphChartZero p` is the explicit regular equation chart of `graphZeroDivisor p` on the first
  diagonal open, from the accepted `cartierDivisorOfIdeal_regularChart` applied to the principal
  regular chart `⟨diagonalAffineOpen 0, diagonalSection p 0⟩` of BRIEF37; its `openSet` is
  `productOpen 0 0` and its coefficient is `diagonalSection p 0`, both by `rfl`.
* `graph_first_case`: on the selected chart open the pulled-back generator is
  `u^{n+1} · (v - u^m)` (BRIEF37's `between_appLE_graph_first'`, whose exceptional factor is
  *definitionally* the accepted `firstExceptionalAmbientEquation n`), matching `B̃ · P^{n+1}` with
  every `C_j` the unit ideal there.
* `graph_second_case`: on the second Rees open the pulled-back generator is
  `(u/v)^n · v^{n+1} · (1 - u'^{m+1} v^m)` (BRIEF37's `between_appLE_graph_second'`), matching
  `B̃ · C_{n-1}^n · P^{n+1}`. **This is the case the earlier briefs called an obstacle**: the strict
  graph is present on this open, with generator `secondAmbientEquation n m`, where the strict fibre
  was absent and contributed `1`.

The centre-complement case, stage `0` and the induction are not performed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusTowerGraphCases

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusGlobalStrictTransform
open FrobeniusExceptionalSuccessorChart FrobeniusExceptionalCartier
open FrobeniusOldExceptionalBirthCartier
open FrobeniusGraphPicardClassAffine FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphZeroCartier FrobeniusGraphStrictCartier
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformFirstChartTensorFrame
open FrobeniusStrictTransformSecondChartAlgebra FrobeniusStrictTransformSecondChartFrame
open FrobeniusTowerFiberPullback FrobeniusTowerCartierIdentity
open FrobeniusTowerGraphCharts FrobeniusTowerGraphPullback

variable {k : Type u} [Field k]

local instance graphCasesProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance graphCasesInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-! ### The explicit regular chart of the graph divisor -/

/-- The graph ideal is principal and regular on the first diagonal open (BRIEF37). -/
def graphPrincipalChart (p : ℕ) :
    PrincipalRegularChart (projectiveProduct k) (graphIdeal p) where
  openSet := diagonalAffineOpen 0
  nonempty := productOpen_nonempty 0 0
  generator := diagonalSection p 0
  span_eq := diagonalSection_ideal p 0
  regular := diagonalSection_regular p 0

/-- The corresponding regular equation chart of `graphZeroDivisor p`. -/
def graphChartZero (p : ℕ) :
    RegularCartierEquationChart (projectiveContactStage (k := k) 0) (graphZeroDivisor p) :=
  cartierDivisorOfIdeal_regularChart _ (graphIdeal p) (graphIdeal_locallyPrincipalRegular p)
    (graphPrincipalChart p)

theorem graphChartZero_openSet (p : ℕ) :
    (graphChartZero (k := k) p).chart.openSet = productOpen 0 0 := rfl

theorem graphChartZero_coefficient (p : ℕ) :
    (graphChartZero (k := k) p).coefficient = diagonalSection (k := k) p 0 := rfl

/-! ### The right-hand side -/

/-- `B̃_n · Π_{j<n-1} C_j^{j+1} · P_n^n` on stage `n` (the strict graph alone on stage `0`). -/
def graphTowerRHS : (n : ℕ) → (m : ℕ) → (projectiveContactStage (k := k) n).IdealSheafData
  | 0, m => strictTransformIdeal 0 (m + 0)
  | n + 1, m =>
      idealSheafDataMul (idealSheafDataMul (strictTransformIdeal (n + 1) (m + (n + 1)))
        (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n))
        (idealSheafDataPow (stepExceptionalIdeal n) (n + 1))

/-! ### The selected chart open -/

set_option maxHeartbeats 4000000 in
/-- **On the selected chart open the graph identity holds.** -/
theorem graph_first_case (n m : ℕ) (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (firstAffineOpen (n + 1)).1) :
    (totalGraphIdeal (n + 1) (m + (n + 1))).ideal W = (graphTowerRHS (n + 1) m).ideal W := by
  refine IdealSheafData.ideal_eq_of_nonempty _ _ W (fun hne => ?_)
  have hW' : W.1 ≤ between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ
      productOpen 0 0 := hW.trans (firstAffineOpen_le_preimage (n + 1))
  have hres := congrArg (fun f => f (diagonalSection (m + (n + 1)) 0))
    (Scheme.Hom.appLE_map (f := between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)))
      (firstAffineOpen_le_preimage (n + 1)) (homOfLE hW).op)
  simp only [CommRingCat.comp_apply] at hres
  have hgen : (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
      (productOpen 0 0) W.1 hW' (diagonalSection (m + (n + 1)) 0) =
      ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (firstAmbientEquation (n + 1) m) *
        ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (firstExceptionalAmbientEquation n) ^ (n + 1) := by
    rw [← hres, between_appLE_graph_first']
    show ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
      (firstExceptionalAmbientEquation n ^ (n + 1) * firstAmbientEquation (n + 1) m) = _
    rw [map_mul, map_pow, mul_comm]
  have hFP : (idealSheafDataFinProd
      (fun j => idealSheafDataPow (oldIdealAt (k := k) (n + 1) j) (j + 1)) n).ideal W = ⊤ :=
    idealSheafDataFinProd_ideal_eq_top _ W n (fun j hj => by
      rw [idealSheafDataPow_ideal, oldIdealAt_of_le (n + 1) j (by omega),
        oldFinalIdeal_first (n + 1) j (by omega) W hW, Ideal.span_singleton_one, Ideal.top_pow])
  rw [totalGraphIdeal_ideal (n + 1) (m + (n + 1)) (graphChartZero (m + (n + 1))) W hW']
  show Ideal.span {(between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
    (productOpen 0 0) W.1 hW' (diagonalSection (m + (n + 1)) 0)} = _
  rw [hgen]
  show _ = (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal W *
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n).ideal W *
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1)).ideal W
  rw [hFP, idealSheafDataPow_ideal,
    ← (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).map_ideal hW,
    strictIdeal_firstAffineOpen, ← (stepExceptionalIdeal (k := k) n).map_ideal hW,
    stepExceptionalIdeal_firstOpen, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]
  rfl

/-! ### The second Rees open -/

/-- On the second Rees open the strict **graph** is present, with the residual generator. -/
theorem graph_second_case_strict (n m : ℕ)
    (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) :
    (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal W =
      Ideal.span {((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
        (secondAmbientEquation n m)} := by
  rw [← (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).map_ideal hW,
    strictIdeal_secondAffineOpen, Ideal.map_span, Set.image_singleton]
  all_goals exact rfl

set_option maxHeartbeats 4000000 in
/-- **On the second Rees open the graph identity holds** — the case earlier briefs called an
obstacle. The non-unit factor `1 - u'^{m+1} v^m` appears on both sides: on the left as part of the
pulled-back equation, on the right as the strict graph `B̃`. -/
theorem graph_second_case (n m : ℕ) (W : (projectiveContactStage (k := k) (n + 1)).affineOpens)
    (hW : W.1 ≤ (secondAffineOpen n).1) :
    (totalGraphIdeal (n + 1) (m + (n + 1))).ideal W = (graphTowerRHS (n + 1) m).ideal W := by
  rw [show m + (n + 1) = (m + 1) + n from by omega]
  refine IdealSheafData.ideal_eq_of_nonempty _ _ W (fun hne => ?_)
  have hW' : W.1 ≤ between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)) ⁻¹ᵁ
      productOpen 0 0 := hW.trans (secondAffineOpen_le_preimage n)
  have hres := congrArg (fun f => f (diagonalSection ((m + 1) + n) 0))
    (Scheme.Hom.appLE_map (f := between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1)))
      (secondAffineOpen_le_preimage n) (homOfLE hW).op)
  simp only [CommRingCat.comp_apply] at hres
  have hgen : (between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
      (productOpen 0 0) W.1 hW' (diagonalSection ((m + 1) + n) 0) =
      ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
          (secondAmbientEquation n m) *
        (((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
            (secondSectionsEquiv n oldRatio) ^ n *
          ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
            (secondSectionsEquiv n vEquation) ^ (n + 1)) := by
    rw [← hres, between_appLE_graph_second_strictGenerator]
    show ((projectiveContactStage (k := k) (n + 1)).presheaf.map (homOfLE hW).op).hom
      (secondSectionsEquiv n oldRatio ^ n * secondSectionsEquiv n vEquation ^ (n + 1) *
        secondAmbientEquation n m) = _
    rw [map_mul, map_mul, map_pow, map_pow]
    ring
  rw [totalGraphIdeal_ideal (n + 1) ((m + 1) + n) (graphChartZero ((m + 1) + n)) W hW']
  show Ideal.span {(between (projectiveProductInitial (k := k)) (Nat.zero_le (n + 1))).appLE
    (productOpen 0 0) W.1 hW' (diagonalSection ((m + 1) + n) 0)} = _
  rw [hgen]
  show _ = (strictTransformIdeal (k := k) (n + 1) (m + (n + 1))).ideal W *
      (idealSheafDataFinProd (fun j => idealSheafDataPow (oldIdealAt (n + 1) j) (j + 1)) n).ideal W *
      (idealSheafDataPow (stepExceptionalIdeal n) (n + 1)).ideal W
  rw [graph_second_case_strict n m W hW, second_case_old n W hW, second_case_exceptional n W hW,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, mul_assoc]

end KltDP.Examples.FrobeniusTowerGraphCases
