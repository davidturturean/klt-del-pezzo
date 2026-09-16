import KltDP.Examples.FrobeniusContactClassPairing
import KltDP.Examples.FrobeniusRulingPairingValues
import KltDP.Examples.FrobeniusGraphExceptionalSeparation
import KltDP.Examples.FrobeniusFiberZeroClass
import KltDP.Examples.FrobeniusStrictTransformFiberRowsValues

/-!
# The graph and fibre self-intersections on one origin contact tower

Write `N = n + 1` and `p = m + N`. The accepted actual Picard classes are
`B = p a + b - Σ E_j` and `F̃ = b - Σ E_j`. The graph and fibre miss every older
exceptional curve, so the corresponding actual kernel lines restrict trivially. Their newest
exceptional degrees are one by the proved Cartier-class pairing comparison. The accepted
telescoping identity then gives `B · Σ E_j = F̃ · Σ E_j = N`, and hence
`B² = 2p - N` and `F̃² = -N`.

These are single-origin contact-tower restriction degrees, with the actual stage's projectivity
and algebraic closure explicit. No numerical, effectivity, Euler-degree or transition-exponent
premise is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactSelfIntersectionValues

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformPrimeCurves FrobeniusStrictTransformPairing
open FrobeniusStrictTransformPicardStep FrobeniusStrictTransformClassesTower
open FrobeniusExceptionalFinalConfiguration FrobeniusOldExceptionalLaterStages
open FrobeniusGraphExceptionalSeparation FrobeniusFiberClosure FrobeniusFiberPicard
open FrobeniusFiberZeroInvertible FrobeniusFiberZeroClass FrobeniusTowerPicardRelation
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
open FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformFiberRowsValues
open FrobeniusContactClassPairing FrobeniusGraphFirstFiberDegree FrobeniusRulingPairingValues

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance contactSelfInitialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The total exceptional sum is the weighted chain of actual strict exceptional classes. -/
theorem sum_totalExceptional_eq_weighted (n : ℕ) :
    (∑ j : Fin (n + 1), totalExceptionalClass (k := k) (n + 1) j) =
      (∑ j : Fin n, (j.val + 1) • oldExceptionalStrictClass (n + 1) j.val (by omega)) +
        (n + 1) • stepExceptionalPicardClass n := by
  simpa only [oldExceptionalStrictClass_eq_castSucc, totalExceptionalClass_last] using
    (telescope_castSucc n (totalExceptionalClass (k := k) (n + 1))).symm

/-- The actual total strict-fibre class is the accepted total second ruling class. -/
theorem fiberTotalClass_eq_secondFiberTotalClass (N : ℕ) :
    fiberTotalClass (fiberKernel_zero_isInvertible (k := k)) N = secondFiberTotalClass N := by
  rw [fiberTotalClass_eq_pullback_secondFiberClass, between_zero, secondFiberClass, map_neg]
  change -Additive.ofMul
      (schemePicardPullbackHom (projectiveContactProjection N) (graphIdealLine 0).toPic) =
    -Additive.ofMul (pullbackInvertibleSheaf (projectiveContactProjection N) (graphIdealLine 0)).toPic
  rw [schemePicardPullbackHom_toPic]

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The graph has zero degree against every older strict exceptional class, by actual disjointness. -/
theorem graphStrictPairing_oldExceptional_zero (m j : ℕ) (hj : j + 2 ≤ n + 1) :
    graphStrictPairing n hproj m (oldExceptionalStrictClass (n + 1) j hj) = 0 := by
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (graphStrictPrimeCurve n hproj m)
    (-Additive.ofMul (oldFinalKernelLine (n + 1) j hj).toPic) = 0
  apply restrictionDegreeHom_neg_kernel_zero (stageSurface (n + 1) hproj)
    (graphStrictPrimeCurve n hproj m)
    (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j hj)
    (oldFinalKernelLine (n + 1) j hj) rfl
  rw [range_inclusion, coe_graphStrictPrimeCurve]
  exact strictTransform_disjoint_finalOld (n + 1) j m hj

/-- The fibre has zero degree against every older strict exceptional class, by actual disjointness. -/
theorem fiberStrictPairing_oldExceptional_zero (j : ℕ) (hj : j + 2 ≤ n + 1) :
    fiberStrictPairing n hproj (oldExceptionalStrictClass (n + 1) j hj) = 0 := by
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom (fiberStrictPrimeCurve n hproj)
    (-Additive.ofMul (oldFinalKernelLine (n + 1) j hj).toPic) = 0
  apply restrictionDegreeHom_neg_kernel_zero (stageSurface (n + 1) hproj)
    (fiberStrictPrimeCurve n hproj)
    (finalOldMap (projectiveProductInitial (k := k)) (n + 1) j hj)
    (oldFinalKernelLine (n + 1) j hj) rfl
  rw [range_inclusion, coe_fiberStrictPrimeCurve]
  exact fiberClosure_disjoint_finalOld (projectiveProductInitial (k := k)) (n + 1) j hj

/-- The graph has degree `N` against the total exceptional sum after `N = n + 1` blowups. -/
theorem graphStrictPairing_sum_totalExceptional (m : ℕ) :
    graphStrictPairing n hproj m
      (∑ j : Fin (n + 1), totalExceptionalClass (n + 1) j) = (n + 1 : ℤ) := by
  rw [sum_totalExceptional_eq_weighted, map_add, map_sum, map_nsmul]
  simp only [map_nsmul, graphStrictPairing_oldExceptional_zero, smul_zero, Finset.sum_const_zero,
    graphStrictPairing_stepExceptional_eq_one, zero_add, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one]

/-- The fibre has degree `N` against the total exceptional sum after `N = n + 1` blowups. -/
theorem fiberStrictPairing_sum_totalExceptional :
    fiberStrictPairing n hproj
      (∑ j : Fin (n + 1), totalExceptionalClass (n + 1) j) = (n + 1 : ℤ) := by
  rw [sum_totalExceptional_eq_weighted, map_add, map_sum, map_nsmul]
  simp only [map_nsmul, fiberStrictPairing_oldExceptional_zero, smul_zero, Finset.sum_const_zero,
    fiberStrictPairing_stepExceptional_eq_one, zero_add, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one]

/-- The actual strict graph has self-intersection `2p - N`, where `p = m + N` and `N = n + 1`. -/
theorem graphStrictPairing_self_eq (m : ℕ) :
    graphStrictPairing n hproj m (strictCurvePicardClass (n + 1) m) =
      2 * (m + (n + 1) : ℤ) - (n + 1 : ℤ) := by
  rw [strictCurvePicardClass_tower, map_sub, map_add, map_nsmul,
    graphStrictPairing_firstFiberTotalClass_eq_one, graphStrictPairing_secondFiberTotalClass_eq,
    graphStrictPairing_sum_totalExceptional]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  ring

/-- The actual strict horizontal fibre has self-intersection `-N` after `N = n + 1` blowups. -/
theorem fiberStrictPairing_self_eq :
    fiberStrictPairing n hproj
      (fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) = -(n + 1 : ℤ) := by
  rw [fiberPicardClass_tower, fiberTotalClass_eq_secondFiberTotalClass, map_sub,
    fiberStrictPairing_secondFiber_zero, fiberStrictPairing_sum_totalExceptional, zero_sub]

/-- The two self-intersection values for the actual graph and fibre on one origin contact tower. -/
theorem contactTower_self_intersections (m : ℕ) :
    graphStrictPairing n hproj m (strictCurvePicardClass (n + 1) m) =
        2 * (m + (n + 1) : ℤ) - (n + 1 : ℤ) ∧
      fiberStrictPairing n hproj
        (fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) = -(n + 1 : ℤ) :=
  ⟨graphStrictPairing_self_eq n hproj m, fiberStrictPairing_self_eq n hproj⟩

end KltDP.Examples.FrobeniusContactSelfIntersectionValues
