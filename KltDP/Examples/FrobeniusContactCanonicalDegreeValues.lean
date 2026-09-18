import KltDP.Examples.FrobeniusInitialCanonicalTower
import KltDP.Examples.FrobeniusContactCanonicalDegreeReduction
import KltDP.Examples.FrobeniusFiberFirstFiberDegree
import KltDP.Examples.FrobeniusStageCanonicalCartier

/-!
# Numerical canonical degrees on the original contact tower

The actual initial canonical formula and the existing geometric ruling and
exceptional rows give the canonical degrees on the original strict graph and
tangent fibre. Their sums with the actual self-intersections are minus two.
The original algebraic closure and final-stage projectivity remain explicit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactCanonicalDegreeValues

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformPairing
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
open FrobeniusGraphPicardClassTotalTransform FrobeniusVerticalPicardBridge
open FrobeniusInitialCanonicalFormula FrobeniusInitialCanonicalTower
open FrobeniusContactTowerCanonicalIteration FrobeniusContactCanonicalDegreeReduction
open FrobeniusGraphBaseRows FrobeniusGraphBasePairing FrobeniusRulingPairingValues
open FrobeniusContactSelfIntersectionValues FrobeniusFiberFirstFiberDegree
open FrobeniusStrictTransformFiberRowsValues FrobeniusStrictTransformClassesTower
open FrobeniusStrictTransformPicardStep
open FrobeniusFiberPicard FrobeniusFiberZeroInvertible
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves FrobeniusStageCanonicalCartier
open SmoothCanonicalCartierRepresentative SmoothCanonicalCartierPicard

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The existing second total ruling is its original Picard pullback. -/
theorem secondFiberTotalClass_eq_pullback (N : ℕ) :
    secondFiberTotalClass (k := k) N =
      (schemePicardPullbackHom (projectiveContactProjection N)).toAdditive secondFiberClass := by
  unfold secondFiberTotalClass graphTotalIdealLine secondFiberClass
  rw [map_neg]
  change -Additive.ofMul
      (pullbackInvertibleSheaf (projectiveContactProjection N) (graphIdealLine 0)).toPic =
    -Additive.ofMul
      (schemePicardPullbackHom (projectiveContactProjection N) (graphIdealLine 0).toPic)
  rw [schemePicardPullbackHom_toPic]

/-- The actual canonical class, expressed in the existing total ruling classes. -/
theorem originalCanonicalClass_eq_totalFibers (N : ℕ) :
    originalCanonicalClass (k := k) N =
      (-2 : ℤ) • firstFiberTotalClass N + (-2 : ℤ) • secondFiberTotalClass N +
        ∑ j : Fin N, totalExceptionalClass N j := by
  rw [originalCanonicalClass_eq_fibers_exceptionals,
    firstFiberTotalClass_eq_pullback_firstFiberClass, secondFiberTotalClass_eq_pullback]

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The strict graph's canonical degree is `-2p - 2 + N`, for `p = m + N`. -/
theorem graphStrictPairing_canonical_eq (m : ℕ) :
    graphStrictPairing n hproj m (originalCanonicalClass (k := k) (n + 1)) =
      -2 * (m + (n + 1) : ℤ) - 2 + (n + 1 : ℤ) := by
  rw [graphStrictPairing_canonical, originalCanonicalClass_zero, map_add,
    map_zsmul, map_zsmul, graphBasePairing_firstFiber_one,
    graphBasePairing_secondFiber_eq_exponent]
  simp only [zsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- The strict tangent fibre's canonical degree is `N - 2`. -/
theorem fiberStrictPairing_canonical_eq :
    fiberStrictPairing n hproj (originalCanonicalClass (k := k) (n + 1)) =
      (n + 1 : ℤ) - 2 := by
  rw [originalCanonicalClass_eq_totalFibers, map_add, map_add, map_zsmul, map_zsmul,
    fiberStrictPairing_firstFiberTotalClass_eq_one, fiberStrictPairing_secondFiber_zero,
    fiberStrictPairing_sum_totalExceptional]
  simp only [zsmul_eq_mul]
  ring

/-- The original strict graph has `(K + B) · B = -2`. -/
theorem graphStrictPairing_canonical_add_self (m : ℕ) :
    graphStrictPairing n hproj m
      (originalCanonicalClass (k := k) (n + 1) + strictCurvePicardClass (n + 1) m) = -2 := by
  rw [map_add, graphStrictPairing_canonical_eq, graphStrictPairing_self_eq]
  ring

/-- The original strict tangent fibre has `(K + F) · F = -2`. -/
theorem fiberStrictPairing_canonical_add_self :
    fiberStrictPairing n hproj
      (originalCanonicalClass (k := k) (n + 1) +
        fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) = -2 := by
  rw [map_add, fiberStrictPairing_canonical_eq, fiberStrictPairing_self_eq]
  ring

/-- The same degree for the actual canonical Cartier representative on the graph. -/
theorem graph_canonicalIntersection (m : ℕ) :
    (graphStrictPrimeCurve n hproj m).intersectionNumber (canonicalCartier (k := k) (n + 1)) =
      -2 * (m + (n + 1) : ℤ) - 2 + (n + 1 : ℤ) := by
  rw [← (graphStrictPrimeCurve n hproj m).picardRestrictionDegreeHom_cartierPicardHom]
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom
    (graphStrictPrimeCurve n hproj m)
    (cartierPicardHom (projectiveContactStage (k := k) (n + 1))
      (cartierRepresentative ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)) = _
  rw [cartierPicardHom_representative]
  exact graphStrictPairing_canonical_eq n hproj m

/-- The same degree for the actual canonical Cartier representative on the tangent fibre. -/
theorem fiber_canonicalIntersection :
    (fiberStrictPrimeCurve n hproj).intersectionNumber (canonicalCartier (k := k) (n + 1)) =
      (n + 1 : ℤ) - 2 := by
  rw [← (fiberStrictPrimeCurve n hproj).picardRestrictionDegreeHom_cartierPicardHom]
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom
    (fiberStrictPrimeCurve n hproj)
    (cartierPicardHom (projectiveContactStage (k := k) (n + 1))
      (cartierRepresentative ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)) = _
  rw [cartierPicardHom_representative]
  exact fiberStrictPairing_canonical_eq n hproj

end KltDP.Examples.FrobeniusContactCanonicalDegreeValues
