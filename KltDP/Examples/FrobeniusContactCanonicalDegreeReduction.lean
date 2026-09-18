import KltDP.Examples.FrobeniusContactTowerCanonicalIteration
import KltDP.Examples.FrobeniusContactSelfIntersectionValues

/-!
# Actual canonical degrees on the strict graph and tangent fibre

The actual canonical tower formula and the already proved exceptional degree
rows reduce both degrees to the original canonical line on the initial product.
After N blowups the correction is N. The initial canonical degree is retained
as an actual geometric degree; its numerical value is not an extra hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactCanonicalDegreeReduction

open KltDP.Geometry KltDP.Geometry.PrimeCurveDegreeTransport
open FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusStrictTransformPairing FrobeniusStrictTransformFiberRows
open FrobeniusContactTowerCanonicalIteration FrobeniusContactSelfIntersectionValues
open FrobeniusGraphBaseRows FrobeniusGraphBasePairing FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassZeroFiber

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The actual strict graph canonical degree is its initial canonical degree plus N. -/
theorem graphStrictPairing_canonical (m : ℕ) :
    graphStrictPairing n hproj m (originalCanonicalClass (k := k) (n + 1)) =
      graphBasePairing (m + (n + 1)) (originalCanonicalClass (k := k) 0) + (n + 1 : ℤ) := by
  rw [originalCanonicalClass_tower, map_add, graphStrictPairing_sum_totalExceptional]
  congr 1
  exact graphStrictPairing_eq_graphPrimeCurve n hproj m _

/-- The actual tangent-fibre canonical degree is its initial canonical degree plus N. -/
theorem fiberStrictPairing_canonical :
    fiberStrictPairing n hproj (originalCanonicalClass (k := k) (n + 1)) =
      eulerDegree (fiberSectionBase (k := k))
        (schemePicardPullbackHom (horizontalFiberMorphism (0 : k))
          (originalCanonicalClass (k := k) 0).toMul) + (n + 1 : ℤ) := by
  rw [originalCanonicalClass_tower, map_add, fiberStrictPairing_sum_totalExceptional]
  congr 1
  exact fiberStrictPairing_pullback n hproj _

end KltDP.Examples.FrobeniusContactCanonicalDegreeReduction
