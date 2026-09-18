import KltDP.Examples.FrobeniusGlobalBlowupCanonicalExceptionalCartier
import KltDP.Examples.FrobeniusContactTowerSelectedPoint
import KltDP.Examples.FrobeniusTowerFunctionField
import KltDP.Examples.FrobeniusGraphPicardClassIntegral

/-!
# The original canonical formula at every actual contact-tower step

The accepted stage integrality and smoothness producers discharge the
hypotheses of the whole-stage canonical formula. The final original and
translated projective-tower theorems require only the coefficient field;
no projectivity, canonical formula or extra numerical premise is assumed.
Every exceptional divisor is the accepted divisor of the actual next
center fiber for that same original stage and projection.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFormula

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth FrobeniusTranslatedCharts
open FrobeniusContactTowerSelectedPoint FrobeniusGlobalBlowupCanonicalExceptionalCartier

variable {k : Type u} [Field k]

local instance towerCanonicalNextIntegral (A : PlaneChartedScheme k) [IsIntegral A.carrier]
    (n : ℕ) : IsIntegral (A.stage n).nextScheme :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral A (n + 1)

/-- The original actual exceptional Cartier divisor of this same tower step. -/
def stageExceptionalCartier (A : PlaneChartedScheme k) [IsIntegral A.carrier] (n : ℕ) :
    CartierDivisor (A.stage (n + 1)).carrier :=
  wholeExceptionalCartier (A.stage n)

/-- The actual stage geometry discharges the new-stage hypotheses of the canonical formula. -/
theorem stage_canonicalPicard_formula (A : PlaneChartedScheme k) [IsIntegral A.carrier]
    [IsSmoothOfRelativeDimension 2 A.structureMap] (n : ℕ) :
    Additive.ofMul (canonicalSheafOfSmoothSurface (A.stage (n + 1)).structureMap).toPic =
      Additive.ofMul (schemePicardPullbackHom (A.stepProjection n)
        (canonicalSheafOfSmoothSurface (A.stage n).structureMap).toPic) +
        cartierPicardHom (A.stage (n + 1)).carrier (stageExceptionalCartier A n) :=
  canonicalSheafPicard_formula_exceptional (A.stage n)

local instance towerCanonicalProductIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The original projective contact tower has the canonical formula at every actual step. -/
theorem originalStage_canonicalPicard_formula (n : ℕ) :
    Additive.ofMul (canonicalSheafOfSmoothSurface
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap).toPic =
      Additive.ofMul (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (canonicalSheafOfSmoothSurface
          ((projectiveProductInitial (k := k)).stage n).structureMap).toPic) +
        cartierPicardHom (projectiveContactStage (k := k) (n + 1))
          (stageExceptionalCartier projectiveProductInitial n) :=
  stage_canonicalPicard_formula projectiveProductInitial n

local instance towerCanonicalTranslatedIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Every original translated contact tower has the same actual canonical step formula. -/
theorem selectedStage_canonicalPicard_formula (p : ℕ) (a : k) (n : ℕ) :
    Additive.ofMul (canonicalSheafOfSmoothSurface ((translatedInitial p a).stage (n + 1)).structureMap).toPic =
      Additive.ofMul (schemePicardPullbackHom ((translatedInitial p a).stepProjection n)
        (canonicalSheafOfSmoothSurface ((translatedInitial p a).stage n).structureMap).toPic) +
        cartierPicardHom (selectedStage p a (n + 1))
          (stageExceptionalCartier (translatedInitial p a) n) :=
  stage_canonicalPicard_formula (translatedInitial p a) n

end KltDP.Examples.FrobeniusContactTowerCanonicalFormula
