import KltDP.Examples.FrobeniusStageCanonicalPairing
import KltDP.Geometry.SmoothCanonicalCartierPicard

/-!
# The actual canonical Cartier divisor on the newest exceptional curve

The chosen Cartier divisor comes from the previously constructed top-differential
line on the original smooth stage. The proved Picard-class comparison and the
whole-stage canonical formula give its intersection with the newest exceptional
curve. Projectivity of that actual stage is retained for the degree pairing.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusStageCanonicalCartier

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open SmoothCanonicalCartierRepresentative SmoothCanonicalCartierPicard
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth
open FrobeniusStageSurface FrobeniusStageCanonicalPairing

variable {k : Type u} [Field k]

local instance canonicalProductIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The actual Cartier representative of the original stage's top-differential line. -/
abbrev canonicalCartier (N : ℕ) :
    CartierDivisor (projectiveContactStage (k := k) N) :=
  cartierRepresentative ((projectiveProductInitial (k := k)).stage N).structureMap

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The actual canonical Cartier divisor has degree minus one on the newest exceptional curve. -/
theorem exceptional_canonicalIntersection :
    (exceptionalPrimeCurve n hproj).intersectionNumber (canonicalCartier (k := k) (n + 1)) =
      -1 := by
  rw [← (exceptionalPrimeCurve n hproj).picardRestrictionDegreeHom_cartierPicardHom]
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom
    (exceptionalPrimeCurve n hproj)
    (cartierPicardHom (projectiveContactStage (k := k) (n + 1))
      (cartierRepresentative ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)) = -1
  rw [cartierPicardHom_representative]
  exact exceptionalPairing_canonical n hproj

/-- Negating that same Cartier divisor gives exceptional degree one. -/
theorem exceptional_antiCanonicalIntersection :
    (exceptionalPrimeCurve n hproj).intersectionNumber (-canonicalCartier (k := k) (n + 1)) =
      1 := by
  rw [(exceptionalPrimeCurve n hproj).intersectionNumber_neg,
    exceptional_canonicalIntersection]
  norm_num

end KltDP.Examples.FrobeniusStageCanonicalCartier
