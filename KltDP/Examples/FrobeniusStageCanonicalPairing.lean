import KltDP.Examples.FrobeniusGlobalBlowupCanonicalPicard
import KltDP.Examples.FrobeniusStageExceptionalPairing

/-!
# The actual canonical class on the newest original exceptional curve

The original whole-stage differential comparison supplies the canonical
Picard formula. The accepted exceptional restriction-degree homomorphism
annihilates every original pullback and takes value minus one on the same
original exceptional class. Its value on the actual canonical line follows.
The original stage projectivity hypothesis is retained for the degree pairing.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusStageCanonicalPairing

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth
open FrobeniusGlobalBlowupCanonicalTarget FrobeniusGlobalBlowupCanonicalPicard
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformPicardStep
open FrobeniusStageExceptionalPairing

variable {k : Type u} [Field k]

local instance canonicalProductIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The proved whole-stage formula, expressed with the original exceptional class. -/
private theorem canonical_class_succ (n : ℕ) :
    Additive.ofMul (canonicalSheafOfSmoothSurface
      ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap).toPic =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (Additive.ofMul (canonicalSheafOfSmoothSurface
          ((projectiveProductInitial (k := k)).stage n).structureMap).toPic) +
        stepExceptionalPicardClass n := by
  have h := canonicalSheafPicard_formula ((projectiveProductInitial (k := k)).stage n)
  simpa only [sub_eq_add_neg] using h

variable [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The newest actual exceptional curve has canonical degree minus one. -/
theorem exceptionalPairing_canonical :
    exceptionalPairing n hproj
      (Additive.ofMul (canonicalSheafOfSmoothSurface
        ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap).toPic) = -1 := by
  rw [canonical_class_succ, map_add, exceptionalPairing_pullback, exceptionalPairing_self,
    zero_add]

end KltDP.Examples.FrobeniusStageCanonicalPairing
