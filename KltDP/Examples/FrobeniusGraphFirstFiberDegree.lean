import KltDP.Examples.FrobeniusVerticalPicardBridge
import KltDP.Examples.FrobeniusGraphVerticalDegree
import KltDP.Examples.FrobeniusStrictTransformPairing

/-!
# The strict graph has intersection one with the first fibre class

The actual divisor `stageVerticalDivisor (n + 1) 1` has the accepted total first fibre class by
`FrobeniusVerticalPicardBridge`. Its intersection number with the strict graph is one by the
geometric local-length and singleton-support computation in `FrobeniusGraphVerticalDegree`.
The defining Cartier-to-Picard comparison for restriction degree therefore proves the row
`B · a = 1` without a class-identification or local-degree premise.

Algebraic closure and projectivity of the contact stage remain explicit hypotheses, as in the
intersection-number theorem. This proves one row; the other F29 rows and global example theorems
remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGraphFirstFiberDegree

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformPairing
open FrobeniusVerticalPicardBridge FrobeniusStageVerticalDivisor FrobeniusGraphVerticalDegree

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The actual strict graph has degree one against the first fibre class, conditional only on the
same algebraic closure and stage projectivity as the geometric intersection computation. -/
theorem graphStrictPairing_firstFiberTotalClass_eq_one (m : ℕ) :
    graphStrictPairing n hproj m (firstFiberTotalClass (n + 1)) = 1 := by
  rw [← stageVerticalDivisor_picard_eq_firstFiberTotalClass (k := k) (n + 1) (1 : k)]
  change (stageSurface (n + 1) hproj).picardRestrictionDegreeHom
    (graphStrictPrimeCurve n hproj m)
    (cartierPicardHom (stageSurface (n + 1) hproj).toScheme
      (stageVerticalDivisor (k := k) (n + 1) (1 : k))) = 1
  rw [(graphStrictPrimeCurve n hproj m).picardRestrictionDegreeHom_cartierPicardHom]
  exact graphStrict_intersectionNumber_vertical_eq_one n hproj m 1 one_ne_zero

end KltDP.Examples.FrobeniusGraphFirstFiberDegree
