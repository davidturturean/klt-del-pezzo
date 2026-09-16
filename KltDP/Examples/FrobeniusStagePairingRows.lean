import KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue
import KltDP.Geometry.IntersectionPairingSymmetry

/-!
# The Frobenius-stage self-intersection row against the unconditional pairing (F29)

Lanes A2 and F state their intersection-table rows in lane D's `selfIntersectionNumber`. By E6/E7
that number is also the value of the unconditional symmetric bilinear pairing on the class
`[O_S(D_E)]` (`selfIntersection_primeCurveClass`, which needs no hypothesis beyond regularity), so the
row reads as a statement about `L²`.

`stageExceptional_selfIntersection_pairing`: for the exceptional prime curve `E` of stage `n+1` of the
contact tower, `[O_S(D_E)]² = −1` — the pairing form of the accepted
`KltDP.Examples.f09_exceptional_self_intersection`.

**Only this row is stateable from accepted material.** Lane A2's own status records `B·B` and `F̃·F̃`
as untreated upstream, and `C_j·C_j = −2` lives in lane A2's *queued*
`FrobeniusOldExceptionalAdjacentRows`, not in the accepted tree; restating it here would duplicate
another lane's unaccepted module. Once those rows exist upstream, each is a one-line corollary of
`selfIntersection_primeCurveClass` exactly as below.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusStagePairingRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStageExceptionalPullback
open FrobeniusStageExceptionalSelfIntersection

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- **`[O_S(D_E)]² = −1`** for the exceptional curve of stage `n+1`, in the unconditional bilinear
pairing. -/
theorem stageExceptional_selfIntersection_pairing :
    selfIntersection (stageSurface (n + 1) hproj) (stageRegular n hproj)
        (cartierDivisorInvertibleSheaf (stageSurface (n + 1) hproj).toScheme
          ((stageSurface (n + 1) hproj).primeCurveCartier (stageRegular n hproj)
            (exceptionalPrimeCurve n hproj))) = -1 := by
  rw [(stageSurface (n + 1) hproj).selfIntersection_primeCurveClass (stageRegular n hproj)
    (exceptionalPrimeCurve n hproj)]
  exact KltDP.Examples.f09_exceptional_self_intersection k n hproj

end KltDP.Examples.FrobeniusStagePairingRows
