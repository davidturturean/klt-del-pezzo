import KltDP.Examples.FrobeniusGlobalBlowupCanonicalPicard
import KltDP.Geometry.PointBlowupExceptionalCartier
import KltDP.Geometry.SchemeKernelGluedIso

/-!
# The whole-stage canonical formula with the original exceptional Cartier divisor

Reuse the accepted exceptional Cartier divisor of the original entire center
fiber. The accepted kernel/glued-kernel comparison identifies its ideal-line
Picard class with the same original kernel used by the differential factor.
This proves K_new = pullback K_old + E on the entire original next scheme.
Integrality is retained precisely where the existing Cartier type requires it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupCanonicalExceptionalCartier

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalBlowupCanonicalTarget FrobeniusGlobalBlowupCanonicalPicard

variable {k : Type u} [Field k]

local instance wholeCartierOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

variable (A : PlaneChartedScheme k) [IsIntegral A.nextScheme]

/-- The accepted original Cartier divisor of the entire original center fiber. -/
abbrev wholeExceptionalCartier : CartierDivisor A.nextScheme :=
  PointBlowupExceptionalCartier.exceptionalCartierDivisor
    A.chart (originPoint (k := k)) A.center_closed

/-- Its class is the negative of the same original exceptional kernel line. -/
theorem wholeExceptionalCartier_picard :
    cartierPicardHom A.nextScheme (wholeExceptionalCartier A) =
      -Additive.ofMul (wholeExceptionalIdealLine A).toPic := by
  have h := toPic_eq_gluedKernelLine
    (PointBlowupGluing.globalCenterFiberι A.chart (originPoint (k := k)) A.center_closed)
    (PointBlowupGluing.globalCenterFiberIdeal_isInvertible
      A.chart (originPoint (k := k)) A.center_closed)
    (PointBlowupExceptionalCartier.exceptionalKer_locallyPrincipalRegular
      A.chart (originPoint (k := k)) A.center_closed)
  rw [wholeExceptionalCartier, PointBlowupExceptionalCartier.exceptionalCartierDivisor,
    cartierDivisorOfIdeal_picard]
  exact congrArg (fun z => -Additive.ofMul z) h.symm

variable [IsSmoothOfRelativeDimension 2 A.structureMap]

/-- The actual one-step canonical formula on the entire original blowup stage. -/
theorem canonicalSheafPicard_formula_exceptional :
    Additive.ofMul (canonicalSheafOfSmoothSurface A.nextStructure).toPic =
      Additive.ofMul (schemePicardPullbackHom A.nextProjection
        (canonicalSheafOfSmoothSurface A.structureMap).toPic) +
        cartierPicardHom A.nextScheme (wholeExceptionalCartier A) := by
  rw [wholeExceptionalCartier_picard, ← sub_eq_add_neg]
  exact canonicalSheafPicard_formula A

end KltDP.Examples.FrobeniusGlobalBlowupCanonicalExceptionalCartier
