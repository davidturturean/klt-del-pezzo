import KltDP.Examples.EqualityAppendixSurface
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses

/-!
# Actual integral Picard data for the appendix Q₁ calculation

All classes are classes of original pulled invertible sheaves on the
mixed surface. The total Q₁ transform has class `2a+b`. The strict-transform
formula additionally requires removing the proved local exceptional
multiplicities; it is not assumed or asserted by this data module.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.EqualityAppendixQ1PicardData

open KltDP.Geometry FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
  FrobeniusMultiCentreSurface FrobeniusContactTowerInfinity
  FrobeniusExceptionalFinalConfiguration FrobeniusGraphPicardClassFrames
  FrobeniusGraphPicardClassFiberClasses EqualityAppendixSurface

variable {k : Type u} [Field k] [CharP k 3]

local instance originPoint_asIdeal_isMaximal :
    (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- The actual total transform of the original `y=x²` graph ideal. -/
def totalIdealLine : InvertibleSheaf (surface (k := k)) :=
  pullbackInvertibleSheaf projection (graphIdealLine 2)

def totalClass : Additive (surface (k := k)).Pic :=
  -Additive.ofMul (totalIdealLine (k := k)).toPic

def firstFiberClass : Additive (surface (k := k)).Pic :=
  (schemePicardPullbackHom projection).toAdditive
    (FrobeniusGraphPicardClassFiberClasses.firstFiberClass (k := k))

def secondFiberClass : Additive (surface (k := k)).Pic :=
  (schemePicardPullbackHom projection).toAdditive
    (FrobeniusGraphPicardClassFiberClasses.secondFiberClass (k := k))

/-- This is an equality in the actual integral Picard group of the mixed surface. -/
theorem totalClass_eq :
    totalClass (k := k) = 2 • firstFiberClass + secondFiberClass := by
  let P := schemePicardPullbackHom (projection (k := k))
  have h := congrArg P.toAdditive
    (inverse_graphIdeal_picard_eq_actual_fibers (k := k) 2)
  simp only [map_neg, map_add, map_nsmul] at h
  change -Additive.ofMul (P (graphIdealLine 2).toPic) =
    2 • P.toAdditive FrobeniusGraphPicardClassFiberClasses.firstFiberClass +
      P.toAdditive FrobeniusGraphPicardClassFiberClasses.secondFiberClass at h
  simpa only [P, schemePicardPullbackHom_toPic,
    totalClass, totalIdealLine, firstFiberClass, secondFiberClass] using h

/-- Original total exceptional classes from the finite towers at zero and one. -/
def finiteExceptionalClass (i : Fin 2) (j : Fin 3) : Additive (surface (k := k)).Pic :=
  (schemePicardPullbackHom (pullback.fst finiteProjection (infinityProjection 3))).toAdditive
    (exceptionalClass 3 2 finiteParameters i j)

/-- The original exceptional ideal of an infinity blowup, pulled to its final tower stage. -/
def infinityExceptionalLine (j : Fin 3) : InvertibleSheaf (infinityStage (k := k) 3) :=
  pullbackInvertibleSheaf
    (between (infinityInitial k) (show j.val + 1 ≤ 3 from j.isLt))
    (PointBlowupGluing.globalCenterFiberIdealLine
      ((infinityInitial k).stage j.val).chart (originPoint (k := k))
      ((infinityInitial k).stage j.val).center_closed)

def infinityExceptionalClass (j : Fin 3) : Additive (surface (k := k)).Pic :=
  -Additive.ofMul (pullbackInvertibleSheaf
    (pullback.snd finiteProjection (infinityProjection 3)) (infinityExceptionalLine j)).toPic

end KltDP.Examples.EqualityAppendixQ1PicardData
