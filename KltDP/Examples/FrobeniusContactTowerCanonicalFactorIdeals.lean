import KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensor
import KltDP.Examples.FrobeniusGlobalBlowupCanonicalTarget
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSource

/-!
# The actual iterated exceptional ideal tensor

At each original stage, pull back the preceding tensor line and tensor it
with the original new center-fiber ideal line. Its map into the structure
module is the product of the two original maps. These are actual module
sheaves and morphisms, before any Picard class is taken.

The differential below is independently the original exterior pullback map
of the actual composite tower projection. Its successor equation comes
from the already proved composition theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdeals

open KltDP.Geometry FrobeniusGlobalBlowupStages
open FrobeniusGlobalBlowupDifferentialAffine FrobeniusGlobalBlowupCanonicalTarget
open FrobeniusContactTowerCanonicalFactorTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorIdealModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

/-- The tensor of the actual total transforms of all preceding step ideals. -/
def totalExceptionalIdealLine : (n : ℕ) → InvertibleSheaf (A.stage n).carrier
  | 0 => InvertibleSheaf.trivial A.carrier
  | n + 1 => tensorLine
      (pullbackInvertibleSheaf (A.stepProjection n) (totalExceptionalIdealLine n))
      (wholeExceptionalIdealLine (A.stage n))

/-- The actual inclusion product, pulled and multiplied using the original comparisons. -/
def totalExceptionalInclusion : (n : ℕ) →
    (totalExceptionalIdealLine A n).obj ⟶
      _root_.SheafOfModules.unit (A.stage n).carrier.ringCatSheaf
  | 0 => 𝟙 _
  | n + 1 => productInclusion
      ((schemeModulePullback (A.stepProjection n)).map (totalExceptionalInclusion n) ≫
        (schemeModulePullbackUnitIso (A.stepProjection n)).hom)
      (wholeExceptionalInclusion (A.stage n))

/-- The original intrinsic top differential sheaf on the actual stage. -/
abbrev stageTop (n : ℕ) : (A.stage n).carrier.Modules := oldTop (A.stage n)

/-- The actual ideal tensor acting on the actual top differential sheaf. -/
abbrev towerCanonicalTarget (n : ℕ) : (A.stage n).carrier.Modules :=
  (totalExceptionalIdealLine A n).obj ⊗ stageTop A n

/-- Its original map to the top differential sheaf. -/
def towerCanonicalInclusion (n : ℕ) : towerCanonicalTarget A n ⟶ stageTop A n :=
  schemeStructureTensorInclusion (totalExceptionalInclusion A n) (stageTop A n)

/-- The original exterior differential of the actual composite projection. -/
def towerDifferentialMap (n : ℕ) :
    (schemeModulePullback (A.toInitial n)).obj (oldTop A) ⟶ stageTop A n :=
  SchemeKaehlerExteriorPullbackTransport.map A.structureMap (A.toInitial n)
    (A.stage n).structureMap (A.toInitial_structure n) 2

/-- The original pullback composition isomorphism for the actual successor projection. -/
def towerSourceIso (n : ℕ) :
    (schemeModulePullback (A.stepProjection n)).obj
        ((schemeModulePullback (A.toInitial n)).obj (oldTop A)) ≅
      (schemeModulePullback (A.toInitial (n + 1))).obj (oldTop A) :=
  SchemeKaehlerExteriorPullbackTransport.sourceIso A.structureMap
    (A.toInitial n) (A.stepProjection n) (A.toInitial (n + 1)) rfl 2

/-- The independently defined original tower differential composes one actual step at a time. -/
theorem towerDifferentialMap_succ (n : ℕ) :
    (schemeModulePullback (A.stepProjection n)).map (towerDifferentialMap A n) ≫
        nextDifferentialMap (A.stage n) =
      (towerSourceIso A n).hom ≫ towerDifferentialMap A (n + 1) :=
  SchemeKaehlerExteriorPullbackTransport.map_comp_sourceIso A.structureMap
    (A.toInitial n) (A.stepProjection n) (A.stage n).structureMap (A.toInitial_structure n)
    (A.toInitial (n + 1)) rfl (A.stage (n + 1)).structureMap rfl
    (A.toInitial_structure (n + 1)) 2

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdeals

