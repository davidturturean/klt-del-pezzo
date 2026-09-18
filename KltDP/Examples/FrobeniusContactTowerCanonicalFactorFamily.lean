import KltDP.Examples.FrobeniusContactTowerCanonicalFactorFiniteTensor
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorTotalLines
import KltDP.Examples.FrobeniusContactTowerCanonicalFactor

/-!
# The normalized tower factor on the original finite total-exceptional family

Compare the recursive actual exceptional tensor with the finite tensor of
the actual total transforms. The individual comparisons retain the original
inclusions, so their finite tensor does too. Transport the compiled whole-tower
canonical factor through this same-object comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorFamily

open KltDP.Geometry FrobeniusGlobalBlowupStages
open FrobeniusGlobalBlowupDifferentialAffine
open FrobeniusContactTowerCanonicalFactorTensor FrobeniusContactTowerCanonicalFactorIdeals
open FrobeniusContactTowerCanonicalFactorFiniteTensor FrobeniusContactTowerCanonicalFactorTotalLines
open FrobeniusContactTowerCanonicalFactor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance familyFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

/-- The finite tensor of the original total exceptional lines on the same whole stage. -/
abbrev totalFamilyLine (N : ℕ) : InvertibleSheaf (A.stage N).carrier :=
  familyLine N (totalLine A N)

/-- Its product of the original total exceptional inclusions. -/
def totalFamilyInclusion (N : ℕ) :
    (totalFamilyLine A N).obj ⟶ _root_.SheafOfModules.unit (A.stage N).carrier.ringCatSheaf :=
  familyInclusion N (totalLine A N) (totalInclusion A N)

/-- Tensor the original old-index pullback comparisons on the actual successor stage. -/
def castSuccFamilyIso (N : ℕ) :
    (familyLine N (fun j => pullbackInvertibleSheaf (A.stepProjection N)
      (totalLine A N j))).obj ≅
    (familyLine N (fun j => totalLine A (N + 1) j.castSucc)).obj :=
  familyIso N _ _ (castSuccIso A N)

/-- The old-index family retains the original pulled inclusions. -/
theorem castSuccFamilyIso_inclusion (N : ℕ) :
    (castSuccFamilyIso A N).hom ≫
      familyInclusion N (fun j => totalLine A (N + 1) j.castSucc)
        (fun j => totalInclusion A (N + 1) j.castSucc) =
    familyInclusion N
      (fun j => pullbackInvertibleSheaf (A.stepProjection N) (totalLine A N j))
      (fun j => (schemeModulePullback (A.stepProjection N)).map (totalInclusion A N j) ≫
        (schemeModulePullbackUnitIso (A.stepProjection N)).hom) := by
  simpa only [castSuccFamilyIso] using
    (familyIso_comp (X := (A.stage (N + 1)).carrier) N
      (fun j => pullbackInvertibleSheaf (A.stepProjection N) (totalLine A N j))
      (fun j => totalLine A (N + 1) j.castSucc) (castSuccIso A N)
      (fun j => (schemeModulePullback (A.stepProjection N)).map (totalInclusion A N j) ≫
        (schemeModulePullbackUnitIso (A.stepProjection N)).hom)
      (fun j => totalInclusion A (N + 1) j.castSucc) (castSuccIso_inclusion A N))

/-- The recursive tensor and the finite original total-transform tensor are isomorphic. -/
def recursiveToFamilyIso : (N : ℕ) →
    ((totalExceptionalIdealLine A N).obj ≅ (totalFamilyLine A N).obj)
  | 0 => Iso.refl _
  | N + 1 => tensorIso
      ((schemeModulePullback (A.stepProjection N)).mapIso (recursiveToFamilyIso N) ≪≫
        familyPullbackIso (A.stepProjection N) N (totalLine A N) ≪≫ castSuccFamilyIso A N)
      (lastIso A N).symm

/-- This isomorphism retains the original full product inclusion. -/
theorem recursiveToFamilyIso_inclusion (N : ℕ) :
    (recursiveToFamilyIso A N).hom ≫ totalFamilyInclusion A N =
      totalExceptionalInclusion A N := by
  induction N with
  | zero =>
      change (𝟙 (_root_.SheafOfModules.unit A.carrier.ringCatSheaf)) ≫ 𝟙 _ = 𝟙 _
      exact Category.id_comp _
  | succ N ih =>
      have hlast :
          (lastIso A N).inv ≫ totalInclusion A (N + 1) (Fin.last N) = stepInclusion A N := by
        rw [← lastIso_inclusion, Iso.inv_hom_id_assoc]
      have hprev :
          (recursiveToFamilyIso A N).hom ≫
            familyInclusion N (totalLine A N) (totalInclusion A N) =
          totalExceptionalInclusion A N := ih
      change (tensorIso
        ((schemeModulePullback (A.stepProjection N)).mapIso (recursiveToFamilyIso A N) ≪≫
          familyPullbackIso (A.stepProjection N) N (totalLine A N) ≪≫ castSuccFamilyIso A N)
        (lastIso A N).symm).hom ≫
          productInclusion
            (familyInclusion N (fun j => totalLine A (N + 1) j.castSucc)
              (fun j => totalInclusion A (N + 1) j.castSucc))
            (totalInclusion A (N + 1) (Fin.last N)) =
        productInclusion
          ((schemeModulePullback (A.stepProjection N)).map (totalExceptionalInclusion A N) ≫
            (schemeModulePullbackUnitIso (A.stepProjection N)).hom) (stepInclusion A N)
      rw [tensorIso_productInclusion, Iso.symm_hom, hlast]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [castSuccFamilyIso_inclusion, familyPullbackIso_comp,
        ← Functor.map_comp_assoc, hprev]

variable [IsSmoothOfRelativeDimension 2 A.structureMap]

/-- The original whole-tower canonical factor, now on the original finite total-exceptional family. -/
def towerCanonicalFamilyIso (N : ℕ) :
    (schemeModulePullback (A.toInitial N)).obj (oldTop A) ≅
      (totalFamilyLine A N).obj ⊗ stageTop A N :=
  towerCanonicalFactorIso A N ≪≫
    tensorIso (recursiveToFamilyIso A N) (Iso.refl (stageTop A N))

/-- Its inclusion remains exactly the original composite-projection exterior differential. -/
theorem towerCanonicalFamilyIso_comp (N : ℕ) :
    (towerCanonicalFamilyIso A N).hom ≫
        schemeStructureTensorInclusion (totalFamilyInclusion A N) (stageTop A N) =
      towerDifferentialMap A N := by
  simp only [towerCanonicalFamilyIso, Iso.trans_hom, Category.assoc]
  rw [tensorIso_structureInclusion, recursiveToFamilyIso_inclusion]
  simp only [Iso.refl_hom, Category.comp_id]
  exact towerCanonicalFactorIso_comp A N

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorFamily
