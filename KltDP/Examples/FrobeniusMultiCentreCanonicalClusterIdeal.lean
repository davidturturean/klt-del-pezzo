import KltDP.Examples.FrobeniusMultiCentreCanonicalIdealFamily
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorFamilyComp

/-!
# The selected ideal tensor is the original completed tower tensor

Use the actual identity between the restricted tower projection and the
original cluster map. The comparison is the original finite tensor pullback
comparison followed by original pullback composition. Combining it with the
proved removal of foreign factors preserves the entire original inclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalClusterIdeal

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphNewest
open FrobeniusContactTowerSelectedPoint FrobeniusContactTowerCanonicalFactorLocalIdeals
open FrobeniusContactTowerCanonicalFactorFiniteTensor FrobeniusContactTowerCanonicalFactorFamilyComp
open FrobeniusMultiCentreCanonicalIdealFamily

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The finite tensor of the already accepted total exceptional lines on their original tower. -/
def towerIdealLine (p : ℕ) (a : k) : InvertibleSheaf (selectedStage p a p) :=
  familyLine p (towerExceptionalLine p a)

/-- Its product of the original total exceptional inclusions. -/
def towerIdealInclusion (p : ℕ) (a : k) :
    (towerIdealLine p a).obj ⟶ _root_.SheafOfModules.unit (selectedStage p a p).ringCatSheaf :=
  familyInclusion p (towerExceptionalLine p a) (towerTotalExceptionalInclusion p a)

/-- The actual original pullback-composition map for the selected cluster family. -/
def clusterToTowerFamilyMap (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (clusterIdealLine (q + 1) n a i).obj ⟶
      (schemeModulePullback (isoMap q n a i)).obj (towerIdealLine (q + 1) (a i)).obj :=
  familyCompositeMap (towerProjection (q + 1) n a i) (isoPreimage q n a i).ι
    (isoMap q n a i) (isoMap_eq q n a i).symm (q + 1) (towerExceptionalLine (q + 1) (a i))

theorem clusterToTowerFamilyMap_isIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    IsIso (clusterToTowerFamilyMap q n a i) :=
  familyCompositeMap_isIso (towerProjection (q + 1) n a i) (isoPreimage q n a i).ι
    (isoMap q n a i) (isoMap_eq q n a i).symm (q + 1) (towerExceptionalLine (q + 1) (a i))

/-- Its inverse is attached to that same original map. -/
def clusterToTowerFamilyIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        (clusterIdealLine (q + 1) n a i).obj ≅
      (schemeModulePullback (isoMap q n a i)).obj (towerIdealLine (q + 1) (a i)).obj := by
  letI := clusterToTowerFamilyMap_isIso q n a i
  exact asIso (clusterToTowerFamilyMap q n a i)

@[simp] theorem clusterToTowerFamilyIso_hom (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterToTowerFamilyIso q n a i).hom = clusterToTowerFamilyMap q n a i := rfl

/-- The original tower map retains its actual pulled inclusion. -/
theorem clusterToTowerFamilyMap_inclusion (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    clusterToTowerFamilyMap q n a i ≫
        (schemeModulePullback (isoMap q n a i)).map (towerIdealInclusion (q + 1) (a i)) ≫
        (schemeModulePullbackUnitIso (isoMap q n a i)).hom =
      (schemeModulePullback (isoPreimage q n a i).ι).map
          (clusterIdealInclusion (q + 1) n a i) ≫
        (schemeModulePullbackUnitIso (isoPreimage q n a i).ι).hom :=
  familyCompositeMap_inclusion (towerProjection (q + 1) n a i) (isoPreimage q n a i).ι
    (isoMap q n a i) (isoMap_eq q n a i).symm (q + 1) (towerExceptionalLine (q + 1) (a i))
    (towerTotalExceptionalInclusion (q + 1) (a i))

/-- Restrict the actual whole ideal tensor to the original selected tower tensor. -/
def clusterIdealIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj (multiIdealLine (q + 1) n a).obj ≅
      (schemeModulePullback (isoMap q n a i)).obj (towerIdealLine (q + 1) (a i)).obj :=
  clusterIdealSelectionIso q n a i ≪≫ clusterToTowerFamilyIso q n a i

/-- The full cluster comparison is normalized by the original entire exceptional inclusion. -/
theorem clusterIdealIso_inclusion (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterIdealIso q n a i).hom ≫
        (schemeModulePullback (isoMap q n a i)).map (towerIdealInclusion (q + 1) (a i)) ≫
        (schemeModulePullbackUnitIso (isoMap q n a i)).hom =
      (schemeModulePullback (isoPreimage q n a i).ι).map
          (multiIdealInclusion (q + 1) n a) ≫
        (schemeModulePullbackUnitIso (isoPreimage q n a i).ι).hom := by
  simp only [clusterIdealIso, Iso.trans_hom, clusterToTowerFamilyIso_hom, Category.assoc]
  rw [clusterToTowerFamilyMap_inclusion]
  exact clusterIdealSelectionIso_inclusion q n a i

end KltDP.Examples.FrobeniusMultiCentreCanonicalClusterIdeal
