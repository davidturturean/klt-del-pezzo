import KltDP.Examples.FrobeniusMultiCentreCanonicalTarget
import KltDP.Examples.FrobeniusMultiCentreCanonicalClusterIdeal
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensorSquare

/-!
# The actual canonical tensor target on each original cluster

The actual ideal comparison and the two original open differential maps
identify the pulled global target with the pulled original tower target.
The original tensor comparison preserves both inclusion maps in their common
intrinsic exterior sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalTensorCharts

open KltDP.Geometry FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
open FrobeniusContactTowerCanonicalFactorIdeals FrobeniusContactTowerCanonicalFactorTensorSquare
open FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCanonicalIdealFamily
open FrobeniusMultiCentreCanonicalClusterIdeal FrobeniusMultiCentreCanonicalDifferentialCharts
open FrobeniusMultiCentreCanonicalTarget

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance multiCanonicalTensorChartsModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

/-- The original global and tower top sheaves meet in the same intrinsic cluster top sheaf. -/
def clusterTopIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj (multiTop (q + 1) n a) ≅
      (schemeModulePullback (isoMap q n a i)).obj
        (stageTop (translatedInitial (q + 1) (a i)) (q + 1)) := by
  letI := multiClusterMap_isIso q n a i
  letI := towerClusterMap_isIso q n a i
  exact asIso (multiClusterMap q n a i) ≪≫ (asIso (towerClusterMap q n a i)).symm

/-- This top comparison retains the two original open differentials. -/
theorem clusterTopIso_comp (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterTopIso q n a i).hom ≫ towerClusterMap q n a i = multiClusterMap q n a i := by
  letI := multiClusterMap_isIso q n a i
  letI := towerClusterMap_isIso q n a i
  simp only [clusterTopIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

abbrev towerCanonicalTarget (p : ℕ) (a : k) : (selectedStage p a p).Modules :=
  (towerIdealLine p a).obj ⊗ stageTop (translatedInitial p a) p

def towerCanonicalInclusion (p : ℕ) (a : k) :
    towerCanonicalTarget p a ⟶ stageTop (translatedInitial p a) p :=
  schemeStructureTensorInclusion (towerIdealInclusion p a) (stageTop (translatedInitial p a) p)

/-- The original tensor source and target comparisons on the selected cluster. -/
def clusterTargetMap (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj (multiCanonicalTarget (q + 1) n a) ⟶
      (schemeModulePullback (isoMap q n a i)).obj (towerCanonicalTarget (q + 1) (a i)) :=
  (pullbackTensorSquareIso (isoPreimage q n a i).ι (isoMap q n a i)
    (clusterIdealIso q n a i) (clusterTopIso q n a i)).hom

theorem clusterTargetMap_isIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    IsIso (clusterTargetMap q n a i) := by
  unfold clusterTargetMap
  infer_instance

/-- The actual cluster target isomorphism has exactly that original forward map. -/
def clusterTargetIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj (multiCanonicalTarget (q + 1) n a) ≅
      (schemeModulePullback (isoMap q n a i)).obj (towerCanonicalTarget (q + 1) (a i)) := by
  letI := clusterTargetMap_isIso q n a i
  exact asIso (clusterTargetMap q n a i)

@[simp] theorem clusterTargetIso_hom (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterTargetIso q n a i).hom = clusterTargetMap q n a i := rfl

private def clusterTargetMap_comp_proof (k : Type u) [Field k]
    (q n : ℕ) (a : Fin n → k) (i : Fin n) :=
  pullbackTensorSquareIso_comp (isoPreimage q n a i).ι (isoMap q n a i)
    (clusterIdealIso q n a i) (clusterTopIso q n a i)
    (multiIdealInclusion (q + 1) n a) (towerIdealInclusion (q + 1) (a i))
    (clusterIdealIso_inclusion q n a i)
    (towerClusterMap q n a i) (multiClusterMap q n a i) (clusterTopIso_comp q n a i)

/-- The actual target comparison preserves the original global and tower inclusions. -/
theorem clusterTargetMap_comp (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    clusterTargetMap q n a i ≫
        (schemeModulePullback (isoMap q n a i)).map (towerCanonicalInclusion (q + 1) (a i)) ≫
        towerClusterMap q n a i =
      (schemeModulePullback (isoPreimage q n a i).ι).map
          (multiCanonicalInclusion (q + 1) n a) ≫ multiClusterMap q n a i :=
  clusterTargetMap_comp_proof k q n a i

end KltDP.Examples.FrobeniusMultiCentreCanonicalTensorCharts
