import KltDP.Examples.FrobeniusMultiCentreCanonicalTensorCharts
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorFamily

/-!
# The original canonical factor on an actual finite-centre cluster

Use the compiled original tower factor, with the same accepted total
exceptional lines. Transport it through the original projection source
comparison and the normalized original ideal/top target comparison. Its
composite is exactly the pulled original finite-centre differential.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalClusterFactor

open KltDP.Geometry FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
open FrobeniusContactTowerCanonicalFactorIdeals FrobeniusContactTowerCanonicalFactorFamily
open FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCanonicalDifferentialCharts
open FrobeniusMultiCentreCanonicalTarget FrobeniusMultiCentreCanonicalTensorCharts

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The original tower factor on the literally identical accepted total-exceptional family. -/
def towerCanonicalIdealFactorIso (p : ℕ) (a : k) :
    (schemeModulePullback (selectedProjection p a p)).obj (baseTop (k := k)) ≅
      FrobeniusMultiCentreCanonicalTensorCharts.towerCanonicalTarget p a :=
  towerCanonicalFamilyIso (translatedInitial p a) p

/-- Its map is normalized by the original accepted tower total-exceptional inclusions. -/
theorem towerCanonicalIdealFactorIso_comp (p : ℕ) (a : k) :
    (towerCanonicalIdealFactorIso p a).hom ≫ towerCanonicalInclusion p a =
      towerDifferentialMap (translatedInitial p a) p :=
  towerCanonicalFamilyIso_comp (translatedInitial p a) p

/-- The actual tower factor transported through the original global cluster square. -/
def clusterCanonicalFactorIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        ((schemeModulePullback (FrobeniusMultiCentreSurface.multiProjection (q + 1) n a)).obj
          (baseTop (k := k))) ≅
      (schemeModulePullback (isoPreimage q n a i).ι).obj (multiCanonicalTarget (q + 1) n a) := by
  letI := clusterSourceMap_isIso q n a i
  exact asIso (clusterSourceMap q n a i) ≪≫
    (schemeModulePullback (isoMap q n a i)).mapIso (towerCanonicalIdealFactorIso (q + 1) (a i)) ≪≫
    (clusterTargetIso q n a i).symm

/-- Its original inclusion is exactly the original restricted whole differential. -/
theorem clusterCanonicalFactorIso_comp (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterCanonicalFactorIso q n a i).hom ≫
        (schemeModulePullback (isoPreimage q n a i).ι).map (multiCanonicalInclusion (q + 1) n a) =
      (schemeModulePullback (isoPreimage q n a i).ι).map (multiDifferentialMap (q + 1) n a) := by
  letI := multiClusterMap_isIso q n a i
  apply (cancel_mono (multiClusterMap q n a i)).mp
  simp only [clusterCanonicalFactorIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [← clusterTargetMap_comp, ← clusterTargetIso_hom, Iso.inv_hom_id_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, towerCanonicalIdealFactorIso_comp]
  exact (multiDifferentialMap_cluster q n a i).symm

end KltDP.Examples.FrobeniusMultiCentreCanonicalClusterFactor
