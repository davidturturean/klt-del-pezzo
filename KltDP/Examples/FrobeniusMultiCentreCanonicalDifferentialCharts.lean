import KltDP.Examples.FrobeniusMultiCentreCanonicalOpenComparison
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdeals
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSquare

/-!
# The original finite-centre differential on its actual cover

The cluster square is the accepted identity between the original projections.
The whole-map equation is the proved original exterior differential composition
law. On the unchanged open the actual restricted blowdown is open, so the same
original differential is invertible there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalDifferentialCharts

open KltDP.Geometry KltDP.Geometry.SchemeKaehlerSheaf
open FrobeniusGlobalBlowupStages FrobeniusTranslatedCharts FrobeniusContactTowerSelectedPoint
open FrobeniusGlobalBlowupDifferentialAffine FrobeniusContactTowerCanonicalFactorIdeals
open FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCurveKernels
open FrobeniusMultiCentreIsoOpenClasses FrobeniusMultiCentreCanonicalOpenComparison

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem square_of_map_eq {C : Type*} [Category C] {S P Q R T : C}
    {a a' : S ⟶ P} {b b' : P ⟶ T} {c c' : S ⟶ Q}
    {d d' : Q ⟶ R} {e e' : R ⟶ T}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e')
    (h : a' ≫ b' = c' ≫ d' ≫ e') : a ≫ b = c ≫ d ≫ e := by
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  exact h

variable {k : Type u} [Field k]

abbrev baseTop : (projectiveProductInitial (k := k)).carrier.Modules :=
  oldTop (projectiveProductInitial (k := k))

abbrev multiTop (p n : ℕ) (a : Fin n → k) : (multiSurface p n a).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (multiStructure p n a)) 2

abbrev clusterTop (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (isoPreimage q n a i).toScheme.Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (clusterStructure q n a i)) 2

/-- The original intrinsic top differential of the actual finite-centre projection. -/
def multiDifferentialMap (p n : ℕ) (a : Fin n → k) :
    (schemeModulePullback (multiProjection p n a)).obj (baseTop (k := k)) ⟶ multiTop p n a :=
  SchemeKaehlerExteriorPullbackTransport.map (projectiveProductInitial (k := k)).structureMap
    (multiProjection p n a) (multiStructure p n a) rfl 2

/-- The original differential on the actual global cluster open. -/
def multiClusterMap (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj (multiTop (q + 1) n a) ⟶
      clusterTop q n a i :=
  SchemeKaehlerExteriorPullbackTransport.map (multiStructure (q + 1) n a)
    (isoPreimage q n a i).ι (clusterStructure q n a i) rfl 2

/-- The original tower differential on that same actual cluster open. -/
def towerClusterMap (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoMap q n a i)).obj
        (stageTop (translatedInitial (q + 1) (a i)) (q + 1)) ⟶ clusterTop q n a i :=
  SchemeKaehlerExteriorPullbackTransport.map
    ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap
    (isoMap q n a i) (clusterStructure q n a i) (isoMap_structure q n a i) 2

theorem multiClusterMap_isIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    IsIso (multiClusterMap q n a i) :=
  SchemeKaehlerExteriorPullbackTransport.map_isIso (multiStructure (q + 1) n a)
    (isoPreimage q n a i).ι (clusterStructure q n a i) rfl 2

theorem towerClusterMap_isIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    IsIso (towerClusterMap q n a i) :=
  SchemeKaehlerExteriorPullbackTransport.map_isIso
    ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap
    (isoMap q n a i) (clusterStructure q n a i) (isoMap_structure q n a i) 2

/-- The original pullback-composition source map around the actual projection square. -/
def clusterSourceMap (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj
        ((schemeModulePullback (multiProjection (q + 1) n a)).obj (baseTop (k := k))) ⟶
      (schemeModulePullback (isoMap q n a i)).obj
        ((schemeModulePullback (selectedProjection (q + 1) (a i) (q + 1))).obj
          (baseTop (k := k))) :=
  (SchemeKaehlerExteriorPullbackTransport.squareSourceIso
    (projectiveProductInitial (k := k)).structureMap (multiProjection (q + 1) n a)
    (isoPreimage q n a i).ι (selectedProjection (q + 1) (a i) (q + 1))
    (isoMap q n a i) (ι_multiProjection q n a i) 2).hom

theorem clusterSourceMap_isIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    IsIso (clusterSourceMap q n a i) := by
  unfold clusterSourceMap
  infer_instance

private def clusterSquare_proof (k : Type u) [Field k]
    (q n : ℕ) (a : Fin n → k) (i : Fin n) :=
  SchemeKaehlerExteriorPullbackTransport.map_square
    (projectiveProductInitial (k := k)).structureMap (multiProjection (q + 1) n a)
    (isoPreimage q n a i).ι (selectedProjection (q + 1) (a i) (q + 1))
    (isoMap q n a i) (ι_multiProjection q n a i) 2
    (multiStructure (q + 1) n a) rfl
    ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap
    (selectedProjection_structure (q + 1) (a i) (q + 1))
    (clusterStructure q n a i) rfl (isoMap_structure q n a i)

private theorem multiDifferentialMap_pullback_eq (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).map (multiDifferentialMap (q + 1) n a) =
      (schemeModulePullback (isoPreimage q n a i).ι).map
        (SchemeKaehlerExteriorPullbackTransport.map (projectiveProductInitial (k := k)).structureMap
          (multiProjection (q + 1) n a) (multiStructure (q + 1) n a) rfl 2) := rfl

private theorem multiClusterMap_eq (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    multiClusterMap q n a i =
      SchemeKaehlerExteriorPullbackTransport.map (multiStructure (q + 1) n a)
        (isoPreimage q n a i).ι (clusterStructure q n a i) rfl 2 := rfl

private theorem towerDifferentialMap_pullback_eq (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoMap q n a i)).map
        (towerDifferentialMap (translatedInitial (q + 1) (a i)) (q + 1)) =
      (schemeModulePullback (isoMap q n a i)).map
        (SchemeKaehlerExteriorPullbackTransport.map (projectiveProductInitial (k := k)).structureMap
          (selectedProjection (q + 1) (a i) (q + 1))
          ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap
          (selectedProjection_structure (q + 1) (a i) (q + 1)) 2) := rfl

private theorem towerClusterMap_eq (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    towerClusterMap q n a i =
      SchemeKaehlerExteriorPullbackTransport.map
        ((translatedInitial (q + 1) (a i)).stage (q + 1)).structureMap
        (isoMap q n a i) (clusterStructure q n a i) (isoMap_structure q n a i) 2 := rfl

/-- The actual whole differential restricts to the original selected-tower differential. -/
theorem multiDifferentialMap_cluster (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).map (multiDifferentialMap (q + 1) n a) ≫
        multiClusterMap q n a i =
      clusterSourceMap q n a i ≫
        (schemeModulePullback (isoMap q n a i)).map
          (towerDifferentialMap (translatedInitial (q + 1) (a i)) (q + 1)) ≫
        towerClusterMap q n a i :=
  square_of_map_eq (multiDifferentialMap_pullback_eq q n a i) (multiClusterMap_eq q n a i)
    rfl (towerDifferentialMap_pullback_eq q n a i) (towerClusterMap_eq q n a i)
    (clusterSquare_proof k q n a i)

/-- On the unchanged open the original pulled whole differential is invertible. -/
theorem multiDifferentialMap_complement_isIso (q n : ℕ) (a : Fin n → k) :
    IsIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (multiDifferentialMap (q + 1) n a)) := by
  letI : IsOpenImmersion ((blowdownIsoOpen q n a).ι ≫ multiProjection (q + 1) n a) := by
    rw [← blowdownMap_eq]
    unfold blowdownMap
    infer_instance
  exact SchemeKaehlerExteriorPullbackTransport.pullback_map_isIso_of_open_comp
    (projectiveProductInitial (k := k)).structureMap (multiProjection (q + 1) n a)
    (multiStructure (q + 1) n a) rfl 2 (blowdownIsoOpen q n a).ι

end KltDP.Examples.FrobeniusMultiCentreCanonicalDifferentialCharts
