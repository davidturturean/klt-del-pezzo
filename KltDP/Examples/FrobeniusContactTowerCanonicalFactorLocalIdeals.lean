import KltDP.Examples.FrobeniusContactTowerCanonicalFactorOffRange
import KltDP.Examples.FrobeniusMultiCentreCrossClusterRestrictions
import KltDP.Examples.FrobeniusMultiCentreIsoOpenClasses

/-!
# Original total exceptional inclusions on the finite-centre cover

The lines are exactly the accepted total exceptional lines, pulled by the
original tower projections. The existing geometric disjointness theorems
make their original inclusions invertible on foreign-cluster and unchanged
opens. The two actual pullback-composition comparisons retain those maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorLocalIdeals

open KltDP.Geometry
open FrobeniusContactTowerCanonicalFactorOffRange
open FrobeniusGlobalBlowupStages FrobeniusExceptionalFinalConfiguration
open FrobeniusContactTowerSelectedPoint FrobeniusTranslatedCharts
open FrobeniusGlobalExceptionalSuccessor FrobeniusMultiCentreSurface
open FrobeniusMultiCentreGraphNewest FrobeniusMultiCentreCurveKernels
open FrobeniusMultiCentreCrossClusterRestrictions FrobeniusMultiCentreIsoOpenClasses

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem pulledInclusion_of_comp_isIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((schemeModulePullback (g ≫ f)).map i ≫
      (schemeModulePullbackUnitIso (g ≫ f)).hom)] :
    IsIso ((schemeModulePullback g).map
      ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) ≫
      (schemeModulePullbackUnitIso g).hom) := by
  rw [← pulledInclusion_comp f g i]
  infer_instance

variable {k : Type u} [Field k]

/-- The original inclusion of the accepted total exceptional line on its completed tower. -/
def towerTotalExceptionalInclusion (p : ℕ) (c : k) (j : Fin p) :
    (towerExceptionalLine p c j).obj ⟶
      _root_.SheafOfModules.unit (selectedStage p c p).ringCatSheaf :=
  pulledKernelInclusion (previousFiberι ((translatedInitial p c).stage j.val))
    (between (translatedInitial p c) j.isLt)

/-- The original inclusion of the same accepted line pulled to the finite-centre surface. -/
def multiTotalExceptionalInclusion (p n : ℕ) (a : Fin n → k) (i : Fin n) (j : Fin p) :
    (pullbackInvertibleSheaf (towerProjection p n a i) (towerExceptionalLine p (a i) j)).obj ⟶
      _root_.SheafOfModules.unit (multiSurface p n a).ringCatSheaf :=
  (schemeModulePullback (towerProjection p n a i)).map
      (towerTotalExceptionalInclusion p (a i) j) ≫
    (schemeModulePullbackUnitIso (towerProjection p n a i)).hom

/-- The actual inclusion of a foreign total exceptional line is invertible on the cluster open. -/
theorem multiTotalExceptionalInclusion_cluster_isIso (q n : ℕ) (a : Fin n → k)
    {i i' : Fin n} (hii' : i' ≠ i) (j : Fin (q + 1)) :
    IsIso ((schemeModulePullback (isoPreimage q n a i).ι).map
      (multiTotalExceptionalInclusion (q + 1) n a i' j) ≫
      (schemeModulePullbackUnitIso (isoPreimage q n a i).ι).hom) := by
  let b := between (translatedInitial (q + 1) (a i')) j.isLt
  let t := towerProjection (q + 1) n a i'
  let l := (isoPreimage q n a i).ι
  let d := previousFiberι ((translatedInitial (q + 1) (a i')).stage j.val)
  letI : IsIso ((schemeModulePullback ((l ≫ t) ≫ b)).map (schemeKernelIdealι d) ≫
      (schemeModulePullbackUnitIso ((l ≫ t) ≫ b)).hom) :=
    pulledKernelInclusion_isIso_of_disjoint d ((l ≫ t) ≫ b)
      (disjoint_cluster_previousFiber q n a hii' j)
  letI : IsIso ((schemeModulePullback (l ≫ t)).map
      (towerTotalExceptionalInclusion (q + 1) (a i') j) ≫
      (schemeModulePullbackUnitIso (l ≫ t)).hom) :=
    pulledInclusion_of_comp_isIso b (l ≫ t) (schemeKernelIdealι d)
  exact pulledInclusion_of_comp_isIso t l (towerTotalExceptionalInclusion (q + 1) (a i') j)

/-- The actual inclusion of every total exceptional line is invertible on the unchanged open. -/
theorem multiTotalExceptionalInclusion_complement_isIso (q n : ℕ) (a : Fin n → k)
    (i : Fin n) (j : Fin (q + 1)) :
    IsIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (multiTotalExceptionalInclusion (q + 1) n a i j) ≫
      (schemeModulePullbackUnitIso (blowdownIsoOpen q n a).ι).hom) := by
  let b := between (translatedInitial (q + 1) (a i)) j.isLt
  let t := towerProjection (q + 1) n a i
  let l := (blowdownIsoOpen q n a).ι
  let d := previousFiberι ((translatedInitial (q + 1) (a i)).stage j.val)
  letI : IsIso ((schemeModulePullback ((l ≫ t) ≫ b)).map (schemeKernelIdealι d) ≫
      (schemeModulePullbackUnitIso ((l ≫ t) ≫ b)).hom) :=
    pulledKernelInclusion_isIso_of_disjoint d ((l ≫ t) ≫ b)
      (disjoint_isoOpen_previousFiber q n a i j)
  letI : IsIso ((schemeModulePullback (l ≫ t)).map
      (towerTotalExceptionalInclusion (q + 1) (a i) j) ≫
      (schemeModulePullbackUnitIso (l ≫ t)).hom) :=
    pulledInclusion_of_comp_isIso b (l ≫ t) (schemeKernelIdealι d)
  exact pulledInclusion_of_comp_isIso t l (towerTotalExceptionalInclusion (q + 1) (a i) j)

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorLocalIdeals

