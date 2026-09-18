import KltDP.Examples.FrobeniusContactTowerCanonicalFactorPullbackFamily
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorLocalIdeals

/-!
# The original exceptional ideal tensor on the finite-centre surface

The line is the ordered double tensor of the accepted total exceptional ideal
lines, pulled by the original tower projections. Its inclusion multiplies their
original inclusions. On a cluster open all foreign cluster factors are removed
by these actual invertible maps; on the unchanged open the whole inclusion is
invertible. Every comparison retains the original product map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalIdealFamily

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphNewest
open FrobeniusMultiCentreCurveKernels FrobeniusContactTowerCanonicalFactorLocalIdeals
open FrobeniusContactTowerCanonicalFactorFiniteTensor
open FrobeniusContactTowerCanonicalFactorPullbackFamily

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- The actual tensor of one tower's accepted total exceptional lines on the whole surface. -/
def clusterIdealLine (p n : ℕ) (a : Fin n → k) (i : Fin n) :
    InvertibleSheaf (multiSurface p n a) :=
  familyLine p (fun j =>
    pullbackInvertibleSheaf (towerProjection p n a i) (towerExceptionalLine p (a i) j))

/-- The product of those same original pulled exceptional inclusions. -/
def clusterIdealInclusion (p n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterIdealLine p n a i).obj ⟶
      _root_.SheafOfModules.unit (multiSurface p n a).ringCatSheaf :=
  familyInclusion p _ (multiTotalExceptionalInclusion p n a i)

/-- The ordered tensor over every original cluster and every original total exceptional line. -/
def multiIdealLine (p n : ℕ) (a : Fin n → k) : InvertibleSheaf (multiSurface p n a) :=
  familyLine n (clusterIdealLine p n a)

/-- Its original product map to the actual structure module. -/
def multiIdealInclusion (p n : ℕ) (a : Fin n → k) :
    (multiIdealLine p n a).obj ⟶
      _root_.SheafOfModules.unit (multiSurface p n a).ringCatSheaf :=
  familyInclusion n (clusterIdealLine p n a) (clusterIdealInclusion p n a)

/-- Every foreign cluster product has invertible original inclusion on the selected cluster open. -/
theorem clusterIdealInclusion_cluster_isIso (q n : ℕ) (a : Fin n → k)
    {i i' : Fin n} (hii' : i' ≠ i) :
    IsIso ((schemeModulePullback (isoPreimage q n a i).ι).map
      (clusterIdealInclusion (q + 1) n a i') ≫
      (schemeModulePullbackUnitIso (isoPreimage q n a i).ι).hom) :=
  pulledFamilyInclusion_isIso (isoPreimage q n a i).ι (q + 1) _
    (multiTotalExceptionalInclusion (q + 1) n a i')
    (fun j => multiTotalExceptionalInclusion_cluster_isIso q n a hii' j)

/-- Every cluster product has invertible original inclusion on the unchanged open. -/
theorem clusterIdealInclusion_complement_isIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    IsIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (clusterIdealInclusion (q + 1) n a i) ≫
      (schemeModulePullbackUnitIso (blowdownIsoOpen q n a).ι).hom) :=
  pulledFamilyInclusion_isIso (blowdownIsoOpen q n a).ι (q + 1) _
    (multiTotalExceptionalInclusion (q + 1) n a i)
    (fun j => multiTotalExceptionalInclusion_complement_isIso q n a i j)

/-- The whole exceptional tensor restricts to precisely its own cluster factor. -/
def clusterIdealSelectionIso (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (schemeModulePullback (isoPreimage q n a i).ι).obj (multiIdealLine (q + 1) n a).obj ≅
      (schemeModulePullback (isoPreimage q n a i).ι).obj
        (clusterIdealLine (q + 1) n a i).obj :=
  pulledFamilySelectIso (isoPreimage q n a i).ι n
    (clusterIdealLine (q + 1) n a) (clusterIdealInclusion (q + 1) n a) i
    (fun _ h => clusterIdealInclusion_cluster_isIso q n a h)

/-- Selection retains the original entire double product inclusion. -/
theorem clusterIdealSelectionIso_inclusion (q n : ℕ) (a : Fin n → k) (i : Fin n) :
    (clusterIdealSelectionIso q n a i).hom ≫
        (schemeModulePullback (isoPreimage q n a i).ι).map
          (clusterIdealInclusion (q + 1) n a i) ≫
        (schemeModulePullbackUnitIso (isoPreimage q n a i).ι).hom =
      (schemeModulePullback (isoPreimage q n a i).ι).map
          (multiIdealInclusion (q + 1) n a) ≫
        (schemeModulePullbackUnitIso (isoPreimage q n a i).ι).hom :=
  pulledFamilySelectIso_inclusion (isoPreimage q n a i).ι n
    (clusterIdealLine (q + 1) n a) (clusterIdealInclusion (q + 1) n a) i
    (fun _ h => clusterIdealInclusion_cluster_isIso q n a h)

/-- The original entire double product inclusion is invertible on the unchanged open. -/
theorem multiIdealInclusion_complement_isIso (q n : ℕ) (a : Fin n → k) :
    IsIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (multiIdealInclusion (q + 1) n a) ≫
      (schemeModulePullbackUnitIso (blowdownIsoOpen q n a).ι).hom) :=
  pulledFamilyInclusion_isIso (blowdownIsoOpen q n a).ι n
    (clusterIdealLine (q + 1) n a) (clusterIdealInclusion (q + 1) n a)
    (clusterIdealInclusion_complement_isIso q n a)

/-- On the unchanged open the original inclusion itself gives the unit comparison. -/
def complementIdealIso (q n : ℕ) (a : Fin n → k) :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj (multiIdealLine (q + 1) n a).obj ≅
      _root_.SheafOfModules.unit (blowdownIsoOpen q n a).toScheme.ringCatSheaf := by
  letI := multiIdealInclusion_complement_isIso q n a
  exact asIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
    (multiIdealInclusion (q + 1) n a) ≫
    (schemeModulePullbackUnitIso (blowdownIsoOpen q n a).ι).hom)

@[simp] theorem complementIdealIso_hom (q n : ℕ) (a : Fin n → k) :
    (complementIdealIso q n a).hom =
      (schemeModulePullback (blowdownIsoOpen q n a).ι).map
        (multiIdealInclusion (q + 1) n a) ≫
      (schemeModulePullbackUnitIso (blowdownIsoOpen q n a).ι).hom := rfl

end KltDP.Examples.FrobeniusMultiCentreCanonicalIdealFamily
