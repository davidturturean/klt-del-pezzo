import KltDP.Examples.FrobeniusMultiCentreCanonicalTarget

/-!
# The original canonical factor on the unchanged finite-centre open

On the complement the original exceptional product inclusion and the original
whole differential are both invertible. Their original maps therefore define
the normalized factor directly. No canonical relation is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalComplementFactor

open KltDP.Geometry FrobeniusMultiCentreSurface FrobeniusMultiCentreCurveKernels
open FrobeniusMultiCentreCanonicalIdealFamily FrobeniusMultiCentreCanonicalDifferentialCharts
open FrobeniusMultiCentreCanonicalTarget

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance multiComplementFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem pulledTensorInclusion_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    [IsIso ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)] :
    IsIso ((schemeModulePullback f).map (schemeStructureTensorInclusion i M)) := by
  haveI : IsIso (schemeStructureTensorInclusion
      ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)
      ((schemeModulePullback f).obj M)) := by
    unfold schemeStructureTensorInclusion
    infer_instance
  rw [← schemeModulePullbackTensorIso_inclusion f i M]
  infer_instance

variable {k : Type u} [Field k]

/-- The actual target inclusion is invertible on the unchanged open. -/
theorem multiCanonicalInclusion_complement_isIso (q n : ℕ) (a : Fin n → k) :
    IsIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (multiCanonicalInclusion (q + 1) n a)) := by
  letI := multiIdealInclusion_complement_isIso q n a
  exact pulledTensorInclusion_isIso (blowdownIsoOpen q n a).ι
    (multiIdealInclusion (q + 1) n a) (multiTop (q + 1) n a)

/-- Use the two original invertible maps on the original complement. -/
def complementCanonicalFactorIso (q n : ℕ) (a : Fin n → k) :
    (schemeModulePullback (blowdownIsoOpen q n a).ι).obj
        ((schemeModulePullback (multiProjection (q + 1) n a)).obj (baseTop (k := k))) ≅
      (schemeModulePullback (blowdownIsoOpen q n a).ι).obj (multiCanonicalTarget (q + 1) n a) := by
  letI := multiDifferentialMap_complement_isIso q n a
  letI := multiCanonicalInclusion_complement_isIso q n a
  exact asIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (multiDifferentialMap (q + 1) n a)) ≪≫
    (asIso ((schemeModulePullback (blowdownIsoOpen q n a).ι).map
      (multiCanonicalInclusion (q + 1) n a))).symm

/-- The complement factor retains the same original restricted differential. -/
theorem complementCanonicalFactorIso_comp (q n : ℕ) (a : Fin n → k) :
    (complementCanonicalFactorIso q n a).hom ≫
        (schemeModulePullback (blowdownIsoOpen q n a).ι).map (multiCanonicalInclusion (q + 1) n a) =
      (schemeModulePullback (blowdownIsoOpen q n a).ι).map (multiDifferentialMap (q + 1) n a) := by
  letI := multiDifferentialMap_complement_isIso q n a
  letI := multiCanonicalInclusion_complement_isIso q n a
  simp only [complementCanonicalFactorIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end KltDP.Examples.FrobeniusMultiCentreCanonicalComplementFactor
