import KltDP.Examples.FrobeniusGlobalBlowupCanonicalTarget
import KltDP.Examples.FrobeniusGlobalBlowupDifferentialComplement

/-!
# The original canonical factor on the unchanged complement

The original entire center-fiber kernel is framed by the actual equation one
on the original complement. Hence its actual tensor inclusion is invertible
there. The original projection differential is already invertible on the same
open. Their actual composite constructs the normalized complementary factor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Examples.FrobeniusGlobalBlowupCanonicalComplementFactor

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupDifferentialAffine
open FrobeniusGlobalBlowupDifferentialComplement FrobeniusGlobalBlowupCanonicalTarget

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance wholeComplementFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem scalarEnd_one (X : Scheme.{u}) :
    schemeScalarEnd (Y := X) 1 = 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply (_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop (_root_.SheafOfModules.unit X.ringCatSheaf)).injective
  change (schemeScalarEnd (Y := X) 1).val.app (op ⊤) (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤))
  rw [schemeScalarEnd_appTop, one_mul]

private theorem pulledTensorInclusion_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)]
    (M : X.Modules) : IsIso ((schemeModulePullback f).map (schemeStructureTensorInclusion i M)) := by
  rw [← schemeModulePullbackTensorIso_inclusion f i M]
  unfold schemeStructureTensorInclusion
  infer_instance

variable {k : Type u} [Field k]

local instance wholeComplementFactorOriginMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

variable (A : PlaneChartedScheme k)

/-- The actual pulled exceptional inclusion is invertible, by its original frame with equation one. -/
theorem complementIdealInclusion_isIso :
    IsIso ((schemeModulePullback (complementOpen A).ι).map (wholeExceptionalInclusion A) ≫
      (schemeModulePullbackUnitIso (complementOpen A).ι).hom) := by
  have h := PointBlowupGluing.globalCenterFiberComplementFrame_inclusion
    A.chart (originPoint (k := k)) A.center_closed
  rw [scalarEnd_one] at h
  exact IsIso.of_isIso_fac_left h

/-- The original whole ideal/top inclusion is invertible on this same actual open. -/
theorem complementCanonicalInclusion_isIso :
    IsIso ((schemeModulePullback (complementOpen A).ι).map (wholeCanonicalInclusion A)) := by
  letI := complementIdealInclusion_isIso A
  exact pulledTensorInclusion_isIso (complementOpen A).ι
    (wholeExceptionalInclusion A) (nextTop A)

/-- The original complementary factor uses precisely the inverses just proved for the actual maps. -/
def complementCanonicalFactorIso :
    (schemeModulePullback (complementOpen A).ι).obj
        ((schemeModulePullback A.nextProjection).obj (oldTop A)) ≅
      (schemeModulePullback (complementOpen A).ι).obj (wholeCanonicalTarget A) := by
  letI := complementDifferential_isIso A
  letI := complementCanonicalInclusion_isIso A
  exact asIso ((schemeModulePullback (complementOpen A).ι).map (nextDifferentialMap A)) ≪≫
    (asIso ((schemeModulePullback (complementOpen A).ι).map (wholeCanonicalInclusion A))).symm

/-- The constructed complement factor retains the original whole-stage differential. -/
theorem complementCanonicalFactorIso_comp :
    (complementCanonicalFactorIso A).hom ≫
        (schemeModulePullback (complementOpen A).ι).map (wholeCanonicalInclusion A) =
      (schemeModulePullback (complementOpen A).ι).map (nextDifferentialMap A) := by
  letI := complementDifferential_isIso A
  letI := complementCanonicalInclusion_isIso A
  change ((schemeModulePullback (complementOpen A).ι).map (nextDifferentialMap A) ≫
      inv ((schemeModulePullback (complementOpen A).ι).map (wholeCanonicalInclusion A))) ≫
    (schemeModulePullback (complementOpen A).ι).map (wholeCanonicalInclusion A) = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end KltDP.Examples.FrobeniusGlobalBlowupCanonicalComplementFactor
