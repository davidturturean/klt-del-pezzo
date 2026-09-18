import KltDP.Examples.FrobeniusContactTowerCanonicalFactorIdeals
import KltDP.Examples.FrobeniusGlobalBlowupCanonicalGlobalFactor
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso

/-!
# The normalized canonical factor on the entire original contact tower

Iterate the proved whole-stage canonical factor. At each step the original
pullback tensor comparison and associator combine the actual exceptional
ideal lines. The resulting isomorphism retains the original exterior
differential of the actual composite tower projection. No formula or
compatibility of that map is supplied as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactor

open KltDP.Geometry FrobeniusGlobalBlowupStages
open FrobeniusGlobalBlowupDifferentialAffine FrobeniusGlobalBlowupCanonicalTarget
open FrobeniusGlobalBlowupCanonicalGlobalFactor
open FrobeniusContactTowerCanonicalFactorTensor FrobeniusContactTowerCanonicalFactorIdeals

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance towerFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private def stepFactorIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P I M : X.Modules} {J N : Y.Modules}
    (e : P ≅ I ⊗ M) (s : (schemeModulePullback f).obj M ≅ J ⊗ N) :
    (schemeModulePullback f).obj P ≅ ((schemeModulePullback f).obj I ⊗ J) ⊗ N :=
  composeFactorIso
    ((schemeModulePullback f).mapIso e ≪≫ schemeModulePullbackTensorIso f I M) s

private theorem stepFactorIso_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P I M : X.Modules} {J N : Y.Modules}
    (e : P ≅ I ⊗ M) (s : (schemeModulePullback f).obj M ≅ J ⊗ N)
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (stepFactorIso f e s).hom ≫
        schemeStructureTensorInclusion
          (productInclusion
            ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) j) N =
      (schemeModulePullback f).map (e.hom ≫ schemeStructureTensorInclusion i M) ≫
        s.hom ≫ schemeStructureTensorInclusion j N := by
  rw [stepFactorIso, composeFactorIso_comp]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [schemeModulePullbackTensorIso_inclusion_assoc, ← Functor.map_comp_assoc]

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

private theorem towerDifferentialMap_zero_isIso : IsIso (towerDifferentialMap A 0) := by
  haveI : IsOpenImmersion (A.toInitial 0) := by
    change IsOpenImmersion (𝟙 A.carrier)
    infer_instance
  exact SchemeKaehlerExteriorPullbackTransport.map_isIso A.structureMap
    (A.toInitial 0) (A.stage 0).structureMap (A.toInitial_structure 0) 2

variable [IsSmoothOfRelativeDimension 2 A.structureMap]

/-- The actual tensor product of all original total exceptional ideals factors the
original differential of the entire tower projection. -/
def towerCanonicalFactorIso : (n : ℕ) →
    (schemeModulePullback (A.toInitial n)).obj (oldTop A) ≅ towerCanonicalTarget A n
  | 0 => by
      letI := towerDifferentialMap_zero_isIso A
      exact asIso (towerDifferentialMap A 0) ≪≫
        (schemeStructureTensorLeftIso (stageTop A 0)).symm
  | n + 1 => (towerSourceIso A n).symm ≪≫
      stepFactorIso (A.stepProjection n) (towerCanonicalFactorIso n)
        (wholeCanonicalBlowupIso (A.stage n))

/-- The constructed isomorphism followed by the original product inclusion is
exactly the original composite-projection exterior differential. -/
theorem towerCanonicalFactorIso_comp (n : ℕ) :
    (towerCanonicalFactorIso A n).hom ≫ towerCanonicalInclusion A n =
      towerDifferentialMap A n := by
  induction n with
  | zero =>
      simp only [towerCanonicalFactorIso, towerCanonicalInclusion,
        totalExceptionalInclusion, schemeStructureTensorInclusion_eq, Iso.trans_hom,
        Iso.symm_hom, asIso_hom, tensor_id, Category.id_comp,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
  | succ n ih =>
      have hprev :
          (towerCanonicalFactorIso A n).hom ≫
              schemeStructureTensorInclusion (totalExceptionalInclusion A n) (stageTop A n) =
            towerDifferentialMap A n := ih
      have hstep :
          (wholeCanonicalBlowupIso (A.stage n)).hom ≫
              schemeStructureTensorInclusion (wholeExceptionalInclusion (A.stage n))
                (stageTop A (n + 1)) =
            nextDifferentialMap (A.stage n) :=
        wholeCanonicalBlowupIso_comp (A.stage n)
      change (towerSourceIso A n).inv ≫
          (stepFactorIso (A.stepProjection n) (towerCanonicalFactorIso A n)
            (wholeCanonicalBlowupIso (A.stage n))).hom ≫
          schemeStructureTensorInclusion
            (productInclusion
              ((schemeModulePullback (A.stepProjection n)).map (totalExceptionalInclusion A n) ≫
                (schemeModulePullbackUnitIso (A.stepProjection n)).hom)
              (wholeExceptionalInclusion (A.stage n))) (stageTop A (n + 1)) =
        towerDifferentialMap A (n + 1)
      rw [stepFactorIso_comp, hprev, hstep, towerDifferentialMap_succ,
        Iso.inv_hom_id_assoc]

end KltDP.Examples.FrobeniusContactTowerCanonicalFactor

