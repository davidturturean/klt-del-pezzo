import KltDP.Geometry.GluedConormalPullbackFrame
import KltDP.Geometry.GluedIdealInvertible
import KltDP.Geometry.PrincipalConormalTildeDual
import KltDP.Geometry.SchemeDualTensorNaturality
import KltDP.Geometry.SchemeModuleSheafificationInstances

/-!
# Original normal tilde on the actual global conormal charts

For an actual locally regular principal ideal sheaf, the original normal
module tilde on an original quotient chart is the chart pullback of the
actual dual of the global conormal sheaf. The existing global conormal
comparison and its proved invertibility supply the objects and maps.
The original evaluation is preserved through the actual pullback tensor
and unit comparisons.

Compatibility of these global chart comparisons on refinements and
gluing the Kähler/determinant adjunction remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.GluedConormalTildeDualChart

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem evaluationTransport {Dcat : Type*} [Category Dcat] [MonoidalCategory Dcat]
    {C P N DC DP B O : Dcat} (c : C ≅ P) (e : N ≅ DC) (s : DP ≅ DC) (b : B ≅ DP)
    (evalP : P ⊗ DP ⟶ O) (evalC : C ⊗ DC ⟶ O)
    (EB : P ⊗ B ⟶ O) (EC : C ⊗ N ⟶ O)
    (hc : (c.hom ⊗ s.inv) ≫ evalP = evalC)
    (hb : (P ◁ b.hom) ≫ evalP = EB)
    (he : (C ◁ e.hom) ≫ evalC = EC) :
    (tensorIso c (e ≪≫ s.symm ≪≫ b.symm)).hom ≫ EB = EC := by
  simp only [tensorIso_hom, Iso.trans_hom, Iso.symm_hom]
  calc
    _ = (c.hom ⊗ (e.hom ≫ s.inv)) ≫ evalP := by
      rw [← hb, ← id_tensorHom]
      simp only [← tensor_comp_assoc, Category.comp_id, Category.assoc, Iso.inv_hom_id]
    _ = (𝟙 C ⊗ e.hom) ≫ (c.hom ⊗ s.inv) ≫ evalP := by
      simp only [← tensor_comp_assoc, Category.id_comp, Category.assoc]
    _ = (C ◁ e.hom) ≫ evalC := by
      rw [hc]
      simp only [id_tensorHom]
    _ = EC := he

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual dual of the original global kernel conormal. -/
def globalNormalSheaf : I.glueData.glued.Modules :=
  KltDP.SheafOfModules.dual I.glueData.glued.ringCatSheaf (schemeConormalSheaf I.gluedTo)

variable (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
  (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original normal module tilde is the actual chart pullback of
the dual of the actual global conormal sheaf. -/
def chartIso : (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde ≅
    (schemeModulePullback (I.glueData.ι U)).obj (globalNormalSheaf I) :=
  PrincipalConormalTildeDual.iso (I.ideal U) (gluedAffineIdealEquation I U d hU) hU.symm hd ≪≫
    (sectionDualIso (I.glueDataObj U)
      (gluedAffineConormalTildePullbackIso I U d hU hd)).symm ≪≫
    (schemeModulePullbackDualIso (I.glueData.ι U) (gluedConormalLine I hI)).symm

set_option maxHeartbeats 800000 in
/-- This actual global-chart comparison preserves the original evaluation,
including the original pullback tensor and unit normalization. -/
theorem chartIso_evaluation :
    (tensorIso (gluedAffineConormalTildePullbackIso I U d hU hd)
      (chartIso I hI U d hU hd)).hom ≫
        (schemeModulePullbackDualEvaluationIso
          (I.glueData.ι U) (gluedConormalLine I hI)).hom =
      (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal U)
        (gluedAffineIdealEquation I U d hU) hU.symm hd).hom := by
  let Y : Scheme.{u} := I.glueDataObj U
  letI : HasWeakSheafify (_root_.Opens.grothendieckTopology Y) AddCommGrp.{u} :=
    SchemeModuleSheafificationInstances.hasWeakSheafify Y
  letI : (_root_.Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrp.{u} :=
    SchemeModuleSheafificationInstances.wEqualsLocallyBijective Y
  let C : Y.Modules := (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde
  let P : Y.Modules :=
    (schemeModulePullback (I.glueData.ι U)).obj (schemeConormalSheaf I.gluedTo)
  let c := gluedAffineConormalTildePullbackIso I U d hU hd
  let e := PrincipalConormalTildeDual.iso (I.ideal U)
    (gluedAffineIdealEquation I U d hU) hU.symm hd
  let b := schemeModulePullbackDualIso (I.glueData.ι U) (gluedConormalLine I hI)
  let s := sectionDualIso Y c
  exact evaluationTransport c e s b
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond P)
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond C)
    (schemeModulePullbackDualEvaluationIso (I.glueData.ι U) (gluedConormalLine I hI)).hom
    (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal U)
      (gluedAffineIdealEquation I U d hU) hU.symm hd).hom
    (SchemeDualTensorNaturality.sectionDualIso_evaluation Y c)
    (schemeModulePullbackDualIso_evaluation (I.glueData.ι U) (gluedConormalLine I hI))
    (PrincipalConormalTildeDual.iso_evaluation (I.ideal U)
      (gluedAffineIdealEquation I U d hU) hU.symm hd)

end KltDP.Geometry.GluedConormalTildeDualChart
