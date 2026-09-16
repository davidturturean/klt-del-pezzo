import KltDP.Geometry.GluedConormalBasicOpenEvaluation
import KltDP.Geometry.SchemeDualComparisonEvaluation

/-!
# The original tilde-dual comparison on actual basic-open quotient charts

The proved original evaluation on the actual basic-open chart fixes the
normal comparison uniquely. Thus restricting the original normal module
and then taking its original tilde-dual comparison is the same as pulling
back the original comparison and using the actual sheaf-dual pullback.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.GluedConormalBasicOpenDual

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem evaluation_cancel {D : Type*} [Category D] [MonoidalCategory D]
    {P C N N' E O : D} (c : P ≅ C) (n : N ≅ N') (p : N ≅ E)
    (evalC : C ⊗ E ⟶ O) (T : C ⊗ N' ⟶ O)
    (h : (c.hom ⊗ p.hom) ≫ evalC = (tensorIso c n).hom ≫ T) :
    (C ◁ (n.inv ≫ p.hom)) ≫ evalC = T := by
  apply (cancel_epi (tensorIso c n).hom).mp
  rw [← id_tensorHom]
  simp only [tensorIso_hom, ← tensor_comp_assoc, Category.comp_id, Iso.hom_inv_id_assoc]
  exact h

private theorem iso_eq_of_inv_comp {C : Type*} [Category C]
    {N N' D : C} (n : N ≅ N') (e : N' ≅ D) (p : N ≅ D)
    (h : n.inv ≫ p.hom = e.hom) : n ≪≫ e = p := by
  apply Iso.ext
  exact (congrArg (fun a => n.hom ≫ a) h).symm.trans (by
    change n.hom ≫ n.inv ≫ p.hom = p.hom
    rw [Iso.hom_inv_id_assoc])

set_option maxHeartbeats 800000 in
/-- The source-chart evaluation is normalized before any basic-open map is inserted. -/
private theorem chart_comparison_evaluation {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (d : Γ(X, U.1))
    (hI : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1))
    (f : Y ⟶ I.glueDataObj U) {C : Y.Modules}
    (c : (schemeModulePullback f).obj
      (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde ≅ C) :
    (c.hom ⊗ ((schemeModulePullback f).mapIso
        (PrincipalConormalTildeDual.iso (I.ideal U)
          (gluedAffineIdealEquation I U d hI) hI.symm hd) ≪≫
      schemeModulePullbackDualIso f
        (PrincipalConormalTildeDual.conormalLine (I.ideal U)
          (gluedAffineIdealEquation I U d hI) hI.symm hd) ≪≫
      (sectionDualIso Y c).symm).hom) ≫
        KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond C =
      (schemeModulePullbackTensorIso f
        (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde).inv ≫
      (schemeModulePullback f).map
        (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal U)
          (gluedAffineIdealEquation I U d hI) hI.symm hd).hom ≫
      (schemeModulePullbackUnitIso f).hom := by
  have h := schemeModulePullbackDualComparison_evaluation f
    (PrincipalConormalTildeDual.conormalLine (I.ideal U)
      (gluedAffineIdealEquation I U d hI) hI.symm hd)
    (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde
    (PrincipalConormalTildeDual.iso (I.ideal U)
      (gluedAffineIdealEquation I U d hI) hI.symm hd) c
  have he := congrArg
    (fun a : (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde ⊗
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde ⟶
        _root_.SheafOfModules.unit (I.glueDataObj U).ringCatSheaf =>
      (schemeModulePullbackTensorIso f
        (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde).inv ≫
      (schemeModulePullback f).map a ≫ (schemeModulePullbackUnitIso f).hom)
    (PrincipalConormalTildeDual.iso_evaluation (I.ideal U)
      (gluedAffineIdealEquation I U d hI) hI.symm hd)
  exact h.trans he

set_option maxHeartbeats 800000 in
/-- Evaluation uniqueness on one original chart, independently of the refinement map. -/
private theorem chart_comparison_unique {X : Scheme.{u}}
    (I : X.IdealSheafData) (V : X.affineOpens) (d : Γ(X, V.1))
    (hI : I.ideal V = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, V.1))
    (P N : (I.glueDataObj V).Modules)
    (c : P ≅ (PrincipalConormalTildeDual.conormalModule (I.ideal V)).tilde)
    (n : N ≅ (PrincipalConormalTildeDual.normalModule (I.ideal V)).tilde)
    (p : N ≅ KltDP.SheafOfModules.dual (I.glueDataObj V).ringCatSheaf
      (PrincipalConormalTildeDual.conormalModule (I.ideal V)).tilde)
    (hp : (c.hom ⊗ p.hom) ≫ KltDP.SheafOfModules.evaluation
      (I.glueDataObj V).sheaf.val (I.glueDataObj V).ringCatSheaf.cond
      (PrincipalConormalTildeDual.conormalModule (I.ideal V)).tilde =
      (tensorIso c n).hom ≫
        (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal V)
          (gluedAffineIdealEquation I V d hI) hI.symm hd).hom) :
    n ≪≫ PrincipalConormalTildeDual.iso (I.ideal V)
      (gluedAffineIdealEquation I V d hI) hI.symm hd = p := by
  exact iso_eq_of_inv_comp n
    (PrincipalConormalTildeDual.iso (I.ideal V)
      (gluedAffineIdealEquation I V d hI) hI.symm hd) p
    (PrincipalConormalTildeDual.iso_unique (I.ideal V)
      (gluedAffineIdealEquation I V d hI) hI.symm hd (n.inv ≫ p.hom)
      (evaluation_cancel c n p
        (KltDP.SheafOfModules.evaluation (I.glueDataObj V).sheaf.val
          (I.glueDataObj V).ringCatSheaf.cond
          (PrincipalConormalTildeDual.conormalModule (I.ideal V)).tilde)
        (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal V)
          (gluedAffineIdealEquation I V d hI) hI.symm hd).hom hp))

open GluedConormalBasicOpenLocalization GluedConormalBasicOpenNormal

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- Restrict the actual normal tilde, then use the smaller original tilde-dual map. -/
def restrictedComparisonIso :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde ≅
      KltDP.SheafOfModules.dual (I.glueDataObj (X.affineBasicOpen r)).ringCatSheaf
        (PrincipalConormalTildeDual.conormalModule (I.ideal (X.affineBasicOpen r))).tilde :=
  normalTildeRefinementIso I U r d hI hd ≪≫
    PrincipalConormalTildeDual.iso (I.ideal (X.affineBasicOpen r))
      (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI))
      (equation_span I U r d hI).symm (equation_regular U r d hd)

/-- Pull back the original tilde-dual map and transport through the actual conormal refinement. -/
def pulledComparisonIso :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
        (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde ≅
      KltDP.SheafOfModules.dual (I.glueDataObj (X.affineBasicOpen r)).ringCatSheaf
        (PrincipalConormalTildeDual.conormalModule (I.ideal (X.affineBasicOpen r))).tilde :=
  (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).mapIso
      (PrincipalConormalTildeDual.iso (I.ideal U)
        (gluedAffineIdealEquation I U d hI) hI.symm hd) ≪≫
    schemeModulePullbackDualIso (I.glueDataObjMap (X.affineBasicOpen_le r))
      (PrincipalConormalTildeDual.conormalLine (I.ideal U)
        (gluedAffineIdealEquation I U d hI) hI.symm hd) ≪≫
    (sectionDualIso (I.glueDataObj (X.affineBasicOpen r))
      (tildeRefinementIso I U r d hI hd)).symm

private theorem comparison_evaluation :
    ((tildeRefinementIso I U r d hI hd).hom ⊗
      (pulledComparisonIso I U r d hI hd).hom) ≫
      KltDP.SheafOfModules.evaluation
        (I.glueDataObj (X.affineBasicOpen r)).sheaf.val
        (I.glueDataObj (X.affineBasicOpen r)).ringCatSheaf.cond
        (PrincipalConormalTildeDual.conormalModule (I.ideal (X.affineBasicOpen r))).tilde =
    (tensorIso (tildeRefinementIso I U r d hI hd)
      (normalTildeRefinementIso I U r d hI hd)).hom ≫
      (PrincipalConormalTildeDual.transportedEvaluationIso (I.ideal (X.affineBasicOpen r))
        (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
          (equation_span I U r d hI))
        (equation_span I U r d hI).symm (equation_regular U r d hd)).hom := by
  exact (chart_comparison_evaluation I U d hI hd
    (I.glueDataObjMap (X.affineBasicOpen_le r))
    (tildeRefinementIso I U r d hI hd)).trans
    (GluedConormalBasicOpenEvaluation.tensor_evaluation I U r d hI hd).symm

private def comparisonIso_eq_proof {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hI : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  chart_comparison_unique I (X.affineBasicOpen r) (sectionMap U r d)
    (equation_span I U r d hI) (equation_regular U r d hd)
    ((schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
      (PrincipalConormalTildeDual.conormalModule (I.ideal U)).tilde)
    ((schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
      (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde)
    (tildeRefinementIso I U r d hI hd) (normalTildeRefinementIso I U r d hI hd)
    (pulledComparisonIso I U r d hI hd) (comparison_evaluation I U r d hI hd)

/-- The two original sheaf-dual routes agree on the actual basic-open quotient chart. -/
theorem comparisonIso_eq :
    restrictedComparisonIso I U r d hI hd = pulledComparisonIso I U r d hI hd :=
  comparisonIso_eq_proof I U r d hI hd

end KltDP.Geometry.GluedConormalBasicOpenDual
