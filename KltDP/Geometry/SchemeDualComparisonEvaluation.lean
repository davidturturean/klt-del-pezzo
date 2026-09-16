import KltDP.Geometry.SchemeInvertibleDualPullback
import KltDP.Geometry.SchemeDualTensorNaturality

/-!
# Evaluation of the actual pulled dual comparison

Pull back an original comparison with a line's sheaf dual, then transport
along an actual isomorphism of the pulled line. Its evaluation is precisely
the pullback of the original evaluation, through the existing tensor and
unit comparisons. This exposes the normalization used by the normal-chart
restriction proof without assuming an evaluation compatibility equation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance comparisonEvaluationSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance comparisonEvaluationTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem comparison_evaluation_word
    {D : Type*} [Category D] [MonoidalCategory D]
    {P C N B DC DP O : D} (c : P ≅ C) (a : N ⟶ B) (b : B ≅ DP) (s : DC ≅ DP)
    (evalC : C ⊗ DC ⟶ O) (evalP : P ⊗ DP ⟶ O) (EB : P ⊗ B ⟶ O)
    (hc : (c.hom ⊗ s.inv) ≫ evalC = evalP)
    (hb : (P ◁ b.hom) ≫ evalP = EB) :
    (c.hom ⊗ (a ≫ b.hom ≫ s.inv)) ≫ evalC = (P ◁ a) ≫ EB := by
  calc
    _ = (𝟙 P ⊗ a) ≫ (𝟙 P ⊗ b.hom) ≫ (c.hom ⊗ s.inv) ≫ evalC := by
      simp only [← tensor_comp_assoc, Category.id_comp, Category.assoc]
    _ = (P ◁ a) ≫ (P ◁ b.hom) ≫ evalP := by
      rw [hc]
      simp only [id_tensorHom]
    _ = (P ◁ a) ≫ EB := by rw [hb]

private theorem pullbackTensor_inv_natural_right {X Y : Scheme.{u}}
    (f : Y ⟶ X) (P : X.Modules) {N D : X.Modules} (a : N ⟶ D) :
    ((schemeModulePullback f).obj P ◁ (schemeModulePullback f).map a) ≫
        (schemeModulePullbackTensorIso f P D).inv =
      (schemeModulePullbackTensorIso f P N).inv ≫
        (schemeModulePullback f).map (P ◁ a) := by
  have h : (schemeModulePullback f).map (P ◁ a) ≫
      (schemeModulePullbackTensorIso f P D).hom =
    (schemeModulePullbackTensorIso f P N).hom ≫
      ((schemeModulePullback f).obj P ◁ (schemeModulePullback f).map a) := by
    have hn := schemeModulePullbackTensorIso_natural f (𝟙 P) a
    rw [(schemeModulePullback f).map_id P] at hn
    simpa only [id_tensorHom] using hn
  apply (cancel_epi (schemeModulePullbackTensorIso f P N).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The exact evaluation of the original pulled dual comparison. -/
theorem schemeModulePullbackDualComparison_evaluation {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) (N : X.Modules)
    (e : N ≅ KltDP.SheafOfModules.dual X.ringCatSheaf L.obj)
    {C : Y.Modules} (c : (schemeModulePullback f).obj L.obj ≅ C) :
    (c.hom ⊗ (((schemeModulePullback f).mapIso e) ≪≫
      schemeModulePullbackDualIso f L ≪≫ (sectionDualIso Y c).symm).hom) ≫
        KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond C =
      (schemeModulePullbackTensorIso f L.obj N).inv ≫
        (schemeModulePullback f).map
          ((L.obj ◁ e.hom) ≫
            KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond L.obj) ≫
        (schemeModulePullbackUnitIso f).hom := by
  refine (comparison_evaluation_word c ((schemeModulePullback f).map e.hom)
    (schemeModulePullbackDualIso f L) (sectionDualIso Y c)
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond C)
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond
      ((schemeModulePullback f).obj L.obj))
    (schemeModulePullbackDualEvaluationIso f L).hom
    (SchemeDualTensorNaturality.sectionDualIso_evaluation Y c)
    (schemeModulePullbackDualIso_evaluation f L)).trans ?_
  rw [schemeModulePullbackDualEvaluationIso_hom, ← Category.assoc]
  erw [pullbackTensor_inv_natural_right f L.obj e.hom]
  simp only [Functor.map_comp, Category.assoc]

end KltDP.Geometry
