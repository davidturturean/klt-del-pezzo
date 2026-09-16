import KltDP.Geometry.SchemeInvertibleSheafPullback
import Mathlib.CategoryTheory.Equivalence

/-!
# Pullback of the actual dual of an invertible sheaf

The original tensor and unit pullback comparisons transport the original
evaluation. Tensoring with the actual pulled-back line is fully faithful,
so this evaluation determines a unique comparison with its actual sheaf dual.
The comparison preserves evaluation, including its unit normalization.

No isomorphism of Picard classes is chosen. No global monoidal structure on
the pullback functor, naturality in the scheme morphism, or intersection
interpretation is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u v w

namespace KltDP.Geometry

section TensorCancellation

variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The two tensor inverses give an equivalence with the original
left-tensor functor. The pinned constructor supplies its triangle identity. -/
private def tensorLeftEquivalenceOfInverse {A D : C} (d : A ⊗ D ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft A) (tensorLeft D)
    ((tensorLeftTensor D A).symm ≪≫
      (tensoringLeft C).mapIso ((β_ D A) ≪≫ d) ≪≫ leftUnitorNatIso C).symm
    ((tensorLeftTensor A D).symm ≪≫
      (tensoringLeft C).mapIso d ≪≫ leftUnitorNatIso C)

private def tensorLeftFullyFaithfulOfInverse {A D : C} (d : A ⊗ D ≅ 𝟙_ C) :
    (tensorLeft A).FullyFaithful :=
  (tensorLeftEquivalenceOfInverse d).fullyFaithfulFunctor

private def comparisonOfEvaluations {A B D U : C}
    (hA : (tensorLeft A).FullyFaithful) (e : A ⊗ B ≅ U) (d : A ⊗ D ≅ U) :
    B ≅ D :=
  hA.preimageIso (e ≪≫ d.symm)

private theorem comparisonOfEvaluations_comp {A B D U : C}
    (hA : (tensorLeft A).FullyFaithful) (e : A ⊗ B ≅ U) (d : A ⊗ D ≅ U) :
    A ◁ (comparisonOfEvaluations hA e d).hom ≫ d.hom = e.hom := by
  change (tensorLeft A).map (hA.preimage (e ≪≫ d.symm).hom) ≫ d.hom = e.hom
  rw [hA.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem comparisonOfEvaluations_unique {A B D U : C}
    (hA : (tensorLeft A).FullyFaithful) (e : A ⊗ B ≅ U) (d : A ⊗ D ≅ U)
    (m : B ⟶ D) (hm : A ◁ m ≫ d.hom = e.hom) :
    m = (comparisonOfEvaluations hA e d).hom := by
  apply hA.map_injective
  apply (cancel_mono d.hom).1
  exact hm.trans (comparisonOfEvaluations_comp hA e d).symm

end TensorCancellation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Scheme

local instance dualPullbackStructureSectionsComm (S : Scheme.{u}) :
    ∀ U, IsMulCommutative (S.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (S.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance dualPullbackModulesMonoidal (S : Scheme.{u}) : MonoidalCategory S.Modules :=
  Scheme.Modules.monoidalCategory S

local instance dualPullbackModulesSymmetric (S : Scheme.{u}) : SymmetricCategory S.Modules :=
  Scheme.Modules.symmetricCategory S

private def lineEvaluationIso {S : Scheme.{u}} (L : InvertibleSheaf S) :
    L.obj ⊗ KltDP.SheafOfModules.dual S.ringCatSheaf L.obj ≅
      _root_.SheafOfModules.unit S.ringCatSheaf :=
  KltDP.SheafOfModules.evaluationIso S.sheaf.val S.ringCatSheaf.cond L.obj

private def lineTensorFullyFaithful {S : Scheme.{u}} (L : InvertibleSheaf S) :
    (tensorLeft L.obj).FullyFaithful :=
  tensorLeftFullyFaithfulOfInverse
    (lineEvaluationIso L ≪≫
      (PresheafOfModules.sheafTensorUnitIso S.sheaf.val S.ringCatSheaf.cond).symm)

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L : InvertibleSheaf X)

/-- The original evaluation transported through the original tensor and
unit comparisons of the actual scheme-module pullback. -/
def schemeModulePullbackDualEvaluationIso :
    (schemeModulePullback f).obj L.obj ⊗
      (schemeModulePullback f).obj (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) ≅
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (schemeModulePullbackTensorIso f L.obj
    (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj)).symm ≪≫
  (schemeModulePullback f).mapIso (lineEvaluationIso L) ≪≫
  schemeModulePullbackUnitIso f

/-- This transported evaluation retains its original map and unit scalar. -/
theorem schemeModulePullbackDualEvaluationIso_hom :
    (schemeModulePullbackDualEvaluationIso f L).hom =
      (schemeModulePullbackTensorIso f L.obj
        (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj)).inv ≫
      (schemeModulePullback f).map
        (KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond L.obj) ≫
      (schemeModulePullbackUnitIso f).hom := rfl

/-- Pullback commutes with the actual sheaf dual for an actual invertible
sheaf. Its forward map is characterized by the original evaluation below. -/
def schemeModulePullbackDualIso :
    (schemeModulePullback f).obj (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) ≅
      KltDP.SheafOfModules.dual Y.ringCatSheaf ((schemeModulePullback f).obj L.obj) :=
  comparisonOfEvaluations (lineTensorFullyFaithful (pullbackInvertibleSheaf f L))
    (schemeModulePullbackDualEvaluationIso f L)
    (lineEvaluationIso (pullbackInvertibleSheaf f L))

/-- The comparison identifies the pulled evaluation with the actual
evaluation on the pulled-back line, without a scalar ambiguity. -/
theorem schemeModulePullbackDualIso_evaluation :
    (schemeModulePullback f).obj L.obj ◁ (schemeModulePullbackDualIso f L).hom ≫
      KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond
        ((schemeModulePullback f).obj L.obj) =
      (schemeModulePullbackDualEvaluationIso f L).hom :=
  comparisonOfEvaluations_comp (lineTensorFullyFaithful (pullbackInvertibleSheaf f L))
    (schemeModulePullbackDualEvaluationIso f L)
    (lineEvaluationIso (pullbackInvertibleSheaf f L))

/-- Evaluation characterizes the forward comparison among all actual
module-sheaf morphisms with these source and target objects. -/
theorem schemeModulePullbackDualIso_unique
    (m : (schemeModulePullback f).obj (KltDP.SheafOfModules.dual X.ringCatSheaf L.obj) ⟶
      KltDP.SheafOfModules.dual Y.ringCatSheaf ((schemeModulePullback f).obj L.obj))
    (hm : (schemeModulePullback f).obj L.obj ◁ m ≫
      KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond
        ((schemeModulePullback f).obj L.obj) =
      (schemeModulePullbackDualEvaluationIso f L).hom) :
    m = (schemeModulePullbackDualIso f L).hom :=
  comparisonOfEvaluations_unique (lineTensorFullyFaithful (pullbackInvertibleSheaf f L))
    (schemeModulePullbackDualEvaluationIso f L)
    (lineEvaluationIso (pullbackInvertibleSheaf f L)) m hm

end Scheme

end KltDP.Geometry
