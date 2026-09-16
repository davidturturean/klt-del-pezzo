import KltDP.Geometry.SchemeModulePullbackTensorComp
import KltDP.Geometry.SchemeDualComparisonEvaluation
import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Composition of the original invertible-sheaf dual pullback comparisons

The original tensor composition and unit composition laws transport the
original evaluation through successive pullbacks. Its accepted uniqueness
then identifies the original dual comparison maps, including the actual
contravariant dual of the original pullback composition isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance dualCompSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance dualCompTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

@[reassoc]
private theorem tensor_comp_inv {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    ((schemeModulePullbackCompIso f g).hom.app M ⊗
        (schemeModulePullbackCompIso f g).hom.app N) ≫
      (schemeModulePullbackTensorIso (f ≫ g) M N).inv =
    (schemeModulePullbackTensorIso f
        ((schemeModulePullback g).obj M) ((schemeModulePullback g).obj N)).inv ≫
      (schemeModulePullback f).map (schemeModulePullbackTensorIso g M N).inv ≫
      (schemeModulePullbackCompIso f g).hom.app (M ⊗ N) := by
  apply (cancel_epi (schemeModulePullbackTensorIso f
    ((schemeModulePullback g).obj M) ((schemeModulePullback g).obj N)).hom).mp
  apply (cancel_epi ((schemeModulePullback f).map
    (schemeModulePullbackTensorIso g M N).hom)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun a => a ≫ (schemeModulePullbackTensorIso (f ≫ g) M N).inv)
      (schemeModulePullbackTensorIso_comp_hom f g M N)

/-- The original transported dual evaluation respects the original composition maps. -/
theorem schemeModulePullbackDualEvaluationIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((schemeModulePullbackCompIso f g).hom.app L.obj ⊗
        (schemeModulePullbackCompIso f g).hom.app
          (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj)) ≫
      (schemeModulePullbackDualEvaluationIso (f ≫ g) L).hom =
    (schemeModulePullbackTensorIso f ((schemeModulePullback g).obj L.obj)
      ((schemeModulePullback g).obj (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))).inv ≫
      (schemeModulePullback f).map (schemeModulePullbackDualEvaluationIso g L).hom ≫
      (schemeModulePullbackUnitIso f).hom := by
  rw [schemeModulePullbackDualEvaluationIso_hom, tensor_comp_inv_assoc]
  have h := congrArg (fun a =>
    (schemeModulePullbackTensorIso f ((schemeModulePullback g).obj L.obj)
      ((schemeModulePullback g).obj (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))).inv ≫
      (schemeModulePullback f).map
        (schemeModulePullbackTensorIso g L.obj
          (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj)).inv ≫
      a ≫ (schemeModulePullbackUnitIso (f ≫ g)).hom)
    ((schemeModulePullbackCompIso f g).hom.naturality
      (KltDP.SheafOfModules.evaluation Z.sheaf.val Z.ringCatSheaf.cond L.obj)).symm
  simp only [schemeModulePullbackDualEvaluationIso_hom, Functor.comp_map,
    Functor.map_comp, Category.assoc] at h ⊢
  refine h.trans ?_
  exact congrArg (fun a =>
    (schemeModulePullbackTensorIso f ((schemeModulePullback g).obj L.obj)
      ((schemeModulePullback g).obj (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))).inv ≫
      (schemeModulePullback f).map
        (schemeModulePullbackTensorIso g L.obj
          (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj)).inv ≫
      (schemeModulePullback f).map ((schemeModulePullback g).map
        (KltDP.SheafOfModules.evaluation Z.sheaf.val Z.ringCatSheaf.cond L.obj)) ≫ a)
    (schemeModulePullbackCompIso_unit f g)

private theorem evaluation_cancel {D : Type*} [Category D] [MonoidalCategory D]
    {P C N N' E O : D} (c : P ≅ C) (n : N ≅ N') (p : N ≅ E)
    (evalC : C ⊗ E ⟶ O) (T : C ⊗ N' ⟶ O)
    (h : (c.hom ⊗ p.hom) ≫ evalC = (tensorIso c n).hom ≫ T) :
    (C ◁ (n.inv ≫ p.hom)) ≫ evalC = T := by
  apply (cancel_epi (tensorIso c n).hom).mp
  rw [← id_tensorHom]
  simp only [tensorIso_hom, ← tensor_comp_assoc, Category.comp_id, Iso.hom_inv_id_assoc]
  exact h

private theorem comparison_unique {D : Type*} [Category D] [MonoidalCategory D]
    {P C N N' E O : D} (c : P ≅ C) (n : N ≅ N') (p : N ≅ E) (e : N' ≅ E)
    (evalC : C ⊗ E ⟶ O) (T : C ⊗ N' ⟶ O)
    (he : ∀ m : N' ⟶ E, (C ◁ m) ≫ evalC = T → m = e.hom)
    (hp : (c.hom ⊗ p.hom) ≫ evalC = (tensorIso c n).hom ≫ T) :
    n ≪≫ e = p := by
  apply Iso.ext
  apply (cancel_epi n.inv).mp
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc]
  exact (he (n.inv ≫ p.hom) (evaluation_cancel c n p evalC T hp)).symm

private theorem dual_composition_evaluation {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    ((schemeModulePullbackCompIso f g).hom.app L.obj ⊗
      ((schemeModulePullback f).mapIso (schemeModulePullbackDualIso g L) ≪≫
        schemeModulePullbackDualIso f (pullbackInvertibleSheaf g L) ≪≫
        (sectionDualIso X ((schemeModulePullbackCompIso f g).app L.obj)).symm).hom) ≫
      KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond
        ((schemeModulePullback (f ≫ g)).obj L.obj) =
    (tensorIso ((schemeModulePullbackCompIso f g).app L.obj)
      ((schemeModulePullbackCompIso f g).app
        (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))).hom ≫
      (schemeModulePullbackDualEvaluationIso (f ≫ g) L).hom := by
  have h := schemeModulePullbackDualComparison_evaluation f
    (pullbackInvertibleSheaf g L)
    ((schemeModulePullback g).obj (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))
    (schemeModulePullbackDualIso g L) ((schemeModulePullbackCompIso f g).app L.obj)
  have he := congrArg (fun a =>
    (schemeModulePullbackTensorIso f ((schemeModulePullback g).obj L.obj)
      ((schemeModulePullback g).obj (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))).inv ≫
      (schemeModulePullback f).map a ≫ (schemeModulePullbackUnitIso f).hom)
    (schemeModulePullbackDualIso_evaluation g L)
  exact h.trans (he.trans (schemeModulePullbackDualEvaluationIso_comp f g L).symm)

/-- The original dual pullback comparisons satisfy their exact composition law. -/
theorem schemeModulePullbackDualIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (L : InvertibleSheaf Z) :
    (schemeModulePullback f).mapIso (schemeModulePullbackDualIso g L) ≪≫
      schemeModulePullbackDualIso f (pullbackInvertibleSheaf g L) =
    (schemeModulePullbackCompIso f g).app
        (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj) ≪≫
      schemeModulePullbackDualIso (f ≫ g) L ≪≫
      sectionDualIso X ((schemeModulePullbackCompIso f g).app L.obj) := by
  have h := comparison_unique ((schemeModulePullbackCompIso f g).app L.obj)
    ((schemeModulePullbackCompIso f g).app (KltDP.SheafOfModules.dual Z.ringCatSheaf L.obj))
    ((schemeModulePullback f).mapIso (schemeModulePullbackDualIso g L) ≪≫
      schemeModulePullbackDualIso f (pullbackInvertibleSheaf g L) ≪≫
      (sectionDualIso X ((schemeModulePullbackCompIso f g).app L.obj)).symm)
    (schemeModulePullbackDualIso (f ≫ g) L)
    (KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond
      ((schemeModulePullback (f ≫ g)).obj L.obj))
    (schemeModulePullbackDualEvaluationIso (f ≫ g) L).hom
    (schemeModulePullbackDualIso_unique (f ≫ g) L)
    (dual_composition_evaluation f g L)
  apply Iso.ext
  apply (cancel_mono (sectionDualIso X ((schemeModulePullbackCompIso f g).app L.obj)).inv).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using congrArg (fun a => a.hom) h.symm

end KltDP.Geometry
