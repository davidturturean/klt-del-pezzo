import KltDP.Geometry.SchemeInvertibleDualPullback
import KltDP.Geometry.SchemeDualTensorNaturality

/-!
# Naturality of the original dual pullback comparison

The existing evaluation characterization fixes the actual pullback/dual
comparison. Naturality of the original tensor comparison and the original
dual evaluation imply that it respects isomorphisms of invertible sheaves.
No compatibility datum or replacement dual is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance dualNaturalitySectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance dualNaturalityTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem evaluation_naturality_word
    {C : Type*} [Category C] [MonoidalCategory C]
    {P Q EA EB DA DB O : C} (c : P ≅ Q) (d : EB ≅ EA)
    (s : DB ≅ DA) (a : EA ≅ DA)
    (evalP : P ⊗ DA ⟶ O) (evalQ : Q ⊗ DB ⟶ O)
    (EP : P ⊗ EA ⟶ O) (EQ : Q ⊗ EB ⟶ O)
    (ha : (P ◁ a.hom) ≫ evalP = EP)
    (hc : (c.hom ⊗ s.inv) ≫ evalQ = evalP)
    (hd : (c.hom ⊗ d.inv) ≫ EQ = EP) :
    (Q ◁ (d.hom ≫ a.hom ≫ s.inv)) ≫ evalQ = EQ := by
  calc
    _ = (c.inv ⊗ d.hom) ≫ (P ◁ a.hom) ≫ (c.hom ⊗ s.inv) ≫ evalQ := by
      simp only [← id_tensorHom, ← tensor_comp_assoc, Category.comp_id,
        Category.id_comp, Category.assoc, Iso.inv_hom_id]
    _ = (c.inv ⊗ d.hom) ≫ EP := by rw [hc, ha]
    _ = (c.inv ⊗ d.hom) ≫ (c.hom ⊗ d.inv) ≫ EQ := by rw [hd]
    _ = EQ := by
      rw [← tensor_comp_assoc, Iso.inv_hom_id, Iso.hom_inv_id, tensor_id,
        Category.id_comp]

@[reassoc]
private theorem pullbackTensor_inv_natural {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M M' N N' : X.Modules} (g : M ⟶ M') (h : N ⟶ N') :
    ((schemeModulePullback f).map g ⊗ (schemeModulePullback f).map h) ≫
        (schemeModulePullbackTensorIso f M' N').inv =
      (schemeModulePullbackTensorIso f M N).inv ≫
        (schemeModulePullback f).map (g ⊗ h) := by
  apply (cancel_epi (schemeModulePullbackTensorIso f M N).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc,
    ← schemeModulePullbackTensorIso_natural f g h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (L₀ L₁ : InvertibleSheaf X)
  (e : L₀.obj ≅ L₁.obj)

/-- The actual transported evaluation respects the original sheaf isomorphism
and its original contravariant dual. -/
theorem schemeModulePullbackDualEvaluationIso_natural :
    (((schemeModulePullback f).mapIso e).hom ⊗
        ((schemeModulePullback f).mapIso (sectionDualIso X e)).inv) ≫
      (schemeModulePullbackDualEvaluationIso f L₁).hom =
    (schemeModulePullbackDualEvaluationIso f L₀).hom := by
  simp only [Functor.mapIso_hom, Functor.mapIso_inv,
    schemeModulePullbackDualEvaluationIso_hom]
  rw [pullbackTensor_inv_natural_assoc, ← Functor.map_comp_assoc,
    SchemeDualTensorNaturality.sectionDualIso_evaluation]

/-- The original dual pullback comparison commutes with isomorphisms of the
original invertible sheaves, with the exact evaluation normalization. -/
theorem schemeModulePullbackDualIso_natural :
    (schemeModulePullback f).mapIso (sectionDualIso X e) ≪≫
        schemeModulePullbackDualIso f L₀ =
      schemeModulePullbackDualIso f L₁ ≪≫
        sectionDualIso Y ((schemeModulePullback f).mapIso e) := by
  apply Iso.ext
  apply (cancel_mono (sectionDualIso Y ((schemeModulePullback f).mapIso e)).inv).mp
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine schemeModulePullbackDualIso_unique f L₁ _ ?_
  exact evaluation_naturality_word ((schemeModulePullback f).mapIso e)
    ((schemeModulePullback f).mapIso (sectionDualIso X e))
    (sectionDualIso Y ((schemeModulePullback f).mapIso e))
    (schemeModulePullbackDualIso f L₀)
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond
      ((schemeModulePullback f).obj L₀.obj))
    (KltDP.SheafOfModules.evaluation Y.sheaf.val Y.ringCatSheaf.cond
      ((schemeModulePullback f).obj L₁.obj))
    (schemeModulePullbackDualEvaluationIso f L₀).hom
    (schemeModulePullbackDualEvaluationIso f L₁).hom
    (schemeModulePullbackDualIso_evaluation f L₀)
    (SchemeDualTensorNaturality.sectionDualIso_evaluation Y
      ((schemeModulePullback f).mapIso e))
    (schemeModulePullbackDualEvaluationIso_natural f L₀ L₁ e)

end KltDP.Geometry
