import KltDP.Geometry.SchemeModulePullbackTensorComp
import KltDP.Geometry.SchemeModulePullbackTensorNaturality

/-!
# Combine the original ambient and normal target comparisons

The original pullback tensor comparison is natural and respects composition.
These proved laws combine the original component restriction squares into
the target square used by the actual intrinsic adjunction chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedAdjunctionTensorRefinement

local instance refinementTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem inverse_word {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A N : C} {A' N' : D} (e : A ≅ N) (e' : A' ≅ N')
    (ν : F.obj N ⟶ N') (r : F.obj A ⟶ A')
    (h : F.map e.hom ≫ ν = r ≫ e'.hom) :
    F.map e.inv ≫ r = ν ≫ e'.inv := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.map_inv_hom_id_assoc]

private def tensor_comp_inv {X U V : Scheme.{u}} (b : V ⟶ U) (i : U ⟶ X)
    (M N : X.Modules) :=
  inverse_word (schemeModulePullback b) (schemeModulePullbackTensorIso i M N)
    (schemeModulePullbackTensorIso (b ≫ i) M N)
    ((schemeModulePullbackTensorIso b
      ((schemeModulePullback i).obj M) ((schemeModulePullback i).obj N)).hom ≫
      ((schemeModulePullbackCompIso b i).hom.app M ⊗
        (schemeModulePullbackCompIso b i).hom.app N))
    ((schemeModulePullbackCompIso b i).hom.app (M ⊗ N))
    (schemeModulePullbackTensorIso_comp_hom b i M N)

/-- The actual two component charts commute with the original tensor and chart pullback.
In the adjunction application both component equations are supplied by their proved original
ambient and normal refinements. No new tensor comparison is constructed. -/
theorem target_refinement {X U V : Scheme.{u}}
    (b : V ⟶ U) (i : U ⟶ X) (j : V ⟶ X) (h : b ≫ i = j) (M N : X.Modules)
    {A B : U.Modules} {A' B' : V.Modules}
    (α : A ⟶ (schemeModulePullback i).obj M)
    (β : B ⟶ (schemeModulePullback i).obj N)
    (α' : A' ⟶ (schemeModulePullback j).obj M)
    (β' : B' ⟶ (schemeModulePullback j).obj N)
    (δ : (schemeModulePullback b).obj A ⟶ A')
    (γ : (schemeModulePullback b).obj B ⟶ B')
    (hA : (schemeModulePullback b).map α ≫
        (schemeModulePullbackCompIso b i).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app M = δ ≫ α')
    (hB : (schemeModulePullback b).map β ≫
        (schemeModulePullbackCompIso b i).hom.app N ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app N = γ ≫ β') :
    (schemeModulePullback b).map
        ((α ⊗ β) ≫ (schemeModulePullbackTensorIso i M N).inv) ≫
        (schemeModulePullbackCompIso b i).hom.app (M ⊗ N) ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app (M ⊗ N) =
      (schemeModulePullbackTensorIso b A B).hom ≫ (δ ⊗ γ) ≫
        (α' ⊗ β') ≫ (schemeModulePullbackTensorIso j M N).inv := by
  subst j
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at hA hB ⊢
  have hTensor :
      ((schemeModulePullback b).map α ⊗ (schemeModulePullback b).map β) ≫
          ((schemeModulePullbackCompIso b i).hom.app M ⊗
            (schemeModulePullbackCompIso b i).hom.app N) =
        (δ ⊗ γ) ≫ (α' ⊗ β') := by
    rw [← tensor_comp, hA, hB, tensor_comp]
  have hInv := tensor_comp_inv b i M N
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hInv]
  simp only [Category.assoc]
  rw [← Category.assoc ((schemeModulePullback b).map (α ⊗ β))
      (schemeModulePullbackTensorIso b
        ((schemeModulePullback i).obj M) ((schemeModulePullback i).obj N)).hom,
    schemeModulePullbackTensorIso_natural b α β]
  calc
    _ = (schemeModulePullbackTensorIso b A B).hom ≫
        (((schemeModulePullback b).map α ⊗ (schemeModulePullback b).map β) ≫
          ((schemeModulePullbackCompIso b i).hom.app M ⊗
            (schemeModulePullbackCompIso b i).hom.app N)) ≫
        (schemeModulePullbackTensorIso (b ≫ i) M N).inv := by
      simp only [Category.assoc]
    _ = _ := by
      rw [hTensor]
      simp only [Category.assoc]

end KltDP.Geometry.GluedAdjunctionTensorRefinement
