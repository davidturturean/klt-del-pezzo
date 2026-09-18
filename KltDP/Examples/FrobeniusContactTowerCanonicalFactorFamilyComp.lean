import KltDP.Examples.FrobeniusContactTowerCanonicalFactorFiniteTensor
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorOffRange

/-!
# Original finite-family pullback under an actual projection identity

Undo the original finite tensor pullback comparison, then use the original
pullback-composition map and the given equality of scheme morphisms. The
normalization is proved abstractly before any actual cluster is specialized.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorFamilyComp

open KltDP.Geometry FrobeniusContactTowerCanonicalFactorFiniteTensor
open FrobeniusContactTowerCanonicalFactorOffRange

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem familyPullbackIso_inv_inclusion {X Y : Scheme.{u}} (f : Y ⟶ X)
    (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (familyPullbackIso f n L).inv ≫ (schemeModulePullback f).map (familyInclusion n L i) ≫
        (schemeModulePullbackUnitIso f).hom =
      familyInclusion n (fun j => pullbackInvertibleSheaf f (L j))
        (fun j => (schemeModulePullback f).map (i j) ≫
          (schemeModulePullbackUnitIso f).hom) := by
  rw [← familyPullbackIso_comp f n L i, Iso.inv_hom_id_assoc]

/-- The forward map uses exactly the original finite tensor and pullback-composition maps. -/
def familyCompositeMap {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    (n : ℕ) (L : Fin n → InvertibleSheaf X) :
    (schemeModulePullback g).obj
        (familyLine n (fun j => pullbackInvertibleSheaf f (L j))).obj ⟶
      (schemeModulePullback t).obj (familyLine n L).obj :=
  (schemeModulePullback g).map (familyPullbackIso f n L).inv ≫
    (schemeModulePullbackCompIso g f).hom.app (familyLine n L).obj ≫
    eqToHom (congrArg (fun r => (schemeModulePullback r).obj (familyLine n L).obj) h)

/-- This original forward map is invertible. -/
theorem familyCompositeMap_isIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    (n : ℕ) (L : Fin n → InvertibleSheaf X) :
    IsIso (familyCompositeMap f g t h n L) := by
  unfold familyCompositeMap
  infer_instance

/-- The original map preserves the pulled product inclusion under the actual projection identity. -/
theorem familyCompositeMap_inclusion {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    familyCompositeMap f g t h n L ≫
        (schemeModulePullback t).map (familyInclusion n L i) ≫
        (schemeModulePullbackUnitIso t).hom =
      (schemeModulePullback g).map
        (familyInclusion n (fun j => pullbackInvertibleSheaf f (L j))
          (fun j => (schemeModulePullback f).map (i j) ≫
            (schemeModulePullbackUnitIso f).hom)) ≫
        (schemeModulePullbackUnitIso g).hom := by
  subst t
  simp only [familyCompositeMap, eqToHom_refl, Category.comp_id, Category.assoc]
  rw [pulledInclusion_comp, ← CategoryTheory.Functor.map_comp_assoc,
    familyPullbackIso_inv_inclusion]

/-- The inverse is attached to this same original forward map. -/
def familyCompositeIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    (n : ℕ) (L : Fin n → InvertibleSheaf X) :
    (schemeModulePullback g).obj
        (familyLine n (fun j => pullbackInvertibleSheaf f (L j))).obj ≅
      (schemeModulePullback t).obj (familyLine n L).obj := by
  letI := familyCompositeMap_isIso f g t h n L
  exact asIso (familyCompositeMap f g t h n L)

@[simp] theorem familyCompositeIso_hom {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (t : Z ⟶ X) (h : g ≫ f = t)
    (n : ℕ) (L : Fin n → InvertibleSheaf X) :
    (familyCompositeIso f g t h n L).hom = familyCompositeMap f g t h n L := rfl

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorFamilyComp
