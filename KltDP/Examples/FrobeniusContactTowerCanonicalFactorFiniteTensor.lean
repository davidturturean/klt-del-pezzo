import KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensor

/-!
# Finite iteration of the original line tensor and its inclusion

This is recursion of the existing binary tensor over the actual ordered
finite family. Both the maps and pullback comparison retain the original
structure-module inclusions. No isomorphism class replaces an actual line,
and no compatibility is built into a new geometric structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorFiniteTensor

open KltDP.Geometry FrobeniusContactTowerCanonicalFactorTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance finiteFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The finite product uses only the original trivial line and original binary tensor. -/
def familyLine {X : Scheme.{u}} : (n : ℕ) →
    (Fin n → InvertibleSheaf X) → InvertibleSheaf X
  | 0, _ => InvertibleSheaf.trivial X
  | n + 1, L => tensorLine (familyLine n (fun j => L j.castSucc)) (L (Fin.last n))

/-- Multiply the actual inclusions in that same order. -/
def familyInclusion {X : Scheme.{u}} : (n : ℕ) → (L : Fin n → InvertibleSheaf X) →
    ((j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) →
    ((familyLine n L).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
  | 0, _, _ => 𝟙 _
  | n + 1, L, i => productInclusion
      (familyInclusion n (fun j => L j.castSucc) (fun j => i j.castSucc)) (i (Fin.last n))

/-- Tensor the given actual line isomorphisms in the same finite order. -/
def familyIso {X : Scheme.{u}} : (n : ℕ) →
    (L M : Fin n → InvertibleSheaf X) → ((j : Fin n) → (L j).obj ≅ (M j).obj) →
    ((familyLine n L).obj ≅ (familyLine n M).obj)
  | 0, _, _, _ => Iso.refl _
  | n + 1, L, M, e => tensorIso
      (familyIso n (fun j => L j.castSucc) (fun j => M j.castSucc)
        (fun j => e j.castSucc)) (e (Fin.last n))

/-- The existing tensor comparison preserves the original product inclusion. -/
@[reassoc] theorem tensorIso_productInclusion {X : Scheme.{u}} {I J M N : X.Modules}
    (e : I ≅ J) (f : M ≅ N)
    (i : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : N ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (tensorIso e f).hom ≫ productInclusion i j =
      productInclusion (e.hom ≫ i) (f.hom ≫ j) := by
  simp only [productInclusion, Category.assoc]
  rw [tensorIso_structureInclusion_assoc]

/-- Pointwise normalized actual comparisons remain normalized after finite tensoring. -/
theorem familyIso_comp {X : Scheme.{u}} (n : ℕ) (L M : Fin n → InvertibleSheaf X)
    (e : (j : Fin n) → (L j).obj ≅ (M j).obj)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : (r : Fin n) → (M r).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ r, (e r).hom ≫ j r = i r) :
    (familyIso n L M e).hom ≫ familyInclusion n M j = familyInclusion n L i := by
  induction n with
  | zero =>
      change (𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) ≫ 𝟙 _ = 𝟙 _
      exact Category.id_comp _
  | succ n ih =>
      change (tensorIso
        (familyIso n (fun r => L r.castSucc) (fun r => M r.castSucc)
          (fun r => e r.castSucc)) (e (Fin.last n))).hom ≫
        productInclusion
          (familyInclusion n (fun r => M r.castSucc) (fun r => j r.castSucc))
          (j (Fin.last n)) =
        productInclusion
          (familyInclusion n (fun r => L r.castSucc) (fun r => i r.castSucc))
          (i (Fin.last n))
      rw [tensorIso_productInclusion, ih _ _ _ _ _ (fun r => h r.castSucc), h (Fin.last n)]

/-- Pullback of the finite tensor uses the original tensor and unit comparisons at every step. -/
def familyPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) : (n : ℕ) →
    (L : Fin n → InvertibleSheaf X) →
    (schemeModulePullback f).obj (familyLine n L).obj ≅
      (familyLine n (fun j => pullbackInvertibleSheaf f (L j))).obj
  | 0, _ => schemeModulePullbackUnitIso f
  | n + 1, L => schemeModulePullbackTensorIso f
      (familyLine n (fun j => L j.castSucc)).obj (L (Fin.last n)).obj ≪≫
      tensorIso (familyPullbackIso f n (fun j => L j.castSucc))
        (Iso.refl ((schemeModulePullback f).obj (L (Fin.last n)).obj))

/-- The original pullback tensor comparison retains multiplication of the original maps. -/
theorem pullback_productInclusion {X Y : Scheme.{u}} (f : Y ⟶ X) {I J : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (schemeModulePullbackTensorIso f I J).hom ≫
      productInclusion
        ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)
        ((schemeModulePullback f).map j ≫ (schemeModulePullbackUnitIso f).hom) =
    (schemeModulePullback f).map (productInclusion i j) ≫
      (schemeModulePullbackUnitIso f).hom := by
  simp only [productInclusion, Functor.map_comp, Category.assoc]
  rw [schemeModulePullbackTensorIso_inclusion_assoc]

/-- The finite pullback comparison preserves the original whole product inclusion. -/
theorem familyPullbackIso_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (familyPullbackIso f n L).hom ≫
        familyInclusion n (fun j => pullbackInvertibleSheaf f (L j))
          (fun j => (schemeModulePullback f).map (i j) ≫
            (schemeModulePullbackUnitIso f).hom) =
      (schemeModulePullback f).map (familyInclusion n L i) ≫
        (schemeModulePullbackUnitIso f).hom := by
  induction n with
  | zero =>
      change (schemeModulePullbackUnitIso f).hom ≫ 𝟙 _ =
        (schemeModulePullback f).map (𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) ≫
          (schemeModulePullbackUnitIso f).hom
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  | succ n ih =>
      simp only [familyPullbackIso, familyInclusion, Iso.trans_hom, Category.assoc]
      rw [tensorIso_productInclusion]
      simp only [Iso.refl_hom, Category.id_comp]
      rw [ih]
      exact pullback_productInclusion f _ _

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorFiniteTensor
