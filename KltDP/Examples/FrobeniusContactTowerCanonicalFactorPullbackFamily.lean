import KltDP.Examples.FrobeniusContactTowerCanonicalFactorSelect

/-!
# Restriction and selection of the original finite tensor

The existing pullback comparison transports the original family product map.
Use that equation to remove factors whose actual pulled inclusions are
invertible, without choosing unrelated trivializations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorPullbackFamily

open KltDP.Geometry FrobeniusContactTowerCanonicalFactorFiniteTensor
open FrobeniusContactTowerCanonicalFactorUnits FrobeniusContactTowerCanonicalFactorSelect

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorPullbackFamilyModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- If the actual pulled factors are units, their original full product is a unit. -/
theorem pulledFamilyInclusion_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ j, IsIso ((schemeModulePullback f).map (i j) ≫
      (schemeModulePullbackUnitIso f).hom)) :
    IsIso ((schemeModulePullback f).map (familyInclusion n L i) ≫
      (schemeModulePullbackUnitIso f).hom) := by
  letI : IsIso (familyInclusion n (fun j => pullbackInvertibleSheaf f (L j))
      (fun j => (schemeModulePullback f).map (i j) ≫
        (schemeModulePullbackUnitIso f).hom)) :=
    familyInclusion_isIso n _ _ h
  rw [← familyPullbackIso_comp f n L i]
  infer_instance

/-- Pull back the original family, then remove the other factors by their actual inclusions. -/
def pulledFamilySelectIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (r : Fin n) (h : ∀ s, s ≠ r → IsIso ((schemeModulePullback f).map (i s) ≫
      (schemeModulePullbackUnitIso f).hom)) :
    (schemeModulePullback f).obj (familyLine n L).obj ≅
      (schemeModulePullback f).obj (L r).obj :=
  familyPullbackIso f n L ≪≫
    familySelectIso n (fun j => pullbackInvertibleSheaf f (L j))
      (fun j => (schemeModulePullback f).map (i j) ≫
        (schemeModulePullbackUnitIso f).hom) r h

/-- The restriction and selection comparison retains the original entire product inclusion. -/
theorem pulledFamilySelectIso_inclusion {X Y : Scheme.{u}} (f : Y ⟶ X)
    (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (r : Fin n) (h : ∀ s, s ≠ r → IsIso ((schemeModulePullback f).map (i s) ≫
      (schemeModulePullbackUnitIso f).hom)) :
    (pulledFamilySelectIso f n L i r h).hom ≫
        (schemeModulePullback f).map (i r) ≫ (schemeModulePullbackUnitIso f).hom =
      (schemeModulePullback f).map (familyInclusion n L i) ≫
        (schemeModulePullbackUnitIso f).hom := by
  simp only [pulledFamilySelectIso, Iso.trans_hom, Category.assoc]
  rw [familySelectIso_inclusion]
  exact familyPullbackIso_comp f n L i

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorPullbackFamily
