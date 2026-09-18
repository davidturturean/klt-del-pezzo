import KltDP.Examples.FrobeniusContactTowerCanonicalFactorFiniteTensor
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Removing invertible original inclusion factors

A factor whose actual inclusion is invertible can be replaced by the actual
structure module. This file retains the original product map under the
left and right unit comparisons, and proves that a finite product of such
original inclusions is invertible.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorUnits

open KltDP.Geometry FrobeniusContactTowerCanonicalFactorTensor
open FrobeniusContactTowerCanonicalFactorFiniteTensor

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorUnitsModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem unitAction_right {C : Type*} [Category C] [MonoidalCategory C]
    {I O : C} (e : O ≅ 𝟙_ C) (i : I ⟶ O) :
    (i ≫ e.hom) ▷ O ≫ (λ_ O).hom = I ◁ e.hom ≫ (ρ_ I).hom ≫ i := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
    unitors_equal, rightUnitor_naturality]

/-- Multiplication by the actual unit on the right is the original right structure action. -/
theorem productInclusion_right_unit {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    productInclusion i (𝟙 _) = (schemeStructureTensorRightIso I).hom ≫ i := by
  simpa only [productInclusion, schemeStructureTensorInclusion,
    schemeStructureTensorRightIso, SchemeModuleStructureUnit.iso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorLeft_map,
    Category.comp_id, Category.assoc] using
    unitAction_right (SchemeModuleStructureUnit.iso X) i

/-- An actual invertible right factor can be removed without changing the remaining inclusion. -/
theorem tensorRightUnit_comp {X : Scheme.{u}} {I J M : X.Modules}
    (e : I ≅ J) (v : M ≅ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (tensorIso e v).hom ≫ (schemeStructureTensorRightIso J).hom ≫ j =
      productInclusion (e.hom ≫ j) v.hom := by
  rw [← productInclusion_right_unit, tensorIso_productInclusion, Category.comp_id]

/-- A product of two actual invertible inclusions is invertible. -/
theorem productInclusion_isIso {X : Scheme.{u}} {I J : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) [IsIso i] [IsIso j] :
    IsIso (productInclusion i j) := by
  unfold productInclusion schemeStructureTensorInclusion
  infer_instance

/-- The product of a finite family of original invertible inclusions is invertible. -/
theorem familyInclusion_isIso {X : Scheme.{u}} (n : ℕ) (L : Fin n → InvertibleSheaf X)
    (i : (j : Fin n) → (L j).obj ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (h : ∀ j, IsIso (i j)) : IsIso (familyInclusion n L i) := by
  induction n with
  | zero =>
      change IsIso (𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf))
      infer_instance
  | succ n ih =>
      letI := ih (fun j => L j.castSucc) (fun j => i j.castSucc) (fun j => h j.castSucc)
      letI := h (Fin.last n)
      exact productInclusion_isIso
        (familyInclusion n (fun j => L j.castSucc) (fun j => i j.castSucc)) (i (Fin.last n))

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorUnits
