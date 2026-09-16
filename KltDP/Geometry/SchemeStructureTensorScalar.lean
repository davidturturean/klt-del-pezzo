import KltDP.Geometry.SchemeModulePullbackTensorMultiplication
import KltDP.Geometry.SchemeConormalEquationChange
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Scalar normalization for the chosen structure-module multiplication

The existing comparison from the tensor unit to the actual structure module
transports the two original unitors. Their naturality identifies the tensor
of two scalar maps with multiplication by the product of the two sections.
This uses the exact multiplication already used for the original ideal product.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance scalarTensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem transportedUnit_mul_eq_left
    {C : Type*} [Category C] [MonoidalCategory C] {O : C} (e : 𝟙_ C ≅ O) :
    O ◁ e.inv ≫ (ρ_ O).hom = e.inv ▷ O ≫ (λ_ O).hom := by
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc]
  rw [← rightUnitor_naturality, ← leftUnitor_naturality,
    whisker_exchange_assoc, unitors_equal]

private theorem transportedUnit_mul_natural_right
    {C : Type*} [Category C] [MonoidalCategory C] {O : C}
    (e : 𝟙_ C ≅ O) (f : O ⟶ O) :
    f ▷ O ≫ (O ◁ e.inv ≫ (ρ_ O).hom) =
      (O ◁ e.inv ≫ (ρ_ O).hom) ≫ f := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

private theorem transportedUnit_mul_natural_left
    {C : Type*} [Category C] [MonoidalCategory C] {O : C}
    (e : 𝟙_ C ≅ O) (g : O ⟶ O) :
    O ◁ g ≫ (O ◁ e.inv ≫ (ρ_ O).hom) =
      (O ◁ e.inv ≫ (ρ_ O).hom) ≫ g := by
  simp only [transportedUnit_mul_eq_left]
  rw [whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]

private theorem transportedUnit_mul_endomorphisms
    {C : Type*} [Category C] [MonoidalCategory C] {O : C}
    (e : 𝟙_ C ≅ O) (f g : O ⟶ O) :
    (f ⊗ g) ≫ (O ◁ e.inv ≫ (ρ_ O).hom) =
      (O ◁ e.inv ≫ (ρ_ O).hom) ≫ f ≫ g := by
  rw [tensorHom_def, Category.assoc, transportedUnit_mul_natural_left,
    ← Category.assoc, transportedUnit_mul_natural_right, Category.assoc]

/-- The chosen structure multiplication sends a tensor of endomorphisms to their composite. -/
theorem schemeStructureTensor_endomorphisms {X : Scheme.{u}}
    (f g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf) :
    (f ⊗ g) ≫
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫ f ≫ g := by
  -- Pin the original counit comparison to the actual scheme module category, as the
  -- accepted multiplication lemma does, so its monoidal instance is the chosen one.
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  rw [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change (f ⊗ g) ≫ (_root_.SheafOfModules.unit X.ringCatSheaf ◁ e.inv ≫
      (ρ_ (_root_.SheafOfModules.unit X.ringCatSheaf)).hom) =
    (_root_.SheafOfModules.unit X.ringCatSheaf ◁ e.inv ≫
      (ρ_ (_root_.SheafOfModules.unit X.ringCatSheaf)).hom) ≫ f ≫ g
  exact transportedUnit_mul_endomorphisms (C := X.Modules) e f g

/-- Two normalized scalar frames multiply by the literal product of their original sections. -/
theorem schemeStructureTensor_scalar_mul {X : Scheme.{u}} (d q : Γ(X, ⊤)) :
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (schemeScalarEnd d ⊗ schemeScalarEnd q) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
        schemeScalarEnd (d * q) := by
  rw [schemeStructureTensor_endomorphisms, Iso.inv_hom_id_assoc, schemeScalarEnd_mul]

end KltDP.Geometry
