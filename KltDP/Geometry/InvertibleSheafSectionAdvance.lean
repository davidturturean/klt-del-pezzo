import KltDP.Geometry.InvertibleSheafTwistFrame

/-!
# Advancing original twisted sections by further powers

Append the original line-sheaf section to the actual recursive tensor
power, one factor at a time. This constructs an actual map from degree n
to degree n+k. It carries the original degree-n power section to the
original degree-(n+k) section, and does the same on every coefficient twist.

These maps allow a common further power to be applied to already constructed
original affine lifts. No new tensor-power representative or additive-power
isomorphism is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.InvertibleSheafSectionAdvance

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionAdvanceMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame

private theorem transportedUnit_right_naturality
    {C : Type*} [Category C] [MonoidalCategory C] {O A B : C}
    (e : 𝟙_ C ≅ O) (f : A ⟶ B) :
    (f ⊗ 𝟙 O) ≫ (B ◁ e.inv ≫ (ρ_ B).hom) =
      (A ◁ e.inv ≫ (ρ_ A).hom) ≫ f := by
  rw [tensorHom_id, ← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

variable {X : Scheme.{u}}

private theorem structureRight_naturality {A B : X.Modules} (f : A ⟶ B) :
    (f ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeStructureTensorRightIso B).hom =
      (schemeStructureTensorRightIso A).hom ≫ f := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  change (f ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) ≫
      (B ◁ e.inv ≫ (ρ_ B).hom) = (A ◁ e.inv ≫ (ρ_ A).hom) ≫ f
  exact transportedUnit_right_naturality e f

private theorem structureRight_inv_naturality {A B : X.Modules} (f : A ⟶ B) :
    f ≫ (schemeStructureTensorRightIso B).inv =
      (schemeStructureTensorRightIso A).inv ≫
        (f ⊗ 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf)) := by
  apply (cancel_mono (schemeStructureTensorRightIso B).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [structureRight_naturality f, Iso.inv_hom_id_assoc]

private theorem section_step {A B : X.Modules}
    (f : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ A)
    (g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ B) :
    f ≫ (schemeStructureTensorRightIso A).inv ≫ (𝟙 A ⊗ g) =
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (f ⊗ g) := by
  rw [← Category.assoc f, structureRight_inv_naturality f, Category.assoc,
    ← tensor_comp, Category.comp_id, Category.id_comp]

variable (L : InvertibleSheaf X) (s : L.obj.sections)

/-- Append the actual original section to the actual recursive power. -/
def advance (n : ℕ) : (k : ℕ) → (power L n).obj ⟶ (power L (n + k)).obj
  | 0 => 𝟙 _
  | k + 1 => advance n k ≫ (schemeStructureTensorRightIso (power L (n + k)).obj).inv ≫
      (𝟙 (power L (n + k)).obj ⊗ L.obj.unitHomEquiv.symm s)

/-- Further multiplication carries the original power section to the
original higher power section, including degree zero. -/
theorem powerSectionHom_advance (n k : ℕ) :
    powerSectionHom L s n ≫ advance L s n k = powerSectionHom L s (n + k) := by
  induction k with
  | zero => simp only [advance, Category.comp_id, Nat.add_zero]
  | succ k ih =>
    change powerSectionHom L s n ≫ advance L s n k ≫
        (schemeStructureTensorRightIso (power L (n + k)).obj).inv ≫
          (𝟙 (power L (n + k)).obj ⊗ L.obj.unitHomEquiv.symm s) =
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (powerSectionHom L s (n + k) ⊗ L.obj.unitHomEquiv.symm s)
    rw [← Category.assoc (powerSectionHom L s n) (advance L s n k), ih]
    exact section_step (powerSectionHom L s (n + k)) (L.obj.unitHomEquiv.symm s)

/-- The original coefficient twist is carried into the original higher twist. -/
def rightAdvance (M : X.Modules) (n k : ℕ) :
    M ⊗ (power L n).obj ⟶ M ⊗ (power L (n + k)).obj :=
  𝟙 M ⊗ advance L s n k

/-- Advancing a multiplied coefficient section is the original higher
power-section multiplication map. -/
theorem rightTwistMap_rightAdvance (M : X.Modules) (n k : ℕ) :
    rightTwistMap M L s n ≫ rightAdvance L s M n k = rightTwistMap M L s (n + k) := by
  simp only [rightTwistMap, rightAdvance, Category.assoc]
  rw [← tensor_comp, Category.id_comp, powerSectionHom_advance]

end KltDP.Geometry.InvertibleSheafSectionAdvance
