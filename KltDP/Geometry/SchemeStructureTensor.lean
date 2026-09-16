import KltDP.Geometry.SheafPicard

/-!
# The original structure-module multiplication through monoidal sheafification

The structure module is identified with the chosen tensor unit by the
original sheafification counit. The resulting right-unit multiplication
agrees with sheafification of the literal presheaf-unit multiplication.
Only the existing monoidal structure and its proved unitality are used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureTensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance structureTensorPresheaves (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance structureTensorSheafification (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

/-- Tensoring with the actual structure module uses its original counit comparison. -/
def schemeStructureTensorRightIso {X : Scheme.{u}} (M : X.Modules) :
    M ⊗ _root_.SheafOfModules.unit X.ringCatSheaf ≅ M :=
  (tensorLeft M).mapIso
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm ≪≫
    ρ_ M

/-- The unit chosen for monoidal sheafification is its literal image of the presheaf unit. -/
theorem schemeSheafification_tensorUnit_hom (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) = 𝟙 _ := rfl

/-- The inverse monoidal unit comparison is the same identity. -/
theorem schemeSheafification_tensorUnit_inv (X : Scheme.{u}) :
    Functor.OplaxMonoidal.η
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) = 𝟙 _ := rfl

/-- Right unitality for the exact sheafification tensorator, with its identity unit map. -/
@[reassoc] theorem schemeSheafification_lax_right_unitality (X : Scheme.{u})
    (P : X.PresheafOfModules) :
    Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        P (𝟙_ X.PresheafOfModules) ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (ρ_ P).hom =
      (ρ_ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).hom := by
  simpa only [schemeSheafification_tensorUnit_hom,
    MonoidalCategory.whiskerLeft_id, Category.id_comp] using
    (Functor.LaxMonoidal.right_unitality
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P).symm

/-- Right unitality for the inverse of the same original tensorator. -/
@[reassoc] theorem schemeSheafification_oplax_right_unitality (X : Scheme.{u})
    (P : X.PresheafOfModules) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        P (𝟙_ X.PresheafOfModules) ≫
        (ρ_ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).hom =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (ρ_ P).hom := by
  simpa only [schemeSheafification_tensorUnit_inv,
    MonoidalCategory.whiskerLeft_id, Category.id_comp] using
    Functor.OplaxMonoidal.right_unitality_hom
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P

private theorem tensorUnitIso_multiplication {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) :
    (e.hom ⊗ e.hom) ≫ (O ◁ e.inv ≫ (ρ_ O).hom) =
      (ρ_ (𝟙_ C)).hom ≫ e.hom := by
  rw [tensorHom_def, Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    e.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    rightUnitor_naturality]

/-- Sheafification of the actual presheaf-unit multiplication is the original
structure-module multiplication, after the two original counits. -/
@[reassoc] theorem schemeSheafification_structure_mul (X : Scheme.{u}) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        (𝟙_ X.PresheafOfModules) (𝟙_ X.PresheafOfModules) ≫
      ((PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom ⊗
        (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  rw [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change Functor.OplaxMonoidal.δ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
      (𝟙_ X.PresheafOfModules) (𝟙_ X.PresheafOfModules) ≫
      (e.hom ⊗ e.hom) ≫
      (_root_.SheafOfModules.unit X.ringCatSheaf ◁ e.inv ≫
        (ρ_ (_root_.SheafOfModules.unit X.ringCatSheaf)).hom) =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫ e.hom
  rw [tensorUnitIso_multiplication (C := X.Modules) e]
  exact schemeSheafification_oplax_right_unitality_assoc
    X (𝟙_ X.PresheafOfModules) e.hom

/-- The existing tensor-to-sheafification comparison gives exactly the same
original structure-module multiplication. -/
@[reassoc] theorem schemeSheafTensorIso_structure_mul (X : Scheme.{u}) :
    (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
      (_root_.SheafOfModules.unit X.ringCatSheaf)
      (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom =
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [PresheafOfModules.sheafTensorIsoSheafification, Iso.trans_hom,
    tensorIso_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  change (e.inv ⊗ e.inv) ≫
      Functor.LaxMonoidal.μ
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        (𝟙_ X.PresheafOfModules) (𝟙_ X.PresheafOfModules) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫ e.hom =
    _root_.SheafOfModules.unit X.ringCatSheaf ◁ e.inv ≫
      (ρ_ (_root_.SheafOfModules.unit X.ringCatSheaf)).hom
  rw [schemeSheafification_lax_right_unitality_assoc X (𝟙_ X.PresheafOfModules)]
  change (e.inv ⊗ e.inv) ≫ (ρ_ (𝟙_ X.Modules)).hom ≫ e.hom =
    _root_.SheafOfModules.unit X.ringCatSheaf ◁ e.inv ≫
      (ρ_ (_root_.SheafOfModules.unit X.ringCatSheaf)).hom
  simp only [tensorHom_def', Category.assoc, rightUnitor_naturality_assoc,
    e.inv_hom_id, Category.comp_id]

end KltDP.Geometry
