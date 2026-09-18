import KltDP.Geometry.SchemeStructureTensor

/-!
# The original structure-module action on an arbitrary module sheaf

The left structure action uses the original sheafification counit and
left unitor. The same original monoidal sheafification comparison carries
the literal presheaf action to this action. No new tensor is selected.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureLeftModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance structureLeftPresheaves (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance structureLeftSheafification (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

/-- The left action of the actual structure module, with its original counit. -/
def schemeStructureTensorLeftIso {X : Scheme.{u}} (M : X.Modules) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⊗ M ≅ M :=
  (tensorRight M).mapIso
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).symm ≪≫
    λ_ M

/-- Left unitality for the original sheafification tensorator. -/
@[reassoc] theorem schemeSheafification_lax_left_unitality (X : Scheme.{u})
    (P : X.PresheafOfModules) :
    Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        (𝟙_ X.PresheafOfModules) P ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (λ_ P).hom =
      (λ_ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).hom := by
  simpa only [schemeSheafification_tensorUnit_hom,
    MonoidalCategory.id_whiskerRight, Category.id_comp] using
    (Functor.LaxMonoidal.left_unitality
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P).symm

/-- Left unitality for the inverse of that same original tensorator. -/
@[reassoc] theorem schemeSheafification_oplax_left_unitality (X : Scheme.{u})
    (P : X.PresheafOfModules) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        (𝟙_ X.PresheafOfModules) P ≫
        (λ_ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).hom =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (λ_ P).hom := by
  simpa only [schemeSheafification_tensorUnit_inv,
    MonoidalCategory.id_whiskerRight, Category.id_comp] using
    Functor.OplaxMonoidal.left_unitality_hom
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P

/-- The chosen tensor/sheafification map transports the literal left action. -/
@[reassoc] theorem schemeSheafTensorIso_structure_left (X : Scheme.{u})
    (M : X.Modules) :
    (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
      (_root_.SheafOfModules.unit X.ringCatSheaf) M).hom ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (λ_ M.val).hom ≫
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom =
    (schemeStructureTensorLeftIso M).hom := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  let t := PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M
  simp only [PresheafOfModules.sheafTensorIsoSheafification, Iso.trans_hom,
    tensorIso_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  change (e.inv ⊗ t.inv) ≫
      Functor.LaxMonoidal.μ
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        (𝟙_ X.PresheafOfModules) M.val ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        (λ_ M.val).hom ≫ t.hom =
    e.inv ▷ M ≫ (λ_ M).hom
  rw [schemeSheafification_lax_left_unitality_assoc X M.val]
  simp only [tensorHom_def, Category.assoc, leftUnitor_naturality_assoc,
    t.inv_hom_id, Category.comp_id]

end KltDP.Geometry
