import KltDP.Geometry.SchemeModulePullbackTensorUnit
import KltDP.Geometry.SchemeStructureTensor

/-!
# Multiplication under the original pullback tensor comparison

The original five-factor tensor comparison preserves the literal multiplication
of the structure module after the canonical pullback-unit maps. Consequently it
transports the product of two actual module morphisms into the structure module.
The proof uses the original presheaf oplax unitality, monoidal sheafification,
and the two original adjunction normalizations; it introduces no new functor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- The accepted naturality module declares these monoidal structures as local
-- instances; reactivate the same declarations here instead of redefining them.
-- The accepted tensor instances are local to their module; re-declare them here
-- as local instances with the same bodies (no `attribute` command).
local instance laneMulModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance laneMulPresheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance laneMulSheafificationTensor (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

private theorem oplax_unit_multiplication
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal] :
    Functor.OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C) ≫
        (Functor.OplaxMonoidal.η F ⊗ Functor.OplaxMonoidal.η F) ≫
        (ρ_ (𝟙_ D)).hom =
      F.map (ρ_ (𝟙_ C)).hom ≫ Functor.OplaxMonoidal.η F := by
  simp only [tensorHom_def', Category.assoc, rightUnitor_naturality,
    Functor.OplaxMonoidal.right_unitality_hom_assoc]

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The inverse of the original comparison retains the same canonical unit map. -/
@[reassoc] theorem schemeModulePullbackSheafificationIso_inv_unit :
    (schemeModulePullbackSheafificationIso f
        (_root_.SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (schemeModulePullbackUnitIso f).hom = schemeModuleSheafifiedPresheafUnitHom f := by
  rw [← schemeModulePullbackSheafificationIso_unit, Iso.inv_hom_id_assoc]

/-- The actual presheaf tensor comparison preserves multiplication of its unit,
using its own original oplax unit map. -/
@[reassoc] theorem schemeModulePresheafPullbackTensorIso_unit_mul :
    (schemeModulePresheafPullbackTensorIso f
        (𝟙_ X.PresheafOfModules) (𝟙_ X.PresheafOfModules)).hom ≫
      (schemeModulePresheafPullbackUnitHom f ⊗ schemeModulePresheafPullbackUnitHom f) ≫
      (ρ_ (𝟙_ Y.PresheafOfModules)).hom =
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).map
        (ρ_ (𝟙_ X.PresheafOfModules)).hom ≫
      schemeModulePresheafPullbackUnitHom f := by
  letI := PresheafOfModules.pullbackOplaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  exact oplax_unit_multiplication
    (PresheafOfModules.pullback (PresheafOfModules.schemeRingPresheafHom f))

/-- The accepted sheafified-multiplication identity, restated on the actual presheaf unit
(the object produced by naturality of the sheafification tensorator). -/
@[reassoc] theorem schemeSheafification_structure_mul' (Z : Scheme.{u}) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val))
        (_root_.PresheafOfModules.unit Z.ringCatSheaf.val)
        (_root_.PresheafOfModules.unit Z.ringCatSheaf.val) ≫
      ((PresheafOfModules.sheafTensorUnitIso Z.sheaf.val Z.ringCatSheaf.cond).hom ⊗
        (PresheafOfModules.sheafTensorUnitIso Z.sheaf.val Z.ringCatSheaf.cond).hom) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Z.ringCatSheaf)).hom =
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
        (ρ_ (𝟙_ Z.PresheafOfModules)).hom ≫
      (PresheafOfModules.sheafTensorUnitIso Z.sheaf.val Z.ringCatSheaf.cond).hom :=
  schemeSheafification_structure_mul Z

/-- The middle factors of the chosen tensor comparison preserve multiplication
after the two original sheafified presheaf-unit maps. -/
@[reassoc] theorem schemeModuleSheafifiedPresheafTensor_unit_mul :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        (schemeModulePresheafPullbackTensorIso f
          (𝟙_ X.PresheafOfModules) (𝟙_ X.PresheafOfModules)).hom ≫
      Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
          (𝟙_ X.PresheafOfModules))
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
          (𝟙_ X.PresheafOfModules)) ≫
      (schemeModuleSheafifiedPresheafUnitHom f ⊗ schemeModuleSheafifiedPresheafUnitHom f) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map
          (ρ_ (𝟙_ X.PresheafOfModules)).hom) ≫
      schemeModuleSheafifiedPresheafUnitHom f := by
  simp only [schemeModuleSheafifiedPresheafUnitHom, tensor_comp, Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_assoc, schemeSheafification_structure_mul' Y]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  rw [schemeModulePresheafPullbackTensorIso_unit_mul]

/-- The same identity with the pulled-back objects spelled through the underlying
presheaf of the actual sheaf unit, as produced by unfolding the tensor comparison. -/
@[reassoc] theorem schemeModuleSheafifiedPresheafTensor_unit_mul' :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        (schemeModulePresheafPullbackTensorIso f
          (_root_.SheafOfModules.unit X.ringCatSheaf).val
          (_root_.SheafOfModules.unit X.ringCatSheaf).val).hom ≫
      Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
          (_root_.SheafOfModules.unit X.ringCatSheaf).val)
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
          (_root_.SheafOfModules.unit X.ringCatSheaf).val) ≫
      (schemeModuleSheafifiedPresheafUnitHom f ⊗ schemeModuleSheafifiedPresheafUnitHom f) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map
          (ρ_ (𝟙_ X.PresheafOfModules)).hom) ≫
      schemeModuleSheafifiedPresheafUnitHom f :=
  schemeModuleSheafifiedPresheafTensor_unit_mul f

/-- Naturality of the adjoint comparison on the unit multiplication, with the source
object spelled through the actual sheaf unit and the target through the presheaf unit. -/
@[reassoc] theorem schemeModuleSheafificationCompPullback_natural_unit' :
    (schemeModulePullback f).map
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
          (ρ_ (𝟙_ X.PresheafOfModules)).hom) ≫
        (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
          (_root_.PresheafOfModules.unit X.ringCatSheaf.val) =
      (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
          ((_root_.SheafOfModules.unit X.ringCatSheaf).val ⊗
            (_root_.SheafOfModules.unit X.ringCatSheaf).val) ≫
        (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
          ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map
            (ρ_ (𝟙_ X.PresheafOfModules)).hom) :=
  schemeModuleSheafificationCompPullback_natural f (ρ_ (𝟙_ X.PresheafOfModules)).hom

/-- The already chosen pullback tensor isomorphism preserves the actual
structure-module multiplication under the already chosen pullback-unit isomorphism. -/
@[reassoc] theorem schemeModulePullbackTensorIso_structure_mul :
    (schemeModulePullbackTensorIso f
        (_root_.SheafOfModules.unit X.ringCatSheaf)
        (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      ((schemeModulePullbackUnitIso f).hom ⊗ (schemeModulePullbackUnitIso f).hom) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom =
    (schemeModulePullback f).map
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (schemeModulePullbackUnitIso f).hom := by
  simp only [schemeModulePullbackTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [← tensor_comp_assoc, schemeModulePullbackSheafificationIso_inv_unit,
    schemeModuleSheafifiedPresheafTensor_unit_mul',
    ← schemeModuleSheafificationCompPullback_natural_unit'_assoc,
    schemeModuleSheafificationCompPullback_unit]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  rw [schemeSheafTensorIso_structure_mul]

/-- Pullback of an actual product inclusion is the product of the two actual
pulled morphisms, through the original tensor and unit comparisons. -/
@[reassoc] theorem schemeModulePullbackTensorIso_product
    {M N : X.Modules}
    (g : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (h : N ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (schemeModulePullbackTensorIso f M N).hom ≫
      (((schemeModulePullback f).map g ≫ (schemeModulePullbackUnitIso f).hom) ⊗
        ((schemeModulePullback f).map h ≫ (schemeModulePullbackUnitIso f).hom)) ≫
      (schemeStructureTensorRightIso (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom =
    (schemeModulePullback f).map
      ((g ⊗ h) ≫
        (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom) ≫
      (schemeModulePullbackUnitIso f).hom := by
  rw [tensor_comp, Category.assoc, ← schemeModulePullbackTensorIso_natural_assoc,
    schemeModulePullbackTensorIso_structure_mul, ← Functor.map_comp_assoc]

end KltDP.Geometry
