import KltDP.Geometry.SchemeStructureTensorLeft
import KltDP.Geometry.SchemeModulePullbackTensorMultiplication
import KltDP.Geometry.SchemeModulePullbackSheafificationCounit

/-!
# The original pullback tensor comparison preserves the structure left action

This follows the accepted structure-multiplication argument with an arbitrary
second module. The original presheaf oplax unitality, sheafification unitality,
unit comparison and counit square normalize the same five original factors.
The result applies to the original exceptional ideal inclusion tensored with
an actual canonical sheaf; no tensor compatibility is supplied as a premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance pullbackLeftModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance pullbackLeftPresheaves (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance pullbackLeftSheafification (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

/-- The original structure left action is natural in the actual module. -/
@[reassoc] theorem schemeStructureTensorLeftIso_natural {X : Scheme.{u}}
    {M N : X.Modules} (h : M ⟶ N) :
    _root_.SheafOfModules.unit X.ringCatSheaf ◁ h ≫
        (schemeStructureTensorLeftIso N).hom =
      (schemeStructureTensorLeftIso M).hom ≫ h := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [schemeStructureTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  change _root_.SheafOfModules.unit X.ringCatSheaf ◁ h ≫
      e.inv ▷ N ≫ (λ_ N).hom = e.inv ▷ M ≫ (λ_ M).hom ≫ h
  rw [whisker_exchange_assoc, leftUnitor_naturality]

/-- Sheafification of the literal presheaf left action uses the original counit. -/
@[reassoc] theorem schemeSheafification_structure_left (X : Scheme.{u})
    (P : X.PresheafOfModules) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        (𝟙_ X.PresheafOfModules) P ≫
      MonoidalCategory.whiskerRight (C := X.Modules)
        (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) ≫
      (schemeStructureTensorLeftIso
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).hom =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (λ_ P).hom := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  let Q : X.Modules :=
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P
  simp only [schemeStructureTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  change Functor.OplaxMonoidal.δ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
      (𝟙_ X.PresheafOfModules) P ≫
      e.hom ▷ Q ≫ e.inv ▷ Q ≫ (λ_ Q).hom = _
  rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp,
    schemeSheafification_oplax_left_unitality]

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The original presheaf pullback tensorator satisfies its own left-unit law. -/
@[reassoc] theorem schemeModulePresheafPullbackTensorIso_structure_left
    (M : X.Modules) :
    (schemeModulePresheafPullbackTensorIso f
        (_root_.SheafOfModules.unit X.ringCatSheaf).val M.val).hom ≫
      schemeModulePresheafPullbackUnitHom f ▷
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val) ≫
      (λ_ ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val)).hom =
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).map (λ_ M.val).hom := by
  letI := PresheafOfModules.pullbackOplaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  exact Functor.OplaxMonoidal.left_unitality_hom
    (PresheafOfModules.pullback (PresheafOfModules.schemeRingPresheafHom f)) M.val

/-- The middle original comparison factors preserve the same structure action. -/
@[reassoc] theorem schemeModuleSheafifiedPresheafTensor_structure_left
    (M : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        (schemeModulePresheafPullbackTensorIso f
          (_root_.SheafOfModules.unit X.ringCatSheaf).val M.val).hom ≫
      Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
          (_root_.SheafOfModules.unit X.ringCatSheaf).val)
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val) ≫
      schemeModuleSheafifiedPresheafUnitHom f ▷
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
          ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val)) ≫
      (schemeStructureTensorLeftIso
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
          ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val))).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map (λ_ M.val).hom) := by
  simp only [schemeModuleSheafifiedPresheafUnitHom, comp_whiskerRight, Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_left_assoc]
  let P : Y.PresheafOfModules :=
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val
  have h := schemeSheafification_structure_left Y P
  change Functor.OplaxMonoidal.δ
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
      (_root_.PresheafOfModules.unit Y.ringCatSheaf.val) P ≫
      MonoidalCategory.whiskerRight (C := Y.Modules)
        (PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).hom
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj P) ≫
      (schemeStructureTensorLeftIso
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj P)).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map (λ_ P).hom at h
  rw [h]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  rw [schemeModulePresheafPullbackTensorIso_structure_left]

/-- The same original pullback tensor isomorphism preserves the actual left action. -/
@[reassoc] theorem schemeModulePullbackTensorIso_structure_left (M : X.Modules) :
    (schemeModulePullbackTensorIso f (_root_.SheafOfModules.unit X.ringCatSheaf) M).hom ≫
      ((schemeModulePullbackUnitIso f).hom ⊗ 𝟙 ((schemeModulePullback f).obj M)) ≫
      (schemeStructureTensorLeftIso ((schemeModulePullback f).obj M)).hom =
    (schemeModulePullback f).map (schemeStructureTensorLeftIso M).hom := by
  simp only [schemeModulePullbackTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [← tensor_comp_assoc, Category.comp_id,
    schemeModulePullbackSheafificationIso_inv_unit, tensorHom_def, Category.assoc,
    schemeStructureTensorLeftIso_natural,
    schemeModuleSheafifiedPresheafTensor_structure_left_assoc,
    ← schemeModuleSheafificationCompPullback_natural_assoc,
    schemeModuleSheafificationCompPullback_forgetIso]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  rw [schemeSheafTensorIso_structure_left]

/-- The original inclusion into the structure module retains its actual tensor action. -/
@[reassoc] theorem schemeModulePullbackTensorIso_structure_inclusion
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (M : X.Modules) :
    (schemeModulePullbackTensorIso f I M).hom ≫
      (((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) ⊗
        𝟙 ((schemeModulePullback f).obj M)) ≫
      (schemeStructureTensorLeftIso ((schemeModulePullback f).obj M)).hom =
    (schemeModulePullback f).map
      ((i ⊗ 𝟙 M) ≫ (schemeStructureTensorLeftIso M).hom) := by
  rw [show 𝟙 ((schemeModulePullback f).obj M) =
      (schemeModulePullback f).map (𝟙 M) ≫ 𝟙 _ by simp]
  rw [tensor_comp, Category.assoc, ← schemeModulePullbackTensorIso_natural_assoc,
    schemeModulePullbackTensorIso_structure_left, ← Functor.map_comp]

end KltDP.Geometry
