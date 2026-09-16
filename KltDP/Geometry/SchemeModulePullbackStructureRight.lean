import KltDP.Geometry.SchemeModulePullbackTensorMultiplication
import KltDP.Geometry.SchemeModuleTensorScalar

/-!
# The original pullback comparison preserves the module right unit

For an arbitrary actual coefficient module, the already chosen five-factor
pullback tensor comparison commutes with tensoring by the structure module
and the original structure-module right unitor. The proof extends the
accepted structure-module multiplication calculation using the original
adjunctions and their actual sheafification counits.

No monoidal structure on the sheaf pullback is assumed or replaced. This is
the transport identity needed to compare actual tensor twists on open charts;
global extension for a nontrivial invertible sheaf is a separate consumer.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.SchemeModulePullbackStructureRight

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance sheafificationTensor (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

private theorem tensorUnitIso_right
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B O : C} (e : 𝟙_ C ≅ O) (a : A ⟶ B) :
    (a ⊗ e.hom) ≫ (B ◁ e.inv ≫ (ρ_ B).hom) = (ρ_ A).hom ≫ a := by
  rw [tensorHom_def, Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    e.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    rightUnitor_naturality]

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

set_option maxHeartbeats 800000 in
/-- The two original adjoint comparisons agree through the actual
sheafification counit of every module, not only of the structure module. -/
@[reassoc] theorem sheafificationCompPullback_counit (M : X.Modules) :
    (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
        M.val ≫ (schemeModulePullbackSheafificationIso f M).inv =
      (schemeModulePullback f).map
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom := by
  have hC :
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv M
        ((schemeModulePullback f).obj M) (𝟙 _)).val =
      (PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).homEquiv
        _ _ ((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y.ringCatSheaf.val)).homEquiv _ _
            (schemeModulePullbackSheafificationIso f M).inv) := by
    simpa only [Iso.hom_inv_id] using
      schemeModulePullbackSheafificationIso_homEquiv f M
        ((schemeModulePullback f).obj M) (schemeModulePullbackSheafificationIso f M).inv
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).homEquiv _ _).injective
  rw [schemeModuleSheafificationCompPullback_homEquiv, ← hC]
  change ((schemeModulePullbackPushforwardAdjunction f).homEquiv M
      ((schemeModulePullback f).obj M) (𝟙 _)).val =
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _
        ((schemeModulePullback f).map
          (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom ≫ 𝟙 _))
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change _ =
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv M.val M
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom ≫
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv M
        ((schemeModulePullback f).obj M) (𝟙 _)).val
  rw [schemeSheafificationForgetIso_homEquiv, Category.id_comp]

/-- The original presheaf tensor comparison obeys its proved right-unit law. -/
@[reassoc] theorem presheafPullbackTensor_right (P : X.PresheafOfModules) :
    (schemeModulePresheafPullbackTensorIso f P (𝟙_ X.PresheafOfModules)).hom ≫
      (𝟙 ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P) ⊗
        schemeModulePresheafPullbackUnitHom f) ≫
      (ρ_ ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P)).hom =
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).map (ρ_ P).hom := by
  letI := PresheafOfModules.pullbackOplaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  simpa only [id_tensorHom] using
    Functor.OplaxMonoidal.right_unitality_hom
      (PresheafOfModules.pullback (PresheafOfModules.schemeRingPresheafHom f)) P

private theorem sheafification_structure_right (P : Y.PresheafOfModules)
    (N : Y.Modules)
    (a : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj P ⟶ N) :
    Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
        P (_root_.PresheafOfModules.unit Y.ringCatSheaf.val) ≫
      (a ⊗ (PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).hom) ≫
      (schemeStructureTensorRightIso N).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map (ρ_ P).hom ≫ a := by
  let e : 𝟙_ Y.Modules ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond
  rw [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change Functor.OplaxMonoidal.δ
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
      P (_root_.PresheafOfModules.unit Y.ringCatSheaf.val) ≫
      (a ⊗ e.hom) ≫ (N ◁ e.inv ≫ (ρ_ N).hom) = _
  rw [tensorUnitIso_right e a]
  exact schemeSheafification_oplax_right_unitality_assoc Y P a

set_option maxHeartbeats 800000 in
private theorem sheafifiedPresheafTensor_right (P : X.PresheafOfModules)
    (N : Y.Modules)
    (a : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P) ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        (schemeModulePresheafPullbackTensorIso f P (_root_.SheafOfModules.unit X.ringCatSheaf).val).hom ≫
      Functor.OplaxMonoidal.δ (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P)
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
          (_root_.SheafOfModules.unit X.ringCatSheaf).val) ≫
      (a ⊗ schemeModuleSheafifiedPresheafUnitHom f) ≫
      (schemeStructureTensorRightIso N).hom =
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map (ρ_ P).hom) ≫ a := by
  let S := PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)
  let Q := (PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P
  have h : (a ⊗ schemeModuleSheafifiedPresheafUnitHom f) =
      (S.map (𝟙 Q) ⊗ S.map (schemeModulePresheafPullbackUnitHom f)) ≫
        (a ⊗ (PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).hom) := by
    rw [← tensor_comp, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [h, Category.assoc, Functor.OplaxMonoidal.δ_natural_assoc,
    sheafification_structure_right (Y := Y) Q N a]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  exact congrArg (fun g => S.map g ≫ a) (presheafPullbackTensor_right f P)

private theorem sheafificationCompPullback_natural_structure_right (M : X.Modules) :
    (schemeModulePullback f).map
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
          (ρ_ M.val).hom) ≫
        (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
          M.val ≫ (schemeModulePullbackSheafificationIso f M).inv =
      (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
          (M.val ⊗ (_root_.SheafOfModules.unit X.ringCatSheaf).val) ≫
        (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
          ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map (ρ_ M.val).hom) ≫
        (schemeModulePullbackSheafificationIso f M).inv := by
  simpa only [Category.assoc] using
    congrArg (fun g => g ≫ (schemeModulePullbackSheafificationIso f M).inv)
      (schemeModuleSheafificationCompPullback_natural f (ρ_ M.val).hom)

set_option maxHeartbeats 800000 in
/-- The original pullback tensor comparison preserves the structure-module
right unitor for every actual coefficient module. -/
@[reassoc] theorem pullbackTensor_structure_right (M : X.Modules) :
    (schemeModulePullbackTensorIso f M (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (𝟙 ((schemeModulePullback f).obj M) ⊗ (schemeModulePullbackUnitIso f).hom) ≫
      (schemeStructureTensorRightIso ((schemeModulePullback f).obj M)).hom =
    (schemeModulePullback f).map (schemeStructureTensorRightIso M).hom := by
  simp only [schemeModulePullbackTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [← tensor_comp_assoc, Category.comp_id,
    schemeModulePullbackSheafificationIso_inv_unit,
    sheafifiedPresheafTensor_right f M.val ((schemeModulePullback f).obj M)
      (schemeModulePullbackSheafificationIso f M).inv,
    ← sheafificationCompPullback_natural_structure_right f M,
    sheafificationCompPullback_counit]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc]
  rw [SchemeModuleTensorScalar.sheafTensorIso_structure_right]

end KltDP.Geometry.SchemeModulePullbackStructureRight
