import KltDP.Geometry.SchemeModulePullbackTensor

/-!
# Naturality of the original scheme-module pullback tensor comparison

The five maps in the already chosen comparison are natural: the actual
sheafification counit, the original adjoint comparison, the original
presheaf pullback tensorator, monoidal sheafification, and the original
pullback/sheafification comparison. Their composite therefore intertwines
the pullback of the original tensor morphism with the tensor of its
original pullbacks. No new tensor or pullback functor is constructed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance sheafificationTensor (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

/-- The original sheafification counit is natural on actual module sheaves. -/
@[reassoc] theorem schemeSheafificationForgetIso_hom_natural {X : Scheme.{u}}
    {M N : X.Modules} (g : M ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map g.val ≫
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf N).hom =
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom ≫ g :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).counit.naturality g

/-- Its inverse uses the same counit and retains the actual underlying morphism. -/
@[reassoc] theorem schemeSheafificationForgetIso_inv_natural {X : Scheme.{u}}
    {M N : X.Modules} (g : M ⟶ N) :
    g ≫ (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf N).inv =
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).inv ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map g.val := by
  apply (cancel_mono
    (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf N).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using
      congrArg (fun h =>
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).inv ≫ h)
        (schemeSheafificationForgetIso_hom_natural g).symm

/-- The original sheaf-tensor comparison preserves both actual module maps. -/
@[reassoc] theorem schemeSheafTensorIsoSheafification_natural {X : Scheme.{u}}
    {M M' N N' : X.Modules} (g : M ⟶ M') (h : N ⟶ N') :
    (g ⊗ h) ≫
        (PresheafOfModules.sheafTensorIsoSheafification
          X.sheaf.val X.ringCatSheaf.cond M' N').hom =
      (PresheafOfModules.sheafTensorIsoSheafification
        X.sheaf.val X.ringCatSheaf.cond M N).hom ≫
          (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (g.val ⊗ h.val) := by
  simp only [PresheafOfModules.sheafTensorIsoSheafification, Iso.trans_hom,
    tensorIso_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom]
  rw [← Category.assoc, ← tensor_comp]
  erw [schemeSheafificationForgetIso_inv_natural (X := X) g,
    schemeSheafificationForgetIso_inv_natural (X := X) h]
  simp only [tensor_comp, Category.assoc]
  erw [Functor.LaxMonoidal.μ_natural
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) g.val h.val]
  rfl

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Naturality of the exact presheaf tensor comparison selected by the original construction. -/
@[reassoc] theorem schemeModulePresheafPullbackTensorIso_natural
    {P P' Q Q' : X.PresheafOfModules} (g : P ⟶ P') (h : Q ⟶ Q') :
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).map (g ⊗ h) ≫
        (schemeModulePresheafPullbackTensorIso f P' Q').hom =
      (schemeModulePresheafPullbackTensorIso f P Q).hom ≫
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map g ⊗
          (PresheafOfModules.pullback (schemeRingSheafHom f).val).map h) := by
  letI := PresheafOfModules.pullbackOplaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  exact (Functor.OplaxMonoidal.δ_natural
    (PresheafOfModules.pullback (PresheafOfModules.schemeRingPresheafHom f)) g h).symm

/-- The exact original adjoint comparison commutes with a presheaf morphism. -/
@[reassoc] theorem schemeModuleSheafificationCompPullback_natural
    {P Q : X.PresheafOfModules} (g : P ⟶ Q) :
    (schemeModulePullback f).map
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map g) ≫
        (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app Q =
      (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app P ≫
        (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
          ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map g) :=
  (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.naturality g

/-- The inverse of the chosen pullback/sheafification comparison preserves actual maps. -/
@[reassoc] theorem schemeModulePullbackSheafificationIso_inv_natural
    {M N : X.Modules} (g : M ⟶ N) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map g.val) ≫
        (schemeModulePullbackSheafificationIso f N).inv =
      (schemeModulePullbackSheafificationIso f M).inv ≫ (schemeModulePullback f).map g :=
  (_root_.SheafOfModules.pullbackIso (schemeRingSheafHom f)).inv.naturality g

/-- The original chosen tensor comparison intertwines the original tensor maps. -/
@[reassoc] theorem schemeModulePullbackTensorIso_natural
    {M M' N N' : X.Modules} (g : M ⟶ M') (h : N ⟶ N') :
    (schemeModulePullback f).map (g ⊗ h) ≫
        (schemeModulePullbackTensorIso f M' N').hom =
      (schemeModulePullbackTensorIso f M N).hom ≫
        ((schemeModulePullback f).map g ⊗ (schemeModulePullback f).map h) := by
  simp only [schemeModulePullbackTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, tensorIso_hom, Functor.Monoidal.μIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, schemeSheafTensorIsoSheafification_natural g h,
    Functor.map_comp, Category.assoc,
    schemeModuleSheafificationCompPullback_natural_assoc f (g.val ⊗ h.val),
    ← Functor.map_comp_assoc,
    schemeModulePresheafPullbackTensorIso_natural f g.val h.val,
    Functor.map_comp, Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural_assoc
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val))
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map g.val)
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).map h.val),
    ← tensor_comp, schemeModulePullbackSheafificationIso_inv_natural f g,
    schemeModulePullbackSheafificationIso_inv_natural f h, tensor_comp]

end KltDP.Geometry
