import KltDP.Geometry.SchemeModulePullbackTensorNaturality

/-!
# Unit normalization of the original pullback/sheafification comparisons

The original presheaf oplax unit is adjoint to the actual structure map.
Its sheafification therefore gives the already chosen sheaf pullback-unit
map under both original adjoint comparison isomorphisms. The proof uses
only their actual adjunctions and the original sheafification counit.
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
local instance laneModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance lanePresheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance laneSheafificationTensor (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (h : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ h) =
      b.homEquiv M N h := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

/-- The original sheafification counit is adjoint to the identity underlying map. -/
theorem schemeSheafificationForgetIso_homEquiv {X : Scheme.{u}} (M : X.Modules) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv M.val M
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom = 𝟙 M.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).right_triangle_components M

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The original presheaf oplax unit, retained literally as a map of actual presheaves. -/
def schemeModulePresheafPullbackUnitHom :
    (PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
        (_root_.PresheafOfModules.unit X.ringCatSheaf.val) ⟶
      _root_.PresheafOfModules.unit Y.ringCatSheaf.val := by
  letI := PresheafOfModules.pullbackOplaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  exact Functor.OplaxMonoidal.η
    (PresheafOfModules.pullback (PresheafOfModules.schemeRingPresheafHom f))

/-- Its adjunct is the original scheme structural map on underlying module presheaves. -/
theorem schemeModulePresheafPullbackUnitHom_homEquiv :
    (PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).homEquiv _ _
      (schemeModulePresheafPullbackUnitHom f) = (structureToPushforwardUnit f).val := by
  letI := PresheafOfModules.pushforwardFactoredLaxMonoidal
    (PresheafOfModules.schemeRingPresheafHom f)
  change (PresheafOfModules.pullbackPushforwardAdjunction
      (PresheafOfModules.schemeRingPresheafHom f)).homEquiv _ _
    (((PresheafOfModules.pullbackPushforwardFactoredAdjunction
        (PresheafOfModules.schemeRingPresheafHom f)).homEquiv _ _).symm
      (Functor.LaxMonoidal.ε (PresheafOfModules.pushforwardFactored
        (PresheafOfModules.schemeRingPresheafHom f)))) = _
  rw [PresheafOfModules.pullbackPushforwardFactoredAdjunction_eq]
  -- The two adjunctions differ only in the definitional spelling of the pushforward.
  erw [Equiv.apply_symm_apply]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact PresheafOfModules.pushforwardFactored_ε_app_apply
    (PresheafOfModules.schemeRingPresheafHom f) U r

/-- The same adjunct equation, with the target object spelled as the original pushforward
of the unit (the form produced by the composite adjunction normalization). -/
theorem schemeModulePresheafPullbackUnitHom_homEquiv' :
    (PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).homEquiv
      (_root_.PresheafOfModules.unit X.ringCatSheaf.val)
      ((_root_.SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
          (_root_.SheafOfModules.unit Y.ringCatSheaf))
      (schemeModulePresheafPullbackUnitHom f) = (structureToPushforwardUnit f).val :=
  schemeModulePresheafPullbackUnitHom_homEquiv f

/-- The original sheafification counit of the unit is adjoint to the identity, stated on
the actual presheaf unit. -/
theorem schemeSheafificationForgetIso_unit_homEquiv (Z : Scheme.{u}) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.val)).homEquiv
      (_root_.PresheafOfModules.unit Z.ringCatSheaf.val) (_root_.SheafOfModules.unit Z.ringCatSheaf)
      (PresheafOfModules.sheafificationForgetIso Z.ringCatSheaf
        (_root_.SheafOfModules.unit Z.ringCatSheaf)).hom =
      𝟙 (_root_.PresheafOfModules.unit Z.ringCatSheaf.val) :=
  schemeSheafificationForgetIso_homEquiv (_root_.SheafOfModules.unit Z.ringCatSheaf)

/-- The accepted unit normalization, restated for the wrapped scheme adjunction. -/
theorem schemeModulePullbackUnitHom_adjunction' :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv _ _ (schemeModulePullbackUnitHom f) =
      structureToPushforwardUnit f :=
  schemeModulePullbackUnitHom_adjunction f

/-- Sheafify that exact presheaf unit map and use the original structure-module counit. -/
def schemeModuleSheafifiedPresheafUnitHom :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
        (_root_.PresheafOfModules.unit X.ringCatSheaf.val)) ⟶
      _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
      (schemeModulePresheafPullbackUnitHom f) ≫
    (PresheafOfModules.sheafTensorUnitIso Y.sheaf.val Y.ringCatSheaf.cond).hom

/-- Under the original sheafification adjunction the same map is the presheaf unit. -/
theorem schemeModuleSheafifiedPresheafUnitHom_homEquiv :
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).homEquiv _ _
      (schemeModuleSheafifiedPresheafUnitHom f) = schemeModulePresheafPullbackUnitHom f := by
  rw [schemeModuleSheafifiedPresheafUnitHom, Adjunction.homEquiv_naturality_left]
  change schemeModulePresheafPullbackUnitHom f ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).homEquiv _ _
      (PresheafOfModules.sheafificationForgetIso Y.ringCatSheaf
        (_root_.SheafOfModules.unit Y.ringCatSheaf)).hom = _
  rw [schemeSheafificationForgetIso_unit_homEquiv, Category.comp_id]

/-- Normalize the actual pullback/sheafification comparison under the original two adjunctions. -/
theorem schemeModulePullbackSheafificationIso_homEquiv (M : X.Modules) (N : Y.Modules)
    (a : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val) ⟶ N) :
    ((schemeModulePullbackPushforwardAdjunction f).homEquiv M N
      ((schemeModulePullbackSheafificationIso f M).hom ≫ a)).val =
    (PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).homEquiv _ _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).homEquiv _ _ a) := by
  have h := homEquiv_leftAdjointUniq_comp
    (_root_.SheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f))
    (_root_.SheafOfModules.PullbackConstruction.adjunction (schemeRingSheafHom f)) M N a
  change ((schemeModulePullbackPushforwardAdjunction f).homEquiv M N
      ((schemeModulePullbackSheafificationIso f M).hom ≫ a)) =
    (_root_.SheafOfModules.PullbackConstruction.adjunction (schemeRingSheafHom f)).homEquiv M N a at h
  rw [h]
  rw [_root_.SheafOfModules.PullbackConstruction.adjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Normalize the other original comparison under the actual composite adjunctions. -/
theorem schemeModuleSheafificationCompPullback_homEquiv
    (P : X.PresheafOfModules) (N : Y.Modules)
    (a : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P) ⟶ N) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _
        ((_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app P ≫ a)) =
    (PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).homEquiv _ _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).homEquiv _ _ a) := by
  have h := homEquiv_leftAdjointUniq_comp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).comp
      (_root_.SheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f)))
    ((PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val))) P N a
  simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply] using h

/-- The sheafified unit adjunct, with the pulled-back object spelled through the
underlying presheaf of the actual sheaf unit. -/
theorem schemeModuleSheafifiedPresheafUnitHom_homEquiv' :
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).homEquiv
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj
        (_root_.SheafOfModules.unit X.ringCatSheaf).val)
      (_root_.SheafOfModules.unit Y.ringCatSheaf)
      (schemeModuleSheafifiedPresheafUnitHom f) = schemeModulePresheafPullbackUnitHom f :=
  schemeModuleSheafifiedPresheafUnitHom_homEquiv f

/-- The presheaf unit adjunct, spelled on the underlying presheaves of the actual sheaf
units and the forgotten structural map. -/
theorem schemeModulePresheafPullbackUnitHom_homEquiv'' :
    (PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val).homEquiv
      (_root_.SheafOfModules.unit X.ringCatSheaf).val
      ((_root_.SheafOfModules.forget Y.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.val)).obj
          (_root_.SheafOfModules.unit Y.ringCatSheaf))
      (schemeModulePresheafPullbackUnitHom f) =
      (_root_.SheafOfModules.forget X.ringCatSheaf).map (structureToPushforwardUnit f) :=
  schemeModulePresheafPullbackUnitHom_homEquiv f

/-- The first original comparison identifies the sheafified presheaf unit with
exactly the canonical original sheaf pullback unit. -/
@[reassoc] theorem schemeModulePullbackSheafificationIso_unit :
    (schemeModulePullbackSheafificationIso f
        (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      schemeModuleSheafifiedPresheafUnitHom f = (schemeModulePullbackUnitIso f).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [show (schemeModulePullbackUnitIso f).hom = schemeModulePullbackUnitHom f from rfl,
    schemeModulePullbackUnitHom_adjunction']
  apply (_root_.SheafOfModules.forget X.ringCatSheaf).map_injective
  change ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _
    ((schemeModulePullbackSheafificationIso f
      (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      schemeModuleSheafifiedPresheafUnitHom f)).val = _
  rw [schemeModulePullbackSheafificationIso_homEquiv,
    schemeModuleSheafifiedPresheafUnitHom_homEquiv',
    schemeModulePresheafPullbackUnitHom_homEquiv'']

/-- The second original comparison has the same canonical normalization through
sheafification of the original presheaf unit. -/
@[reassoc] theorem schemeModuleSheafificationCompPullback_unit :
    (_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app
        (_root_.PresheafOfModules.unit X.ringCatSheaf.val) ≫
      schemeModuleSheafifiedPresheafUnitHom f =
    (schemeModulePullback f).map
      (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom ≫
        (schemeModulePullbackUnitIso f).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).homEquiv _ _).injective
  rw [schemeModuleSheafificationCompPullback_homEquiv,
    schemeModuleSheafifiedPresheafUnitHom_homEquiv,
    schemeModulePresheafPullbackUnitHom_homEquiv',
    Adjunction.homEquiv_naturality_left]
  rw [show (schemeModulePullbackUnitIso f).hom = schemeModulePullbackUnitHom f from rfl]
  -- The unit object appears here through the unfolded ring sheaf of `X`.
  erw [schemeModulePullbackUnitHom_adjunction' f]
  rw [Adjunction.homEquiv_naturality_right]
  change (structureToPushforwardUnit f).val =
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).homEquiv _ _
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
        (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫ (structureToPushforwardUnit f).val
  rw [schemeSheafificationForgetIso_homEquiv, Category.id_comp]

end KltDP.Geometry
