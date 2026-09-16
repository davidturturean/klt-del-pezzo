import KltDP.Geometry.PrimeCurvePullbackFrameCoordinate

/-!
# The pulled-back trivialization sends the doubly pulled-back frame to `1`

Every comparison isomorphism entering the pulled-back atlas is normalized by an adjunction unit,
so it transports pulled-back sections to pulled-back sections: the composite pullback comparison
(`schemeModulePullbackCompIso`, by `Adjunction.unit_leftAdjointUniq_hom_app`), the equality
comparison (`eqToIso`), and the restriction/pullback comparison (`restrictionIsoPullback`). The
surface chart trivialization sends the frame `1/f_c` to `1`, and the structure-module comparison
sends the pulled-back `1` to `1`. Together these give the core identity `hcore` of
`PrimeCurvePullbackFrameCoordinate`, hence the unconditional Picard-class bridge.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section Composite

variable {X Y Z : Scheme.{u}}

/-- The unit of the composite adjunction (normalized by the pushforward composition comparison)
is the iterated pulled-back section. -/
theorem compAdjunction_unit_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens)
    (s : M.val.obj (op U)) :
    ((((schemeModulePullbackPushforwardAdjunction g).comp
        (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g)).unit.app M).val.app (op U) s =
      pullbackSection f ((schemeModulePullback g).obj M) (g ⁻¹ᵁ U) (pullbackSection g M U s) := rfl

/-- The composite pullback comparison sends the iterated pulled-back section to the pulled-back
section along the composite. -/
theorem schemeModulePullbackCompIso_hom_app_pullbackSection (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : M.val.obj (op U)) :
    ((schemeModulePullbackCompIso f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (pullbackSection f ((schemeModulePullback g).obj M) (g ⁻¹ᵁ U) (pullbackSection g M U s)) =
      pullbackSection (f ≫ g) M U s := by
  have h1 : ((schemeModulePullbackCompIso f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
      (((((schemeModulePullbackPushforwardAdjunction g).comp
        (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
        (schemeModulePushforwardCompIso f g)).unit.app M).val.app (op U) s) =
      pullbackSection (f ≫ g) M U s :=
    congrArg (fun q : M ⟶ (schemeModulePushforward (f ≫ g)).obj
        ((schemeModulePullback (f ≫ g)).obj M) => q.val.app (op U) s)
      (Adjunction.unit_leftAdjointUniq_hom_app
        (((schemeModulePullbackPushforwardAdjunction g).comp
          (schemeModulePullbackPushforwardAdjunction f)).ofNatIsoRight
          (schemeModulePushforwardCompIso f g))
        (schemeModulePullbackPushforwardAdjunction (f ≫ g)) M)
  exact (congrArg (fun y => ((schemeModulePullbackCompIso f g).hom.app M).val.app
    (op ((f ≫ g) ⁻¹ᵁ U)) y) (compAdjunction_unit_app_val_app f g M U s)).symm.trans h1

/-- The inverse composite comparison sends the pulled-back section along the composite to the
iterated pulled-back section. -/
theorem schemeModulePullbackCompIso_inv_app_pullbackSection (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : M.val.obj (op U)) :
    ((schemeModulePullbackCompIso f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (pullbackSection (f ≫ g) M U s) =
      pullbackSection f ((schemeModulePullback g).obj M) (g ⁻¹ᵁ U) (pullbackSection g M U s) := by
  have h2 : ((schemeModulePullbackCompIso f g).inv.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
      (((schemeModulePullbackCompIso f g).hom.app M).val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (pullbackSection f ((schemeModulePullback g).obj M) (g ⁻¹ᵁ U)
          (pullbackSection g M U s))) =
      pullbackSection f ((schemeModulePullback g).obj M) (g ⁻¹ᵁ U) (pullbackSection g M U s) :=
    congrArg (fun q : (schemeModulePullback g ⋙ schemeModulePullback f).obj M ⟶
        (schemeModulePullback g ⋙ schemeModulePullback f).obj M =>
      q.val.app (op ((f ≫ g) ⁻¹ᵁ U))
        (pullbackSection f ((schemeModulePullback g).obj M) (g ⁻¹ᵁ U) (pullbackSection g M U s)))
      ((schemeModulePullbackCompIso f g).hom_inv_id_app M)
  rw [schemeModulePullbackCompIso_hom_app_pullbackSection] at h2
  exact h2

/-- The equality comparison transports pulled-back sections along the induced equality of
preimage opens. -/
theorem eqToIso_pullback_hom_app_pullbackSection {f g : X ⟶ Y} (h : f = g) (M : Y.Modules)
    (U : Y.Opens) (s : M.val.obj (op U)) :
    ((eqToIso (congrArg schemeModulePullback h)).hom.app M).val.app (op (f ⁻¹ᵁ U))
        (pullbackSection f M U s) =
      ((schemeModulePullback g).obj M).val.map
        (eqToHom (congrArg (fun φ : X ⟶ Y => φ ⁻¹ᵁ U) h)).op (pullbackSection g M U s) := by
  subst h
  exact (ConcreteCategory.congr_hom
    (((schemeModulePullback f).obj M).val.presheaf.map_id (op (f ⁻¹ᵁ U)))
    (pullbackSection f M U s)).symm

/-- The inverse restriction/pullback comparison sends a pulled-back section to the restriction of
the section along the (unique) inclusion `f(f⁻¹U) ≤ U`. -/
theorem restrictionIsoPullback_inv_app_pullbackSection (f : Y ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (U : X.Opens) (g : f ''ᵁ f ⁻¹ᵁ U ⟶ U) (s : N.val.obj (op U)) :
    ((SchemeModuleRestriction.restrictionIsoPullback f).inv.app N).val.app (op (f ⁻¹ᵁ U))
        (pullbackSection f N U s) = N.val.map g.op s := by
  have h2 : ((SchemeModuleRestriction.restrictionIsoPullback f).inv.app N).val.app (op (f ⁻¹ᵁ U))
      (((SchemeModuleRestriction.restrictionIsoPullback f).hom.app N).val.app (op (f ⁻¹ᵁ U))
        (((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s)) =
      ((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s :=
    congrArg (fun q : (SchemeModuleRestriction.restriction f).obj N ⟶
        (SchemeModuleRestriction.restriction f).obj N =>
      q.val.app (op (f ⁻¹ᵁ U))
        (((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s))
      ((SchemeModuleRestriction.restrictionIsoPullback f).hom_inv_id_app N)
  rw [restrictionIsoPullback_hom_app_unit] at h2
  exact h2.trans (restrictionAdjunction_unit_app_val_app f N U g s)

/-- The inverse restriction/pullback comparison sends a pulled-back section to the
restriction-adjunction unit of the section. -/
theorem restrictionIsoPullback_inv_app_pullbackSection_unit (f : Y ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (U : X.Opens) (s : N.val.obj (op U)) :
    ((SchemeModuleRestriction.restrictionIsoPullback f).inv.app N).val.app (op (f ⁻¹ᵁ U))
        (pullbackSection f N U s) =
      ((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s := by
  have h2 : ((SchemeModuleRestriction.restrictionIsoPullback f).inv.app N).val.app (op (f ⁻¹ᵁ U))
      (((SchemeModuleRestriction.restrictionIsoPullback f).hom.app N).val.app (op (f ⁻¹ᵁ U))
        (((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s)) =
      ((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s :=
    congrArg (fun q : (SchemeModuleRestriction.restriction f).obj N ⟶
        (SchemeModuleRestriction.restriction f).obj N =>
      q.val.app (op (f ⁻¹ᵁ U))
        (((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s))
      ((SchemeModuleRestriction.restrictionIsoPullback f).hom_inv_id_app N)
  rw [restrictionIsoPullback_hom_app_unit] at h2
  exact h2

/-- Restriction of the structure module preserves `1`. -/
theorem unit_val_map_one (Y : Scheme.{u}) {W W' : Y.Opens} (r : W' ⟶ W) :
    (_root_.SheafOfModules.unit Y.ringCatSheaf).val.map r.op (1 : Γ(Y, W)) = (1 : Γ(Y, W')) :=
  (Y.ringCatSheaf.val.map r.op).hom.map_one

end Composite

section IsoCancellation

variable {X : Scheme.{u}}

/-- Generic: an over-site module isomorphism cancels on sections (`inv ∘ hom`). -/
theorem overModuleIso_inv_app_hom_app {U : X.Opens}
    {A B : _root_.SheafOfModules.{u} (X.ringCatSheaf.over U)} (e : A ≅ B) (V : (Over U)ᵒᵖ)
    (x : A.val.obj V) : e.inv.val.app V (e.hom.val.app V x) = x := by
  have h : ((e.hom ≫ e.inv).val.app V) x = (_root_.SheafOfModules.Hom.val (𝟙 A)).app V x :=
    congrArg (fun q : A ⟶ A => (_root_.SheafOfModules.Hom.val q).app V x) e.hom_inv_id
  exact (overModuleHom_comp_val_app e.hom e.inv V x).symm.trans
    (h.trans (overModuleHom_id_val_app A V x))

/-- Generic: an over-site module isomorphism cancels on sections (`hom ∘ inv`). -/
theorem overModuleIso_hom_app_inv_app {U : X.Opens}
    {A B : _root_.SheafOfModules.{u} (X.ringCatSheaf.over U)} (e : A ≅ B) (V : (Over U)ᵒᵖ)
    (x : B.val.obj V) : e.hom.val.app V (e.inv.val.app V x) = x := by
  have h : ((e.inv ≫ e.hom).val.app V) x = (_root_.SheafOfModules.Hom.val (𝟙 B)).app V x :=
    congrArg (fun q : B ⟶ B => (_root_.SheafOfModules.Hom.val q).app V x) e.inv_hom_id
  exact (overModuleHom_comp_val_app e.inv e.hom V x).symm.trans
    (h.trans (overModuleHom_id_val_app B V x))

/-- Generic: the over-site restriction comparison sends the restriction-adjunction unit of a
section back to the section. -/
theorem openToOverRestrictionIso_hom_app_unit (U : X.Opens) (N : X.Modules) (s : N.val.obj (op U)) :
    (openToOverRestrictionIso U N).hom.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U))))
        (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) = s :=
  (congrArg (fun y => (openToOverRestrictionIso U N).hom.val.app
      (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) y)
    ((restrictionAdjunction_unit_app_val_app U.ι N U
      (eqToHom (openImage_preimage U (Over.mk (homOfLE (le_rfl : U ≤ U))))) s).trans
      (openToOverRestrictionIso_inv_app U N s).symm)).trans
    (overModuleIso_hom_app_inv_app (openToOverRestrictionIso U N)
      (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) s)

end IsoCancellation

section ChartFrame

variable {X : Scheme.{u}} (U : X.Opens) (N : X.Modules)
  (e : _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅ N.over U)

/-- The over-site chart isomorphism underlying a scheme-level chart trivialization built from an
over-site unit trivialization `e`. -/
def chartOverIsoOf :
    (openToOverFunctor U).obj (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
      (openToOverFunctor U).obj ((SchemeModuleRestriction.restriction U.ι).obj N) :=
  (openToOverUnitIso U).symm ≪≫ e ≪≫ (openToOverRestrictionIso U N).symm

/-- The scheme-level chart trivialization built from `e` (the shape of
`cartierChartRestrictionUnitIso`). -/
def chartRestrictionUnitIsoOf :
    _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      (SchemeModuleRestriction.restriction U.ι).obj N :=
  (openToOverFunctor U).preimageIso (chartOverIsoOf U N e)

/-- The same trivialization in the pullback language (the shape of `cartierChartPullbackUnitIso`). -/
def chartPullbackUnitIsoOf :
    (schemeModulePullback U.ι).obj N ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((SchemeModuleRestriction.restrictionIsoPullback U.ι).app N).symm ≪≫
    (chartRestrictionUnitIsoOf U N e).symm

/-- The scheme-level chart trivialization is the preimage of the over-site one. -/
theorem openToOverFunctor_map_chartRestrictionUnitIsoOf_inv :
    (openToOverFunctor U).map (chartRestrictionUnitIsoOf U N e).inv = (chartOverIsoOf U N e).inv :=
  (openToOverFunctor U).map_preimage (chartOverIsoOf U N e).inv

variable (s : N.val.obj (op U))
  (hs : s = e.hom.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U)))

include hs in
/-- The inverse over-site trivialization sends the frame `e.hom 1` to `1`. -/
theorem iso_inv_app_frame : e.inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) s = (1 : Γ(X, U)) :=
  (congrArg (fun y => e.inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) y) hs).trans
    (overModuleIso_inv_app_hom_app e (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U)))

include hs in
/-- The scheme-level chart trivialization, inverted, sends the adjunction-unit image of the frame
to `1`. -/
theorem chartRestrictionUnitIsoOf_inv_app_unit :
    (chartRestrictionUnitIsoOf U N e).inv.val.app (op (U.ι ⁻¹ᵁ U)) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) = (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) := by
  have h1 : (chartRestrictionUnitIsoOf U N e).inv.val.app (op (U.ι ⁻¹ᵁ U)) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) =
      ((openToOverFunctor U).map (chartRestrictionUnitIsoOf U N e).inv).val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) :=
    (openToOverFunctor_map_val_app U (chartRestrictionUnitIsoOf U N e).inv
      (Over.mk (homOfLE (le_rfl : U ≤ U))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s)).symm
  have h2 : ((openToOverFunctor U).map (chartRestrictionUnitIsoOf U N e).inv).val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) =
      (chartOverIsoOf U N e).inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) :=
    congrArg (fun q : ((openToOverFunctor U).obj ((SchemeModuleRestriction.restriction U.ι).obj N)) ⟶ ((openToOverFunctor U).obj (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)) => q.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s))
      (openToOverFunctor_map_chartRestrictionUnitIsoOf_inv U N e)
  have h3 : (chartOverIsoOf U N e).inv = ((openToOverRestrictionIso U N).hom ≫ e.inv) ≫ (openToOverUnitIso U).hom := rfl
  have h4 : (chartOverIsoOf U N e).inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) =
      (((openToOverRestrictionIso U N).hom ≫ e.inv) ≫ (openToOverUnitIso U).hom).val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) :=
    congrArg (fun q : ((openToOverFunctor U).obj ((SchemeModuleRestriction.restriction U.ι).obj N)) ⟶ ((openToOverFunctor U).obj (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)) => q.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s)) h3
  have h5 := overModuleHom_comp_val_app ((openToOverRestrictionIso U N).hom ≫ e.inv) (openToOverUnitIso U).hom (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s)
  have h6 := overModuleHom_comp_val_app (openToOverRestrictionIso U N).hom e.inv (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s)
  have h7 : (openToOverRestrictionIso U N).hom.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (((SchemeModuleRestriction.restrictionAdjunction U.ι).unit.app N).val.app (op U) s) = s := openToOverRestrictionIso_hom_app_unit U N s
  have h8 := iso_inv_app_frame U N e s hs
  have h9 := openToOverUnitIso_hom_app_one U
  exact h1.trans (h2.trans (h4.trans (h5.trans ((congrArg (fun y => (openToOverUnitIso U).hom.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) y)
    (h6.trans ((congrArg (fun y => e.inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) y) h7).trans h8))).trans h9))))

include hs in
/-- The pullback-language chart trivialization sends the pulled-back frame to `1`. -/
theorem chartPullbackUnitIsoOf_hom_app_pullbackSection :
    (chartPullbackUnitIsoOf U N e).hom.val.app (op (U.ι ⁻¹ᵁ U)) (pullbackSection U.ι N U s) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) := by
  have h0 : (chartPullbackUnitIsoOf U N e).hom =
      (SchemeModuleRestriction.restrictionIsoPullback U.ι).inv.app N ≫
        (chartRestrictionUnitIsoOf U N e).inv := rfl
  have h1 := congrArg (fun q : (schemeModulePullback U.ι).obj N ⟶
      _root_.SheafOfModules.unit U.toScheme.ringCatSheaf =>
    q.val.app (op (U.ι ⁻¹ᵁ U)) (pullbackSection U.ι N U s)) h0
  have h2 := schemeModuleHom_comp_val_app
    ((SchemeModuleRestriction.restrictionIsoPullback U.ι).inv.app N)
    (chartRestrictionUnitIsoOf U N e).inv (op (U.ι ⁻¹ᵁ U)) (pullbackSection U.ι N U s)
  have h3 := congrArg (fun y => (chartRestrictionUnitIsoOf U N e).inv.val.app (op (U.ι ⁻¹ᵁ U)) y)
    (restrictionIsoPullback_inv_app_pullbackSection_unit U.ι N U s)
  exact h1.trans (h2.trans (h3.trans (chartRestrictionUnitIsoOf_inv_app_unit U N e s hs)))

end ChartFrame

section CartierChart

variable (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X) (c : CartierEquationChart X D)

/-- The Cartier chart trivialization is the generic one built from `cartierEquationOverIso`. -/
theorem cartierChartPullbackUnitIso_eq :
    cartierChartPullbackUnitIso X D c =
      chartPullbackUnitIsoOf c.openSet (cartierDivisorModule X D)
        (cartierEquationOverIso X D c.openSet c.equation c.represents) := rfl

/-- The frame `1/f_c` is the chart trivialization applied to `1`. -/
theorem cartierFrame_eq_hom_one :
    cartierFrame X D c =
      (cartierEquationOverIso X D c.openSet c.equation c.represents).hom.val.app
        (op (Over.mk (homOfLE (le_rfl : c.openSet ≤ c.openSet)))) (1 : Γ(X, c.openSet)) := rfl

/-- **The pullback-language chart trivialization sends the pulled-back frame to `1`.** -/
theorem cartierChartPullbackUnitIso_hom_app_pullbackSection :
    (cartierChartPullbackUnitIso X D c).hom.val.app (op (c.openSet.ι ⁻¹ᵁ c.openSet))
        (pullbackSection c.openSet.ι (cartierDivisorModule X D) c.openSet (cartierFrame X D c)) =
      (1 : Γ(c.openSet.toScheme, c.openSet.ι ⁻¹ᵁ c.openSet)) :=
  chartPullbackUnitIsoOf_hom_app_pullbackSection c.openSet (cartierDivisorModule X D)
    (cartierEquationOverIso X D c.openSet c.equation c.represents) (cartierFrame X D c)
    (cartierFrame_eq_hom_one X D c)

end CartierChart

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)

/-- The pulled-back trivialization, unfolded. -/
theorem pullbackChartTrivialization_hom (c : C.GenericChart D) :
    (C.pullbackChartTrivialization D c).hom =
      (schemeModulePullbackRestrictObjIso C.inclusion c.1.chart.openSet (cartierDivisorModule X.toScheme D)).hom ≫
        ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom ≫ (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom) := rfl

/-- The pullback–restriction comparison, unfolded. -/
theorem schemeModulePullbackRestrictObjIso_hom (c : C.GenericChart D) :
    (schemeModulePullbackRestrictObjIso C.inclusion c.1.chart.openSet (cartierDivisorModule X.toScheme D)).hom =
      (schemeModulePullbackCompIso (C.chartPreimage D c.1).ι C.inclusion).hom.app (cartierDivisorModule X.toScheme D) ≫ ((eqToIso (congrArg schemeModulePullback (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).hom.app (cartierDivisorModule X.toScheme D) ≫ (schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)) := rfl

/-- The pulled-back frame is the pulled-back section of the frame. -/
theorem pullbackFrame_def (c : C.GenericChart D) :
    C.pullbackFrame D c = pullbackSection C.inclusion (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart) := rfl

set_option maxHeartbeats 1600000 in
/-- The pullback–restriction comparison sends the doubly pulled-back frame to the transported
iterated pulled-back frame of the restricted chart. -/
theorem restrictObjIso_hom_app_pullbackFrame (c : C.GenericChart D) :
    ((schemeModulePullbackRestrictObjIso C.inclusion c.1.chart.openSet (cartierDivisorModule X.toScheme D)).hom).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)) =
      ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D))).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D)) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) := by
  have s1 : ((schemeModulePullbackCompIso (C.chartPreimage D c.1).ι C.inclusion).hom.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)) = pullbackSection ((C.chartPreimage D c.1).ι ≫ C.inclusion) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart) :=
    schemeModulePullbackCompIso_hom_app_pullbackSection (C.chartPreimage D c.1).ι C.inclusion (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)
  have s2 : ((eqToIso (congrArg schemeModulePullback (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).hom.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection ((C.chartPreimage D c.1).ι ≫ C.inclusion) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)) =
      ((schemeModulePullback ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι)).obj (cartierDivisorModule X.toScheme D)).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)) :=
    eqToIso_pullback_hom_app_pullbackSection (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)
  have s3 : ((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (((schemeModulePullback ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι)).obj (cartierDivisorModule X.toScheme D)).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) =
      ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D))).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) :=
    PresheafOfModules.naturality_apply ((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)).val (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))
  have s4 : ((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)) = (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D)) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) :=
    schemeModulePullbackCompIso_inv_app_pullbackSection (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)
  have hR := congrArg (fun q : (schemeModulePullback (C.chartPreimage D c.1).ι).obj ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) ⟶ ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D))) => q.val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)))
    (C.schemeModulePullbackRestrictObjIso_hom D c)
  have hc1 := schemeModuleHom_comp_val_app ((schemeModulePullbackCompIso (C.chartPreimage D c.1).ι C.inclusion).hom.app (cartierDivisorModule X.toScheme D))
    ((eqToIso (congrArg schemeModulePullback (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).hom.app (cartierDivisorModule X.toScheme D) ≫ (schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)) (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c))
  have hc2 := schemeModuleHom_comp_val_app ((eqToIso (congrArg schemeModulePullback (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).hom.app (cartierDivisorModule X.toScheme D)) ((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)) (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet))
    (((schemeModulePullbackCompIso (C.chartPreimage D c.1).ι C.inclusion).hom.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)))
  exact hR.trans (hc1.trans (hc2.trans ((congrArg (fun v => ((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet))
    (((eqToIso (congrArg schemeModulePullback (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).hom.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) v)) s1).trans
    ((congrArg (fun v => ((schemeModulePullbackCompIso (C.inclusion ∣_ c.1.chart.openSet) c.1.chart.openSet.ι).inv.app (cartierDivisorModule X.toScheme D)).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) v) s2).trans
    (s3.trans (congrArg (fun v => ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D))).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op v) s4))))))

set_option maxHeartbeats 1600000 in
/-- **The core identity**: the pulled-back trivialization sends the doubly pulled-back frame to
`1`. -/
theorem pullbackChartTrivialization_pullbackFrame (c : C.GenericChart D) :
    (C.pullbackChartTrivialization D c).hom.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)) = (1 : Γ((C.chartPreimage D c.1).toScheme, (C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) := by
  have hT := congrArg (fun q : (schemeModulePullback (C.chartPreimage D c.1).ι).obj ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) ⟶ (_root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf) =>
    q.val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c))) (C.pullbackChartTrivialization_hom D c)
  have hc1 := schemeModuleHom_comp_val_app (schemeModulePullbackRestrictObjIso C.inclusion c.1.chart.openSet (cartierDivisorModule X.toScheme D)).hom
    ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom ≫ (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom) (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c))
  have hc2 := schemeModuleHom_comp_val_app ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom) (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet))
    ((schemeModulePullbackRestrictObjIso C.inclusion c.1.chart.openSet (cartierDivisorModule X.toScheme D)).hom.val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)))
  have sR := C.restrictObjIso_hom_app_pullbackFrame D c
  have s5 : ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D))).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D)) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)))) =
      ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf)).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom).val.app (op (((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D)) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)))) :=
    PresheafOfModules.naturality_apply ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom).val (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D)) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart)))
  have s6 : ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom).val.app (op (((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) ((schemeModulePullback c.1.chart.openSet.ι).obj (cartierDivisorModule X.toScheme D)) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) =
      pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)
        ((cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom.val.app (op (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) :=
    pullbackSection_map (C.inclusion ∣_ c.1.chart.openSet) (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))
  have s7 : pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)
        ((cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom.val.app (op (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection c.1.chart.openSet.ι (cartierDivisorModule X.toScheme D) c.1.chart.openSet (cartierFrame X.toScheme D c.1.chart))) = (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (1 : Γ(c.1.chart.openSet.toScheme, c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet))) :=
    congrArg (fun v => pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) v)
      (cartierChartPullbackUnitIso_hom_app_pullbackSection X.toScheme D c.1.chart)
  have s8 : (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom.val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) (((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf)).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (1 : Γ(c.1.chart.openSet.toScheme, c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)))) =
      (_root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op ((schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom.val.app (op (((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (1 : Γ(c.1.chart.openSet.toScheme, c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)))) :=
    PresheafOfModules.naturality_apply (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom.val (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (1 : Γ(c.1.chart.openSet.toScheme, c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)))
  have s9 : (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom.val.app (op (((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) (pullbackSection (C.inclusion ∣_ c.1.chart.openSet) (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet) (1 : Γ(c.1.chart.openSet.toScheme, c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet))) = (1 : Γ((C.chartPreimage D c.1).toScheme, ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) :=
    schemeModulePullbackUnitIso_pullbackSection_one (C.inclusion ∣_ c.1.chart.openSet) (c.1.chart.openSet.ι ⁻¹ᵁ c.1.chart.openSet)
  have s10 : (_root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op (1 : Γ((C.chartPreimage D c.1).toScheme, ((C.inclusion ∣_ c.1.chart.openSet) ≫ c.1.chart.openSet.ι) ⁻¹ᵁ c.1.chart.openSet)) = (1 : Γ((C.chartPreimage D c.1).toScheme, ((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) := unit_val_map_one (C.chartPreimage D c.1).toScheme (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm))
  exact hT.trans (hc1.trans (hc2.trans ((congrArg (fun v => (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom.val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet))
    (((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).map (cartierChartPullbackUnitIso X.toScheme D c.1.chart).hom).val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) v)) sR).trans
    ((congrArg (fun v => (schemeModulePullbackUnitIso (C.inclusion ∣_ c.1.chart.openSet)).hom.val.app (op (((C.chartPreimage D c.1).ι ≫ C.inclusion) ⁻¹ᵁ c.1.chart.openSet)) v) (s5.trans
      (congrArg (fun v => ((schemeModulePullback (C.inclusion ∣_ c.1.chart.openSet)).obj (_root_.SheafOfModules.unit c.1.chart.openSet.toScheme.ringCatSheaf)).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op v) (s6.trans s7)))).trans
    (s8.trans ((congrArg (fun v => (_root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf).val.map (eqToHom (congrArg (fun φ : (C.chartPreimage D c.1).toScheme ⟶ X.toScheme => φ ⁻¹ᵁ c.1.chart.openSet) (morphismRestrict_ι C.inclusion c.1.chart.openSet).symm)).op v) s9).trans s10))))))

/-- **The pulled-back frame has chart coordinate `1` in the pulled-back atlas** (`hpull`). -/
theorem chartEquiv_pullbackFrame (c : C.GenericChart D) :
    chartEquiv C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
      (C.pullbackFrame D c) = 1 :=
  C.chartEquiv_pullbackFrame_of_trivialization D hD c
    (C.pullbackChartTrivialization_pullbackFrame D c)

variable (hC : C.NotInSupport D hD)

/-- The pulled-back atlas has the image cocycle. -/
theorem transitionUnits_pullbackLocalTrivializations_eq (c d : C.GenericChart D) :
    transitionUnits C.toScheme _ (C.pullbackLocalTrivializations D hD) c d =
      C.imageCocycle D c d :=
  C.transitionUnits_pullback_of_frames D hD (C.chartEquiv_pullbackFrame D hD) c d

/-- **The Picard-class bridge, unconditional**: `[O_C(D|_C)] = [i^*O_X(D)]`. -/
theorem picardClass_restrict_eq_pullback :
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)).toPic =
      (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)).toPic :=
  C.picardClass_restrict_eq_pullback_of_pullbackFrames D hD hC (C.chartEquiv_pullbackFrame D hD)

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
