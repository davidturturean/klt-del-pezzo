import KltDP.Geometry.PrimeCurveRestrictedFrameCoordinate

/-!
# The pulled-back frames have chart coordinate `1`

The pulled-back atlas of `i^*O_X(D)` on the chart preimages `i⁻¹U_c` is assembled from the
accepted chart trivializations of `O_X(D)` through the pullback/restriction comparisons. Its
chart coordinate of the pulled-back frame `i^*(1/f_c)` is `1`: pulled-back sections are
transported by every comparison isomorphism (they are all normalized by the adjunction units),
the surface trivialization sends `1/f_c` to `1`, and the structure-module comparison sends the
pulled-back `1` to `1`.

This module proves the generic section-level lemmas and the *reduction*
`chartEquiv_pullbackFrame_of_trivialization : hcore → hpull`, where `hcore` says that the
pullback-language trivialization sends the doubly pulled-back frame to `1`; `hcore` itself and the
unconditional Picard-class bridge are proved in `PrimeCurvePullbackFrameCore`.

As in `PrimeCurveRestrictedFrameCoordinate`, the tactic-built isomorphisms are wrapped in
constants and every step is a `congrArg` or a generic identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section SectionLemmas

variable {X Y : Scheme.{u}}

/-- Generic: evaluating a composite of module-sheaf morphisms on a section. -/
theorem schemeModuleHom_comp_val_app {A B E : Y.Modules} (a : A ⟶ B) (b : B ⟶ E)
    (V : Y.Opensᵒᵖ) (x : A.val.obj V) :
    (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := rfl

/-- Generic: evaluating the identity morphism on a section. -/
theorem schemeModuleHom_id_val_app (A : Y.Modules) (V : Y.Opensᵒᵖ) (x : A.val.obj V) :
    (_root_.SheafOfModules.Hom.val (𝟙 A)).app V x = x := rfl

/-- Pulled-back sections are natural in the module: the unit of the adjunction. -/
theorem pullbackSection_map (f : Y ⟶ X) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (s : M.val.obj (op U)) :
    ((schemeModulePullback f).map φ).val.app (op (f ⁻¹ᵁ U)) (pullbackSection f M U s) =
      pullbackSection f N U (φ.val.app (op U) s) :=
  (congrArg
    (fun g : M ⟶ (schemeModulePushforward f).obj ((schemeModulePullback f).obj N) =>
      g.val.app (op U) s)
    ((schemeModulePullbackPushforwardAdjunction f).unit.naturality φ)).symm

/-- The structure-module comparison sends the pulled-back `1` to `1`. -/
theorem schemeModulePullbackUnitIso_pullbackSection_one (f : Y ⟶ X) (U : X.Opens) :
    (schemeModulePullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ U))
        (pullbackSection f (_root_.SheafOfModules.unit X.ringCatSheaf) U (1 : Γ(X, U))) =
      (1 : Γ(Y, f ⁻¹ᵁ U)) := by
  have h : (schemeModulePullbackPushforwardAdjunction f).unit.app
        (_root_.SheafOfModules.unit X.ringCatSheaf) ≫
      (schemeModulePushforward f).map (schemeModulePullbackUnitHom f) =
        structureToPushforwardUnit f :=
    (Adjunction.homEquiv_unit (adj := schemeModulePullbackPushforwardAdjunction f)
      (f := schemeModulePullbackUnitHom f)).symm.trans (schemeModuleUnit_homEquiv f)
  have h1 : (schemeModulePullbackUnitHom f).val.app (op (f ⁻¹ᵁ U))
        (pullbackSection f (_root_.SheafOfModules.unit X.ringCatSheaf) U (1 : Γ(X, U))) =
      (structureToPushforwardUnit f).val.app (op U) (1 : Γ(X, U)) :=
    congrArg
      (fun g : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
          (schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) =>
        g.val.app (op U) (1 : Γ(X, U))) h
  exact h1.trans ((structureToPushforwardUnit_app f U (1 : Γ(X, U))).trans
    (f.app U).hom.map_one)

/-- The restriction/pullback comparison sends the restriction-adjunction unit of a section to
its pulled-back section. -/
theorem restrictionIsoPullback_hom_app_unit (f : Y ⟶ X) [IsOpenImmersion f] (N : X.Modules)
    (U : X.Opens) (s : N.val.obj (op U)) :
    ((SchemeModuleRestriction.restrictionIsoPullback f).hom.app N).val.app (op (f ⁻¹ᵁ U))
        (((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s) =
      pullbackSection f N U s :=
  congrArg
    (fun g : N ⟶ (schemeModulePushforward f).obj ((schemeModulePullback f).obj N) =>
      g.val.app (op U) s)
    (Adjunction.unit_leftAdjointUniq_hom_app (SchemeModuleRestriction.restrictionAdjunction f)
      (schemeModulePullbackPushforwardAdjunction f) N)

/-- The restriction-adjunction unit restricts along the (unique) inclusion
`f(f⁻¹U) ≤ U`. -/
theorem restrictionAdjunction_unit_app_val_app_counit (f : Y ⟶ X) [IsOpenImmersion f]
    (N : X.Modules) (U : X.Opens) (s : N.val.obj (op U)) :
    ((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s =
      N.val.map (f.isOpenEmbedding.isOpenMap.adjunction.counit.app U).op s := rfl

/-- The restriction-adjunction unit restricts along any morphism `f(f⁻¹U) ⟶ U` (they are all
equal). -/
theorem restrictionAdjunction_unit_app_val_app (f : Y ⟶ X) [IsOpenImmersion f] (N : X.Modules)
    (U : X.Opens) (g : f ''ᵁ f ⁻¹ᵁ U ⟶ U) (s : N.val.obj (op U)) :
    ((SchemeModuleRestriction.restrictionAdjunction f).unit.app N).val.app (op U) s =
      N.val.map g.op s :=
  (restrictionAdjunction_unit_app_val_app_counit f N U s).trans
    (congrArg (fun g' : f ''ᵁ f ⁻¹ᵁ U ⟶ U => N.val.map g'.op s) (Subsingleton.elim _ g))

/-- Generic: evaluating a composite of over-site module morphisms on a section. -/
theorem overModuleHom_comp_val_app {U : X.Opens}
    {A B E : _root_.SheafOfModules.{u} (X.ringCatSheaf.over U)} (a : A ⟶ B) (b : B ⟶ E)
    (V : (Over U)ᵒᵖ) (x : A.val.obj V) :
    (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := rfl

/-- Generic: evaluating the identity over-site module morphism on a section. -/
theorem overModuleHom_id_val_app {U : X.Opens}
    (A : _root_.SheafOfModules.{u} (X.ringCatSheaf.over U)) (V : (Over U)ᵒᵖ)
    (x : A.val.obj V) : (_root_.SheafOfModules.Hom.val (𝟙 A)).app V x = x := rfl

/-- The over-site unit comparison on the top object is the structure map of the open; it sends
`1` to `1`. -/
theorem openToOverUnitIso_hom_app_one (U : X.Opens) :
    (openToOverUnitIso U).hom.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U)) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) :=
  (U.ι.app U).hom.map_one

/-- The inverse over-site unit comparison on the top object sends `1` to `1`. -/
theorem openToOverUnitIso_inv_app_one (U : X.Opens) :
    (openToOverUnitIso U).inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U))))
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) = (1 : Γ(X, U)) := by
  have h1 : (openToOverUnitIso U).inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U))))
        ((openToOverUnitIso U).hom.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U))))
          (1 : Γ(X, U))) =
      (openToOverUnitIso U).inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U))))
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)) :=
    congrArg (fun y => (openToOverUnitIso U).inv.val.app
      (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) y) (openToOverUnitIso_hom_app_one U)
  have h2 : ((openToOverUnitIso U).hom ≫ (openToOverUnitIso U).inv).val.app
        (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U)) =
      (_root_.SheafOfModules.Hom.val (𝟙 (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)))).app
        (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U)) :=
    congrArg (fun g : _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
        _root_.SheafOfModules.unit (X.ringCatSheaf.over U) =>
      (_root_.SheafOfModules.Hom.val g).app (op (Over.mk (homOfLE (le_rfl : U ≤ U))))
        (1 : Γ(X, U))) (openToOverUnitIso U).hom_inv_id
  exact h1.symm.trans ((overModuleHom_comp_val_app (openToOverUnitIso U).hom
    (openToOverUnitIso U).inv (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U))).symm.trans
    (h2.trans (overModuleHom_id_val_app (_root_.SheafOfModules.unit (X.ringCatSheaf.over U))
      (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) (1 : Γ(X, U)))))

/-- The over-site restriction comparison on the top object is the module restriction along
the equality `U.ι(U.ι⁻¹U) = U`. -/
theorem openToOverRestrictionIso_inv_app (U : X.Opens) (N : X.Modules)
    (s : (N.over U).val.obj (op (Over.mk (homOfLE (le_rfl : U ≤ U))))) :
    (openToOverRestrictionIso U N).inv.val.app (op (Over.mk (homOfLE (le_rfl : U ≤ U)))) s =
      N.val.map (eqToHom (openImage_preimage U (Over.mk (homOfLE (le_rfl : U ≤ U))))).op s := rfl

/-- Evaluating a pushed-forward morphism on the over site. -/
theorem openToOverFunctor_map_val_app (U : X.Opens) {A B : U.toScheme.Modules} (φ : A ⟶ B)
    (V : Over U) (x : ((openToOverFunctor U).obj A).val.obj (op V)) :
    ((openToOverFunctor U).map φ).val.app (op V) x =
      φ.val.app (op (U.overEquivalence.functor.obj V)) x := rfl

/-- The top object of the over site is the whole open. -/
theorem overEquivalence_functor_obj_top (U : X.Opens) :
    U.overEquivalence.functor.obj (Over.mk (homOfLE (le_rfl : U ≤ U))) = U.ι ⁻¹ᵁ U := rfl

/-- Generic: the unit trivialization built from a chart isomorphism `F ≪≫ O` (free-singleton
comparison followed by a unit trivialization) evaluates to the inverse of `O`. -/
theorem trans_symm_trans_hom_val_app {U : X.Opens} {M : X.Modules}
    (F : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (O : _root_.SheafOfModules.unit (X.ringCatSheaf.over U) ≅ M.over U) (V : (Over U)ᵒᵖ)
    (s : (M.over U).val.obj V) :
    ((F ≪≫ O).symm ≪≫ F).hom.val.app V s = O.inv.val.app V s := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end SectionLemmas

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)

/-- The pulled-back chart trivialization of `i^*O_X(D)` on a chart preimage, as a constant. -/
def pullbackChartUnitIso (c : C.GenericChart D) :
    _root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf ≅
      (SchemeModuleRestriction.restriction (C.chartPreimage D c.1).ι).obj
        ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) :=
  pullbackCartierChartUnitIso X.toScheme D C.inclusion c.1.chart

/-- The pulled-back trivialization read on the over site, as a constant. -/
def pullbackChartIso (c : C.GenericChart D) :
    _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) ≅
      ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).over
        (C.chartPreimage D c.1) :=
  openChartToOverUnitIso (C.chartPreimage D c.1)
    ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))
    (C.pullbackChartUnitIso D c)

/-- The pulled-back trivialization in the pullback language, as a constant. -/
def pullbackChartTrivialization (c : C.GenericChart D) :
    (schemeModulePullback (C.chartPreimage D c.1).ι).obj
        ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) ≅
      _root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf :=
  schemeModulePullbackTrivialization C.inclusion c.1.chart.openSet
    (cartierDivisorModule X.toScheme D) (cartierChartPullbackUnitIso X.toScheme D c.1.chart)

/-- The chart isomorphism of the pulled-back atlas, with its type reduced to the chart preimage. -/
def pullbackAtlasIso (c : C.GenericChart D) :
    _root_.SheafOfModules.free (R := C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) PUnit ≅ ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).over (C.chartPreimage D c.1) :=
  (C.pullbackLocalTrivializations D hD).iso c

/-- The chart isomorphism of the pulled-back atlas. -/
theorem pullbackAtlasIso_eq (c : C.GenericChart D) :
    C.pullbackAtlasIso D hD c = C.restrictedFreeIso D c ≪≫ C.pullbackChartIso D c := rfl

/-- Its inverse. -/
theorem pullbackAtlasIso_inv (c : C.GenericChart D) :
    (C.pullbackAtlasIso D hD c).inv =
      (C.pullbackChartIso D c).inv ≫ (C.restrictedFreeIso D c).inv := rfl

/-- The unit trivialization of the pulled-back atlas, unfolded. -/
theorem pullbackLocalTrivializations_unitIso_hom (c : C.GenericChart D) :
    ((C.pullbackLocalTrivializations D hD).unitIso c).hom =
      (C.pullbackAtlasIso D hD c).inv ≫ (C.restrictedFreeIso D c).hom := rfl

/-- The pulled-back chart trivialization unfolds to the pullback-language trivialization
composed with the restriction/pullback comparison. -/
theorem pullbackChartUnitIso_inv (c : C.GenericChart D) :
    (C.pullbackChartUnitIso D c).inv =
      (SchemeModuleRestriction.restrictionIsoPullback (C.chartPreimage D c.1).ι).hom.app ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) ≫
        (C.pullbackChartTrivialization D c).hom := rfl

/-- Evaluation of the unit trivialization of the pulled-back atlas at the chart: it is the inverse
of the pulled-back chart trivialization on the over site. -/
theorem pullbackLocalTrivializations_unitIso_hom_app (c : C.GenericChart D)
    (s : ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).val.obj (op (C.chartPreimage D c.1))) :
    ((C.pullbackLocalTrivializations D hD).unitIso c).hom.val.app (C.restrictedChartTop D c) s =
      (C.pullbackChartIso D c).inv.val.app (C.restrictedChartTop D c) s :=
  trans_symm_trans_hom_val_app (C.restrictedFreeIso D c) (C.pullbackChartIso D c) (C.restrictedChartTop D c) s

/-- The over-site trivialization unfolds on the top object: transport to the open subscheme,
the pulled-back chart trivialization, and the unit comparison. -/
theorem pullbackChartIso_inv_app (c : C.GenericChart D)
    (s : ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).val.obj (op (C.chartPreimage D c.1))) :
    (C.pullbackChartIso D c).inv.val.app (C.restrictedChartTop D c) s =
      (openToOverUnitIso (C.chartPreimage D c.1)).inv.val.app (C.restrictedChartTop D c)
        ((C.pullbackChartUnitIso D c).inv.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))
          ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) s)) := by
  have h1 : (C.pullbackChartIso D c).inv.val.app (C.restrictedChartTop D c) s =
      (((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c) ≪≫
          openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv ≫
        (openToOverUnitIso (C.chartPreimage D c.1)).inv).val.app (C.restrictedChartTop D c) s :=
    congrArg (fun g : ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).over (C.chartPreimage D c.1) ⟶
        _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) => g.val.app (C.restrictedChartTop D c) s)
      (Iso.trans_inv (openToOverUnitIso (C.chartPreimage D c.1))
        ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c) ≪≫
          openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))))
  have h2 : (((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c) ≪≫
          openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv ≫
        (openToOverUnitIso (C.chartPreimage D c.1)).inv).val.app (C.restrictedChartTop D c) s =
      (openToOverUnitIso (C.chartPreimage D c.1)).inv.val.app (C.restrictedChartTop D c)
        (((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c) ≪≫
          openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) s) :=
    overModuleHom_comp_val_app ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c) ≪≫
          openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv (openToOverUnitIso (C.chartPreimage D c.1)).inv (C.restrictedChartTop D c) s
  have h3 : ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c) ≪≫
          openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) s =
      ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv ≫
        ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c)).inv).val.app (C.restrictedChartTop D c) s :=
    congrArg (fun g : ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)).over (C.chartPreimage D c.1) ⟶
        (openToOverFunctor (C.chartPreimage D c.1)).obj
          (_root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf) => g.val.app (C.restrictedChartTop D c) s)
      (Iso.trans_inv ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c))
        (openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))))
  have h4 : ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv ≫
        ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c)).inv).val.app (C.restrictedChartTop D c) s =
      ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c)).inv.val.app (C.restrictedChartTop D c)
        ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) s) :=
    overModuleHom_comp_val_app (openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv
      ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c)).inv (C.restrictedChartTop D c) s
  have h5 : ((openToOverFunctor (C.chartPreimage D c.1)).mapIso (C.pullbackChartUnitIso D c)).inv.val.app (C.restrictedChartTop D c)
        ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) s) =
      (C.pullbackChartUnitIso D c).inv.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))
        ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) s) := rfl
  exact h1.trans (h2.trans (congrArg (fun y => (openToOverUnitIso (C.chartPreimage D c.1)).inv.val.app (C.restrictedChartTop D c) y)
    (h3.trans (h4.trans h5))))

/-- Evaluation of the inverse pulled-back chart trivialization on a section of the restricted
pullback. -/
theorem pullbackChartUnitIso_inv_val_app (c : C.GenericChart D)
    (x : ((SchemeModuleRestriction.restriction (C.chartPreimage D c.1).ι).obj ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).val.obj (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))) :
    (C.pullbackChartUnitIso D c).inv.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) x =
      (C.pullbackChartTrivialization D c).hom.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))
        (((SchemeModuleRestriction.restrictionIsoPullback (C.chartPreimage D c.1).ι).hom.app ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) x) :=
  (congrArg (fun g : (SchemeModuleRestriction.restriction (C.chartPreimage D c.1).ι).obj ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) ⟶
      _root_.SheafOfModules.unit (C.chartPreimage D c.1).toScheme.ringCatSheaf => g.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) x)
    (C.pullbackChartUnitIso_inv D c)).trans
    (schemeModuleHom_comp_val_app
      ((SchemeModuleRestriction.restrictionIsoPullback (C.chartPreimage D c.1).ι).hom.app ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)))
      (C.pullbackChartTrivialization D c).hom (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) x)

/-- The over-site restriction comparison sends the pulled-back frame to the restriction-adjunction
unit of the pulled-back frame. -/
theorem openToOverRestrictionIso_inv_app_pullbackFrame (c : C.GenericChart D) :
    (openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) (C.pullbackFrame D c) =
      ((SchemeModuleRestriction.restrictionAdjunction (C.chartPreimage D c.1).ι).unit.app ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).val.app (op (C.chartPreimage D c.1))
        (C.pullbackFrame D c) :=
  (openToOverRestrictionIso_inv_app (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.pullbackFrame D c)).trans
    (restrictionAdjunction_unit_app_val_app (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1)
      (eqToHom (openImage_preimage (C.chartPreimage D c.1) (Over.mk (homOfLE (le_rfl : (C.chartPreimage D c.1) ≤ (C.chartPreimage D c.1))))))
      (C.pullbackFrame D c)).symm

/-- The inverse pulled-back chart trivialization on the transported pulled-back frame is the
pulled-back trivialization on the doubly pulled-back frame. -/
theorem pullbackChartUnitIso_inv_pullbackFrame (c : C.GenericChart D) :
    (C.pullbackChartUnitIso D c).inv.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))
        ((openToOverRestrictionIso (C.chartPreimage D c.1) ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).inv.val.app (C.restrictedChartTop D c) (C.pullbackFrame D c)) =
      (C.pullbackChartTrivialization D c).hom.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))
        (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)) := by
  have h1 := congrArg (fun y => (C.pullbackChartUnitIso D c).inv.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) y)
    (C.openToOverRestrictionIso_inv_app_pullbackFrame D c)
  have h2 := C.pullbackChartUnitIso_inv_val_app D c
    (((SchemeModuleRestriction.restrictionAdjunction (C.chartPreimage D c.1).ι).unit.app ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D))).val.app (op (C.chartPreimage D c.1))
      (C.pullbackFrame D c))
  have h3 := congrArg (fun y => (C.pullbackChartTrivialization D c).hom.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1))) y)
    (restrictionIsoPullback_hom_app_unit (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c))
  exact h1.trans (h2.trans h3)

/-- **Reduction of the pulled-back frame fact to the pullback-language trivialization**: if the
pulled-back trivialization sends the doubly pulled-back frame to `1`, the frame has chart
coordinate `1` in the pulled-back atlas. -/
theorem chartEquiv_pullbackFrame_of_trivialization (c : C.GenericChart D)
    (hcore : (C.pullbackChartTrivialization D c).hom.val.app (op ((C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))
        (pullbackSection (C.chartPreimage D c.1).ι ((schemeModulePullback C.inclusion).obj (cartierDivisorModule X.toScheme D)) (C.chartPreimage D c.1) (C.pullbackFrame D c)) = (1 : Γ((C.chartPreimage D c.1).toScheme, (C.chartPreimage D c.1).ι ⁻¹ᵁ (C.chartPreimage D c.1)))) :
    chartEquiv C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
      (C.pullbackFrame D c) = 1 := by
  have h1 : chartEquiv C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
        (C.pullbackFrame D c) =
      ((C.pullbackLocalTrivializations D hD).unitIso c).hom.val.app (C.restrictedChartTop D c) (C.pullbackFrame D c) :=
    chartEquiv_apply C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
      (C.pullbackFrame D c)
  have h2 := C.pullbackLocalTrivializations_unitIso_hom_app D hD c (C.pullbackFrame D c)
  have h3 := C.pullbackChartIso_inv_app D c (C.pullbackFrame D c)
  have h4 := congrArg (fun y => (openToOverUnitIso (C.chartPreimage D c.1)).inv.val.app (C.restrictedChartTop D c) y)
    ((C.pullbackChartUnitIso_inv_pullbackFrame D c).trans hcore)
  have h5 := openToOverUnitIso_inv_app_one (C.chartPreimage D c.1)
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
