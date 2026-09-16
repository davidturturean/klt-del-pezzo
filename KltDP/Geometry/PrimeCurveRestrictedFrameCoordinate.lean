import KltDP.Geometry.PrimeCurveRestrictionPicardCocycle

/-!
# The restricted frames have chart coordinate `1`

In the accepted Cartier trivialization of `O_C(D|_C)` on a restricted chart, the frame
`1/(f_c|_C)` is the image of `1`; its coordinate in the restricted atlas is therefore `1`
(hom–inverse cancellation on the over-site). This discharges the hypothesis `hres` of the
Picard-class bridge, which then depends only on the pulled-back frame fact `hpull`.

The two tactic-built isomorphisms involved (the free-singleton comparison and the accepted
chart trivialization) are wrapped in constants, and every step is a `congrArg` or an
instance of a generic identity, so that the elaborator never unifies one against the other.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry.TransitionUnitGluing KltDP.Geometry.TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D : CartierDivisor X.toScheme) (hD : HasRegularCartierEquations X.toScheme D)
  (hC : C.NotInSupport D hD)

/-- The accepted chart trivialization of `O_C(D|_C)` on a restricted chart, as a constant. -/
def restrictedChartIso (c : C.GenericChart D) :
    _root_.SheafOfModules.unit
        (C.toScheme.ringCatSheaf.over (C.restrictedChart D hD hC c).chart.openSet) ≅
      (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).over
        (C.restrictedChart D hD hC c).chart.openSet :=
  cartierEquationOverIso C.toScheme (C.restrictCartier D hD hC)
    (C.restrictedChart D hD hC c).chart.openSet (C.restrictedChart D hD hC c).chart.equation
    (C.restrictedChart D hD hC c).chart.represents

/-- The free-singleton comparison on a restricted chart, as a constant. -/
def restrictedFreeIso (c : C.GenericChart D) :
    _root_.SheafOfModules.free (R := C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) PUnit ≅
      _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) :=
  _root_.SheafOfModules.freeUniqueIsoUnit
    (R := C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) PUnit

/-- The restricted chart, viewed as the top object of its own over-site. -/
abbrev restrictedChartTop (c : C.GenericChart D) : (Over (C.chartPreimage D c.1))ᵒᵖ :=
  op (Over.mk (homOfLE (le_rfl : C.chartPreimage D c.1 ≤ C.chartPreimage D c.1)))

/-- The chart open of the restricted atlas. -/
theorem restrictedLocalTrivializations_X (c : C.GenericChart D) :
    (C.restrictedLocalTrivializations D hD hC).X c = C.chartPreimage D c.1 := rfl

/-- The chart isomorphism of the restricted atlas. -/
theorem restrictedLocalTrivializations_iso (c : C.GenericChart D) :
    (C.restrictedLocalTrivializations D hD hC).iso c =
      C.restrictedFreeIso D c ≪≫ C.restrictedChartIso D hD hC c := rfl

/-- The unit trivialization of the restricted atlas, unfolded. -/
theorem restrictedLocalTrivializations_unitIso_hom (c : C.GenericChart D) :
    ((C.restrictedLocalTrivializations D hD hC).unitIso c).hom =
      ((C.restrictedLocalTrivializations D hD hC).iso c).inv ≫ (C.restrictedFreeIso D c).hom := rfl

/-- The restricted frame is the chart trivialization applied to `1`. -/
theorem restrictedFrame_eq_hom_one (c : C.GenericChart D) :
    C.restrictedFrame D hD hC c =
      (C.restrictedChartIso D hD hC c).hom.val.app (C.restrictedChartTop D c)
        (1 : Γ(C.toScheme, C.chartPreimage D c.1)) := rfl

/-- Generic: evaluating a composite of module-sheaf morphisms on a section. -/
theorem overSheafHom_comp_val_app {U : C.toScheme.Opens}
    {A B E : _root_.SheafOfModules.{u} (C.toScheme.ringCatSheaf.over U)} (a : A ⟶ B) (b : B ⟶ E)
    (V : (Over U)ᵒᵖ) (x : A.val.obj V) :
    (a ≫ b).val.app V x = b.val.app V (a.val.app V x) := rfl

/-- Generic: evaluating the identity morphism on a section. -/
theorem overSheafHom_id_val_app {U : C.toScheme.Opens}
    (A : _root_.SheafOfModules.{u} (C.toScheme.ringCatSheaf.over U)) (V : (Over U)ᵒᵖ)
    (x : A.val.obj V) : (_root_.SheafOfModules.Hom.val (𝟙 A)).app V x = x := rfl

/-- Evaluation of the unit trivialization of the restricted atlas at the chart: it is the inverse
of the accepted chart trivialization. -/
theorem restrictedLocalTrivializations_unitIso_hom_app (c : C.GenericChart D)
    (s : (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).val.obj
      (op (C.chartPreimage D c.1))) :
    ((C.restrictedLocalTrivializations D hD hC).unitIso c).hom.val.app
        (op (Over.mk (homOfLE (le_rfl : C.chartPreimage D c.1 ≤ C.chartPreimage D c.1)))) s =
      (cartierEquationOverIso C.toScheme (C.restrictCartier D hD hC)
        (C.restrictedChart D hD hC c).chart.openSet (C.restrictedChart D hD hC c).chart.equation
        (C.restrictedChart D hD hC c).chart.represents).inv.val.app
        (op (Over.mk (homOfLE (le_rfl : C.chartPreimage D c.1 ≤ C.chartPreimage D c.1)))) s := by
  have h1 : ((C.restrictedLocalTrivializations D hD hC).unitIso c).hom.val.app (C.restrictedChartTop D c) s =
      (((C.restrictedLocalTrivializations D hD hC).iso c).inv ≫ (C.restrictedFreeIso D c).hom).val.app (C.restrictedChartTop D c) s :=
    congrArg (fun g : (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).over (C.chartPreimage D c.1) ⟶ _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) => g.val.app (C.restrictedChartTop D c) s)
      (C.restrictedLocalTrivializations_unitIso_hom D hD hC c)
  have h2 : (((C.restrictedLocalTrivializations D hD hC).iso c).inv ≫ (C.restrictedFreeIso D c).hom).val.app (C.restrictedChartTop D c) s =
      (C.restrictedFreeIso D c).hom.val.app (C.restrictedChartTop D c) (((C.restrictedLocalTrivializations D hD hC).iso c).inv.val.app (C.restrictedChartTop D c) s) :=
    C.overSheafHom_comp_val_app ((C.restrictedLocalTrivializations D hD hC).iso c).inv (C.restrictedFreeIso D c).hom (C.restrictedChartTop D c) s
  have h3 : ((C.restrictedLocalTrivializations D hD hC).iso c).inv.val.app (C.restrictedChartTop D c) s =
      ((C.restrictedFreeIso D c) ≪≫ (C.restrictedChartIso D hD hC c)).inv.val.app (C.restrictedChartTop D c) s :=
    congrArg (fun e : _root_.SheafOfModules.free (R := C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) PUnit ≅ (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).over (C.chartPreimage D c.1) => e.inv.val.app (C.restrictedChartTop D c) s)
      (C.restrictedLocalTrivializations_iso D hD hC c)
  have h4 : ((C.restrictedFreeIso D c) ≪≫ (C.restrictedChartIso D hD hC c)).inv.val.app (C.restrictedChartTop D c) s =
      ((C.restrictedChartIso D hD hC c).inv ≫ (C.restrictedFreeIso D c).inv).val.app (C.restrictedChartTop D c) s :=
    congrArg (fun g : (cartierDivisorModule C.toScheme (C.restrictCartier D hD hC)).over (C.chartPreimage D c.1) ⟶ _root_.SheafOfModules.free (R := C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) PUnit => g.val.app (C.restrictedChartTop D c) s) (Iso.trans_inv (C.restrictedFreeIso D c) (C.restrictedChartIso D hD hC c))
  have h5 : ((C.restrictedChartIso D hD hC c).inv ≫ (C.restrictedFreeIso D c).inv).val.app (C.restrictedChartTop D c) s =
      (C.restrictedFreeIso D c).inv.val.app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s) :=
    C.overSheafHom_comp_val_app (C.restrictedChartIso D hD hC c).inv (C.restrictedFreeIso D c).inv (C.restrictedChartTop D c) s
  have h6 : (C.restrictedFreeIso D c).hom.val.app (C.restrictedChartTop D c) ((C.restrictedFreeIso D c).inv.val.app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s)) =
      ((C.restrictedFreeIso D c).inv ≫ (C.restrictedFreeIso D c).hom).val.app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s) :=
    (C.overSheafHom_comp_val_app (C.restrictedFreeIso D c).inv (C.restrictedFreeIso D c).hom (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s)).symm
  have h7 : ((C.restrictedFreeIso D c).inv ≫ (C.restrictedFreeIso D c).hom).val.app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s) =
      (_root_.SheafOfModules.Hom.val (𝟙 (_root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1))))).app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s) :=
    congrArg (fun g : _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) ⟶ _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1)) =>
      (_root_.SheafOfModules.Hom.val g).app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s)) (C.restrictedFreeIso D c).inv_hom_id
  have h8 : (_root_.SheafOfModules.Hom.val (𝟙 (_root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1))))).app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s) =
      (C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s :=
    C.overSheafHom_id_val_app (_root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.chartPreimage D c.1))) (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) s)
  exact h1.trans (h2.trans ((congrArg (fun y => (C.restrictedFreeIso D c).hom.val.app (C.restrictedChartTop D c) y)
    (h3.trans (h4.trans h5))).trans (h6.trans (h7.trans h8))))

/-- **The restricted frame has chart coordinate `1` in the restricted atlas.** -/
theorem chartEquiv_restrictedFrame (c : C.GenericChart D) :
    chartEquiv C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c le_rfl (C.restrictedFrame D hD hC c) = 1 := by
  have h1 : chartEquiv C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c le_rfl (C.restrictedFrame D hD hC c) =
      ((C.restrictedLocalTrivializations D hD hC).unitIso c).hom.val.app (C.restrictedChartTop D c) (C.restrictedFrame D hD hC c) :=
    chartEquiv_apply C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c le_rfl (C.restrictedFrame D hD hC c)
  have h2 : ((C.restrictedLocalTrivializations D hD hC).unitIso c).hom.val.app (C.restrictedChartTop D c) (C.restrictedFrame D hD hC c) =
      (C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) (C.restrictedFrame D hD hC c) :=
    C.restrictedLocalTrivializations_unitIso_hom_app D hD hC c (C.restrictedFrame D hD hC c)
  have h3 : (C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) (C.restrictedFrame D hD hC c) =
      (C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).hom.val.app (C.restrictedChartTop D c) (1 : Γ(C.toScheme, C.chartPreimage D c.1))) :=
    congrArg (fun y => (C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) y) (C.restrictedFrame_eq_hom_one D hD hC c)
  have h4 : (C.restrictedChartIso D hD hC c).inv.val.app (C.restrictedChartTop D c) ((C.restrictedChartIso D hD hC c).hom.val.app (C.restrictedChartTop D c) (1 : Γ(C.toScheme, C.chartPreimage D c.1))) =
      ((C.restrictedChartIso D hD hC c).hom ≫ (C.restrictedChartIso D hD hC c).inv).val.app (C.restrictedChartTop D c) (1 : Γ(C.toScheme, C.chartPreimage D c.1)) :=
    (C.overSheafHom_comp_val_app (C.restrictedChartIso D hD hC c).hom (C.restrictedChartIso D hD hC c).inv (C.restrictedChartTop D c)
      (1 : Γ(C.toScheme, C.chartPreimage D c.1))).symm
  have h5 : ((C.restrictedChartIso D hD hC c).hom ≫ (C.restrictedChartIso D hD hC c).inv).val.app (C.restrictedChartTop D c) (1 : Γ(C.toScheme, C.chartPreimage D c.1)) =
      (_root_.SheafOfModules.Hom.val (𝟙 (_root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.restrictedChart D hD hC c).chart.openSet)))).app (C.restrictedChartTop D c)
        (1 : Γ(C.toScheme, C.chartPreimage D c.1)) :=
    congrArg (fun g : _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.restrictedChart D hD hC c).chart.openSet) ⟶ _root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.restrictedChart D hD hC c).chart.openSet) =>
      (_root_.SheafOfModules.Hom.val g).app (C.restrictedChartTop D c) (1 : Γ(C.toScheme, C.chartPreimage D c.1)))
      (C.restrictedChartIso D hD hC c).hom_inv_id
  have h6 : (_root_.SheafOfModules.Hom.val (𝟙 (_root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.restrictedChart D hD hC c).chart.openSet)))).app (C.restrictedChartTop D c)
        (1 : Γ(C.toScheme, C.chartPreimage D c.1)) = (1 : Γ(C.toScheme, C.chartPreimage D c.1)) :=
    C.overSheafHom_id_val_app (_root_.SheafOfModules.unit (C.toScheme.ringCatSheaf.over (C.restrictedChart D hD hC c).chart.openSet)) (C.restrictedChartTop D c) (1 : Γ(C.toScheme, C.chartPreimage D c.1))
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- The restricted atlas has the image cocycle. -/
theorem transitionUnits_restrictedLocalTrivializations_eq (c d : C.GenericChart D) :
    transitionUnits C.toScheme _ (C.restrictedLocalTrivializations D hD hC) c d =
      C.imageCocycle D c d :=
  C.transitionUnits_restricted_of_frames D hD hC (C.chartEquiv_restrictedFrame D hD hC) c d

/-- **The Picard-class bridge, conditional only on the pulled-back frame fact `hpull`.** -/
theorem picardClass_restrict_eq_pullback_of_pullbackFrames
    (hpull : ∀ c : C.GenericChart D,
      chartEquiv C.toScheme _ (C.pullbackLocalTrivializations D hD) c le_rfl
        (C.pullbackFrame D c) = 1) :
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D hD hC)).toPic =
      (pullbackInvertibleSheaf C.inclusion (cartierDivisorInvertibleSheaf X.toScheme D)).toPic :=
  C.picardClass_restrict_eq_pullback_of_frames D hD hC (C.chartEquiv_restrictedFrame D hD hC) hpull

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
