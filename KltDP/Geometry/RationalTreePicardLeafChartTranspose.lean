import KltDP.Geometry.RationalTreePicardClosedCoverMatchingMap

/-!
# Transposes of the chart trivialization

The chart trivialization `leafChartOpenUnitIso` of `L` on the open subscheme `U`
is the affine leaf-node trivialization `LeafNodeChart.chartUnitIso` on
`Spec Γ(X,U)` transported through the affine identification `isoSpec`. Its
transpose along `U.ι` is computed here in terms of the transpose
`chartUnitIsoTranspose` of the affine trivialization along `fromSpec`
(`leafChartTranspose_eq`).

The affine trivialization followed by the structure map to each closed piece is
the transpose of the corresponding affine-piece frame
(`chartUnitIso_structure_right`, from the compatibility module's
`chartUnitIso_pullback_right`; the left version carries the lifted node scalar).
Combined with task 7's `componentChartFrame_transpose`, the transpose of the chart
trivialization, pushed to the complement piece, is therefore the transpose of the
global complement frame pushed to that piece
(`chartUnitIsoTranspose_structure_right`, `chartUnitIsoTranspose_complement`).
These are the chart-side inputs of the overlap comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

variable {X : Scheme.{u}} [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  (L : InvertibleSheaf X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)
  (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
  (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf)

/-- The transpose of the affine leaf-node trivialization along `fromSpec`. -/
abbrev chartUnitIsoTranspose :
    L.obj ⟶ (schemeModulePushforward U.2.fromSpec).obj
      (_root_.SheafOfModules.unit (Spec (CommRingCat.of Γ(X, U.1))).ringCatSheaf) :=
  (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv L.obj _
    (LeafNodeChart.chartUnitIso L f h frameC frameC').hom

/-- The chart trivialization after the equality transport. -/
def chartOpenRest :
    (schemeModulePullback (U.2.isoSpec.hom ≫ U.2.fromSpec)).obj L.obj ⟶
      _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf :=
  (schemeModulePullbackCompIso U.2.isoSpec.hom U.2.fromSpec).inv.app L.obj ≫
    (schemeModulePullback U.2.isoSpec.hom).map (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
    (schemeModulePullbackUnitIso U.2.isoSpec.hom).hom

set_option maxHeartbeats 800000 in
theorem leafChartOpenUnitIso_hom :
    (leafChartOpenUnitIso L f h frameC frameC').hom =
      ((eqToIso (congrArg schemeModulePullback (affineOpen_ι_eq_isoSpec_fromSpec U))).app
        L.obj).hom ≫ chartOpenRest L f h frameC frameC' := rfl

theorem compIso_hom_app_chartOpenRest :
    (schemeModulePullbackCompIso U.2.isoSpec.hom U.2.fromSpec).hom.app L.obj ≫
        chartOpenRest L f h frameC frameC' =
      (schemeModulePullback U.2.isoSpec.hom).map
          (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        (schemeModulePullbackUnitIso U.2.isoSpec.hom).hom := by
  unfold chartOpenRest
  exact Iso.hom_inv_id_app_assoc _ _ _

set_option maxHeartbeats 800000 in
/-- The transpose of the chart trivialization along `U.ι`, transported through
`U.ι = isoSpec.hom ≫ fromSpec`, is the transpose of the affine trivialization
followed by the structure map of the affine identification. -/
theorem leafChartTranspose_eq :
    leafChartTranspose L f h frameC frameC' ≫
        (eqToIso (congrArg schemeModulePushforward (affineOpen_ι_eq_isoSpec_fromSpec U))).hom.app
          (_root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf) =
      chartUnitIsoTranspose L f h frameC frameC' ≫
        (schemeModulePushforward U.2.fromSpec).map (structureToPushforwardUnit U.2.isoSpec.hom) := by
  have hu : (schemeModulePullbackPushforwardAdjunction U.2.isoSpec.hom).homEquiv _ _
      (schemeModulePullbackUnitIso U.2.isoSpec.hom).hom =
      structureToPushforwardUnit U.2.isoSpec.hom :=
    schemeModulePullbackUnitHom_adjunction U.2.isoSpec.hom
  have s0 := congrArg
    (fun z : (schemeModulePullback U.1.ι).obj L.obj ⟶
        _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf =>
      (schemeModulePullbackPushforwardAdjunction U.1.ι).homEquiv _ _ z ≫
        (eqToIso (congrArg schemeModulePushforward (affineOpen_ι_eq_isoSpec_fromSpec U))).hom.app
          (_root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf))
    (leafChartOpenUnitIso_hom L f h frameC frameC')
  have e1 := schemeModulePullback_homEquiv_eqToIso_app (affineOpen_ι_eq_isoSpec_fromSpec U) L.obj
    _ (chartOpenRest L f h frameC frameC')
  have e2 : (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction U.2.isoSpec.hom).homEquiv _ _
        ((schemeModulePullbackCompIso U.2.isoSpec.hom U.2.fromSpec).hom.app L.obj ≫
          chartOpenRest L f h frameC frameC')) =
      (schemeModulePullbackPushforwardAdjunction (U.2.isoSpec.hom ≫ U.2.fromSpec)).homEquiv _ _
        (chartOpenRest L f h frameC frameC') :=
    schemeModulePullbackCompIso_homEquiv _ _ _ _ _
  have e3 := congrArg
    (fun z : (schemeModulePullback U.2.isoSpec.hom).obj
        ((schemeModulePullback U.2.fromSpec).obj L.obj) ⟶
        _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf =>
      (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction U.2.isoSpec.hom).homEquiv _ _ z))
    (compIso_hom_app_chartOpenRest L f h frameC frameC')
  have e4 : (schemeModulePullbackPushforwardAdjunction U.2.isoSpec.hom).homEquiv _ _
      ((schemeModulePullback U.2.isoSpec.hom).map
          (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        (schemeModulePullbackUnitIso U.2.isoSpec.hom).hom) =
      (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        structureToPushforwardUnit U.2.isoSpec.hom := by
    rw [Adjunction.homEquiv_naturality_left, hu]
  have e4' := congrArg
    (fun z : (schemeModulePullback U.2.fromSpec).obj L.obj ⟶
        (schemeModulePushforward U.2.isoSpec.hom).obj
          (_root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf) =>
      (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _ z) e4
  have e5 : (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
      ((LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        structureToPushforwardUnit U.2.isoSpec.hom) =
      chartUnitIsoTranspose L f h frameC frameC' ≫
        (schemeModulePushforward U.2.fromSpec).map (structureToPushforwardUnit U.2.isoSpec.hom) :=
    Adjunction.homEquiv_naturality_right _ _ _
  exact s0.trans (e1.trans (e2.symm.trans (e3.trans (e4'.trans e5))))

/-- The affine trivialization followed by the structure map to the complement
closed piece is the transpose of the complement chart frame. -/
theorem chartUnitIso_structure_right :
    (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        structureToPushforwardUnit
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)) =
      (schemeModulePullbackPushforwardAdjunction
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).homEquiv _ _
        (componentChartFrame X ({C}ᶜ) U L frameC').hom := by
  have hu : (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).homEquiv _ _
        (schemeModulePullbackUnitIso
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).hom =
      structureToPushforwardUnit
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)) :=
    schemeModulePullbackUnitHom_adjunction _
  have h2 : (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).homEquiv _ _
        ((schemeModulePullback
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).map
            (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
          (schemeModulePullbackUnitIso
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).hom) =
      (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        (schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).homEquiv _ _
          (schemeModulePullbackUnitIso
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).hom :=
    Adjunction.homEquiv_naturality_left _ _ _
  exact ((h2.trans (congrArg (fun z => (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫ z)
    hu)).symm).trans
    (congrArg (fun z => (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).homEquiv _ _ z)
      (LeafNodeChart.chartUnitIso_pullback_right L f h frameC frameC'))

/-- The affine trivialization followed by the structure map to the leaf closed
piece and the lifted node scalar is the transpose of the leaf chart frame. -/
theorem chartUnitIso_structure_left :
    (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        structureToPushforwardUnit
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ≫
        (schemeModulePushforward
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
          (schemeScalarEnd (h.chartScalarSection L f frameC frameC')) =
      (schemeModulePullbackPushforwardAdjunction
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _
        (componentChartFrame X {C} U L frameC).hom := by
  have hu : (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _
        (schemeModulePullbackUnitIso
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).hom =
      structureToPushforwardUnit
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) :=
    schemeModulePullbackUnitHom_adjunction _
  have h2 : (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _
        ((schemeModulePullback
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
            (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
          (schemeModulePullbackUnitIso
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).hom ≫
          schemeScalarEnd (h.chartScalarSection L f frameC frameC')) =
      (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
        (schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _
          ((schemeModulePullbackUnitIso
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).hom ≫
            schemeScalarEnd (h.chartScalarSection L f frameC frameC')) :=
    Adjunction.homEquiv_naturality_left _ _ _
  have h3 : (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _
        ((schemeModulePullbackUnitIso
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).hom ≫
          schemeScalarEnd (h.chartScalarSection L f frameC frameC')) =
      structureToPushforwardUnit
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ≫
        (schemeModulePushforward
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
          (schemeScalarEnd (h.chartScalarSection L f frameC frameC')) := by
    rw [Adjunction.homEquiv_naturality_right, hu]
  exact ((h2.trans (congrArg (fun z => (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫ z)
    h3)).symm).trans
    (congrArg (fun z => (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _ z)
      (LeafNodeChart.chartUnitIso_pullback_left L f h frameC frameC'))

/-- The affine transpose pushed to the complement piece is the double transpose
of the complement chart frame. -/
theorem chartUnitIsoTranspose_structure_right :
    chartUnitIsoTranspose L f h frameC frameC' ≫
        (schemeModulePushforward U.2.fromSpec).map
          (structureToPushforwardUnit
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))) =
      (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).homEquiv _ _
          (componentChartFrame X ({C}ᶜ) U L frameC').hom) :=
  (Adjunction.homEquiv_naturality_right _ _ _).symm.trans
    (congrArg (fun z => (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _ z)
      (chartUnitIso_structure_right L f h frameC frameC'))

set_option maxHeartbeats 800000 in
/-- The affine transpose pushed to the complement piece and transported through
`closedComponentInclusion_fromSpec` is the transpose of the global complement
frame pushed to that piece (task 7's identification (c)). -/
theorem chartUnitIsoTranspose_complement :
    (chartUnitIsoTranspose L f h frameC frameC' ≫
        (schemeModulePushforward U.2.fromSpec).map
          (structureToPushforwardUnit
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)))) ≫
      (eqToIso (congrArg schemeModulePushforward
        (closedComponentInclusion_fromSpec X ({C}ᶜ) U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).ringCatSheaf) =
    (componentFrameTranspose X ({C}ᶜ) L frameC' ≫
      (schemeModulePushforward (componentUnionInclusion X ({C}ᶜ))).map
        (structureToPushforwardUnit (componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι)) ≫
      (schemeModulePushforward ((componentUnionInclusion X ({C}ᶜ) ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X ({C}ᶜ))).map
        (structureToPushforwardUnit (componentUnionChartIso X ({C}ᶜ) U).hom) :=
  (congrArg
    (fun z : L.obj ⟶ (schemeModulePushforward U.2.fromSpec).obj
        ((schemeModulePushforward
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).obj
          (_root_.SheafOfModules.unit
            (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).ringCatSheaf)) =>
      z ≫ (eqToIso (congrArg schemeModulePushforward
        (closedComponentInclusion_fromSpec X ({C}ᶜ) U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).ringCatSheaf))
    (chartUnitIsoTranspose_structure_right L f h frameC frameC')).trans
    (componentChartFrame_transpose X ({C}ᶜ) U L frameC')

end KltDP.Geometry.RationalTreePicard
