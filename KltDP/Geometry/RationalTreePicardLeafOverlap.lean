import KltDP.Geometry.RationalTreePicardComplementOverlap

/-!
# The coordinate comparison on the chart/leaf overlap

The chart/leaf overlap carries the node scalar. As on the complement side, both
coordinates of a section `s` over `W ≤ U ⊓ leafOpen` are compared on the closed leaf
component `Z_C` through the chart identification `Spec (Γ(X,U) ⧸ I) ≅ Z_C ∩ U`:

* the leaf-open coordinate, read on `Z_C`, is the frame value `frameC♯(s)`
  (`componentOpen_coordinate_value`, the general form of the complement-side lemma);
* the chart coordinate, read on `Z_C` and multiplied by the transported lifted node
  scalar `chartScalarSection`, is the frame value (`leafOverlap_coordinate_raw`, from
  `chartUnitIso_structure_left`, identification (c) for the leaf piece, and the
  sectionwise formula of `schemeScalarEnd`).

Hence `hleafT` (the leaf coordinate equation of `leafNodeUnitIsoOfTransposes`)
reduces to ONE remaining identity about constants: the leaf gauge unit `β`, restricted
to `W` and read on the chart piece, is the inverse of the transported lifted node
scalar (`LeafScalarIdentity`). With it, `leafNodeUnitIsoOfScalar` gives the
trivialization `L.obj ≅ unit`; the identity is proved for the inverse node-scalar
gauge unit in `RationalTreePicardLeafScalarIdentity` (`leafScalarIdentity_nodeScalarGauge_inv`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction TransitionUnitGluing

section GeneralOpen

variable (X : Scheme.{u}) [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  (S : Set ↥(irreducibleComponents X)) (V : X.Opens)
  (hV : (V : Set X) ⊆ componentClosedUnion X S) (L : InvertibleSheaf X)
  (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf)
  {W : X.Opens} (hWV : W ≤ V) (s : L.obj.val.obj (op W))

include hWV in
/-- The coordinate of a section in the open trivialization derived from a component
frame, read on the component union, is the frame value. -/
theorem componentOpen_coordinate_value :
    (componentUnionInclusion X S).app W
        (openSectionsInv V hWV
          ((pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
            (op W) s)) =
      (componentFrameTranspose X S L frame).val.app (op W) s := by
  have key0 := congrArg
    (fun φ : L.obj ⟶ (schemeModulePushforward
        ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫ componentUnionInclusion X S)).obj
        (_root_.SheafOfModules.unit (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf) =>
      φ.val.app (op W) s)
    (componentOpenFrame_transpose X S V hV L frame)
  have key : ((eqToIso (congrArg schemeModulePushforward
      (morphismRestrict_ι (componentUnionInclusion X S) V))).hom.app
        (_root_.SheafOfModules.unit
          (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf)).val.app (op W)
      ((componentUnionInclusion X S ∣_ V).app (V.ι ⁻¹ᵁ W)
        ((pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
          (op W) s)) =
    (componentUnionInclusion X S ⁻¹ᵁ V).ι.app (componentUnionInclusion X S ⁻¹ᵁ W)
      ((componentFrameTranspose X S L frame).val.app (op W) s) := key0
  have key' := (pushforward_eqToIso_unit_app (morphismRestrict_ι (componentUnionInclusion X S) V) W
    ((componentUnionInclusion X S ∣_ V).app (V.ι ⁻¹ᵁ W)
      ((pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
        (op W) s))).symm.trans key
  have hVy : V.ι.app W (openSectionsInv V hWV
      ((pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
        (op W) s)) =
      (pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
        (op W) s :=
    openSectionsInv_app' V hWV _
  apply openImmersion_app_injective (componentUnionInclusion X S ⁻¹ᵁ V).ι
    (componentUnionInclusion X S ⁻¹ᵁ W)
    (by
      rw [Scheme.Opens.opensRange_ι]
      exact fun x hx => hWV hx)
  change ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫ componentUnionInclusion X S).app W
    (openSectionsInv V hWV
      ((pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
        (op W) s)) = _
  rw [Scheme.congr_app (morphismRestrict_ι (componentUnionInclusion X S) V).symm W]
  change (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.presheaf.map (eqToHom _).op
    ((componentUnionInclusion X S ∣_ V).app (V.ι ⁻¹ᵁ W)
      (V.ι.app W (openSectionsInv V hWV
        ((pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame)).val.app
          (op W) s)))) = _
  rw [hVy]
  exact key'

end GeneralOpen

section LeafOverlap

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

/-- The affine transpose pushed to the leaf piece, with the lifted node scalar, is
the double transpose of the leaf chart frame. -/
theorem chartUnitIsoTranspose_structure_left :
    chartUnitIsoTranspose L f h frameC frameC' ≫
        (schemeModulePushforward U.2.fromSpec).map
          (structureToPushforwardUnit
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ≫
          (schemeModulePushforward
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
            (schemeScalarEnd (h.chartScalarSection L f frameC frameC'))) =
      (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).homEquiv _ _
          (componentChartFrame X {C} U L frameC).hom) :=
  (Adjunction.homEquiv_naturality_right _ _ _).symm.trans
    (congrArg (fun z => (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _ z)
      (chartUnitIso_structure_left L f h frameC frameC'))

set_option maxHeartbeats 800000 in
/-- The affine transpose pushed to the leaf piece with the scalar, transported through
`closedComponentInclusion_fromSpec`, is the transpose of the global leaf frame pushed to
that piece (identification (c) for the leaf piece). -/
theorem chartUnitIsoTranspose_leaf :
    (chartUnitIsoTranspose L f h frameC frameC' ≫
        (schemeModulePushforward U.2.fromSpec).map
          (structureToPushforwardUnit
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ≫
          (schemeModulePushforward
            (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
            (schemeScalarEnd (h.chartScalarSection L f frameC frameC')))) ≫
      (eqToIso (congrArg schemeModulePushforward
        (closedComponentInclusion_fromSpec X {C} U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).ringCatSheaf) =
    (componentFrameTranspose X {C} L frameC ≫
      (schemeModulePushforward (componentUnionInclusion X {C})).map
        (structureToPushforwardUnit (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι)) ≫
      (schemeModulePushforward ((componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X {C})).map
        (structureToPushforwardUnit (componentUnionChartIso X {C} U).hom) :=
  (congrArg
    (fun z : L.obj ⟶ (schemeModulePushforward U.2.fromSpec).obj
        ((schemeModulePushforward
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).obj
          (_root_.SheafOfModules.unit
            (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).ringCatSheaf)) =>
      z ≫ (eqToIso (congrArg schemeModulePushforward
        (closedComponentInclusion_fromSpec X {C} U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).ringCatSheaf))
    (chartUnitIsoTranspose_structure_left L f h frameC frameC')).trans
    (componentChartFrame_transpose X {C} U L frameC)

variable {W : X.Opens} (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C) (s : L.obj.val.obj (op W))

/-- The section `s` evaluated by the transpose of the global leaf frame. -/
abbrev leafFrameValue (L : InvertibleSheaf X)
    (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
    (s : L.obj.val.obj (op W)) :
    Γ(componentUnionScheme X {C}, componentUnionInclusion X {C} ⁻¹ᵁ W) :=
  (componentFrameTranspose X {C} L frameC).val.app (op W) s

/-- The lifted node scalar restricted to the chart piece over `W` and transported to
the leaf component through the chart identification. -/
abbrev transportedNodeScalar (L : InvertibleSheaf X) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (h : LeafNodeChart X C q U hq)
    (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
    (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) :
    Γ(Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U)),
      ((componentUnionChartIso X {C} U).hom ≫ (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι) ⁻¹ᵁ
        (componentUnionInclusion X {C} ⁻¹ᵁ W)) :=
  (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
    (eqToHom (show ((componentUnionChartIso X {C} U).hom ≫
      ((componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X {C})) ⁻¹ᵁ W =
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫ U.2.fromSpec) ⁻¹ᵁ W
      by rw [closedComponentInclusion_fromSpec X {C} U])).op
    ((Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
      (homOfLE (le_top : (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U) ≫
        U.2.fromSpec) ⁻¹ᵁ W ≤ ⊤)).op (h.chartScalarSection L f frameC frameC'))

include hWl in
/-- The leaf-open coordinate, read on `Z_C`, is the frame value. -/
theorem leafOpen_coordinate_value :
    (componentUnionInclusion X {C}).app W
        (openSectionsInv (leafOpen X C) hWl
          ((leafOpenTranspose L frameC).val.app (op W) s)) =
      leafFrameValue L frameC s :=
  componentOpen_coordinate_value X {C} (leafOpen X C) (leafOpen_subset X C) L frameC hWl s

set_option maxHeartbeats 800000 in
include hWU in
/-- The chart coordinate, read on `Z_C` through the chart identification and multiplied
by the transported lifted node scalar, is the frame value. -/
theorem leafOverlap_coordinate_raw :
    ((componentUnionChartIso X {C} U).hom ≫ (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι).app
          (componentUnionInclusion X {C} ⁻¹ᵁ W)
          ((componentUnionInclusion X {C}).app W
            (openSectionsInv U.1 hWU
              ((leafChartTranspose L f h frameC frameC').val.app (op W) s))) *
        transportedNodeScalar L f h frameC frameC' =
      ((componentUnionChartIso X {C} U).hom ≫ (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι).app
        (componentUnionInclusion X {C} ⁻¹ᵁ W) (leafFrameValue L frameC s) := by
  have hfs := chart_fromSpec_value L f h frameC frameC' hWU s
  have key2 : ((eqToIso (congrArg schemeModulePushforward
      (closedComponentInclusion_fromSpec X {C} U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).ringCatSheaf)).val.app
        (op W)
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)).app
            (U.2.fromSpec ⁻¹ᵁ W)
            ((chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s) *
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
            (homOfLE le_top).op (h.chartScalarSection L f frameC frameC')) =
      (componentUnionChartIso X {C} U).hom.app
        (((componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X {C}) ⁻¹ᵁ W)
        ((componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι.app (componentUnionInclusion X {C} ⁻¹ᵁ W)
          (leafFrameValue L frameC s)) :=
    congrArg (fun φ => φ.val.app (op W) s) (chartUnitIsoTranspose_leaf L f h frameC frameC')
  have key2' := (pushforward_eqToIso_unit_app (closedComponentInclusion_fromSpec X {C} U) W
    ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)).app
        (U.2.fromSpec ⁻¹ᵁ W)
        ((chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s) *
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (homOfLE le_top).op (h.chartScalarSection L f frameC frameC'))).symm.trans key2
  rw [map_mul] at key2'
  -- the chart side through the closed piece
  have hleft : ((componentUnionChartIso X {C} U).hom ≫
      (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι).app (componentUnionInclusion X {C} ⁻¹ᵁ W)
        ((componentUnionInclusion X {C}).app W (openSectionsInv U.1 hWU
          ((leafChartTranspose L f h frameC frameC').val.app (op W) s))) =
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom (congrArg (fun m => m ⁻¹ᵁ W) (closedComponentInclusion_fromSpec X {C} U).symm)).op
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)).app
          (U.2.fromSpec ⁻¹ᵁ W)
          ((chartUnitIsoTranspose L f h frameC frameC').val.app (op W) s)) := by
    change ((componentUnionChartIso X {C} U).hom ≫
        ((componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X {C})).app W
        (openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) = _
    rw [Scheme.congr_app (closedComponentInclusion_fromSpec X {C} U).symm W]
    change (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).presheaf.map
        (eqToHom _).op
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)).app
          (U.2.fromSpec ⁻¹ᵁ W)
          (U.2.fromSpec.app W (openSectionsInv U.1 hWU
            ((leafChartTranspose L f h frameC frameC').val.app (op W) s)))) = _
    rw [hfs]
    rfl
  rw [hleft]
  exact key2'

/-- The remaining scalar identity for the leaf overlap: the leaf gauge unit, restricted
to `W` and read on the chart piece of the leaf component, is the inverse of the
transported lifted node scalar. -/
def LeafScalarIdentity (β : Γ(X, leafOpen X C)ˣ) : Prop :=
  ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C),
    ((componentUnionChartIso X {C} U).hom ≫ (componentUnionInclusion X {C} ⁻¹ᵁ U.1).ι).app
        (componentUnionInclusion X {C} ⁻¹ᵁ W)
        ((componentUnionInclusion X {C}).app W (res X hWl (β : Γ(X, leafOpen X C)))) *
      transportedNodeScalar L f h frameC frameC' = 1

end LeafOverlap

end KltDP.Geometry.RationalTreePicard
