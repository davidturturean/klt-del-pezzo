import KltDP.Geometry.RationalTreePicardComponentOpenFrameTranspose

/-!
# The closed-cover route: the chart frame transpose and the canonical matching maps

Closed-cover route for the gluing step of Lemma 2.2. The single identification (c)
of the route is proved here in its adjunction form: the frame
`componentChartFrame X S U L frame` on the affine closed piece `Spec (Γ(X,U) ⧸ I_S)`
(the accepted affine descent's input) is the global frame `frame` on `Z_S`
transported through `Spec (Γ(X,U) ⧸ I_S) ≅ Z_S ∩ U → Z_S` and `Spec Γ(X,U) → X`.
`componentChartFrame_transpose` states that its double transpose (along the affine
closed immersion, then along `fromSpec`), pushed forward through the equality
`closedComponentInclusion_fromSpec`, equals the transpose `frame♯` of the global
frame pushed forward to the piece. So the accepted affine matching map on the
chart, whose components are exactly these transposes
(`closedComponentFrameSheafMap`), is the restriction of a map defined on `X`.

Also defined (no theorem about them yet): the canonical closed-cover maps on `X`,
`closedCoverStructureMap : O_X ⟶ ι_{C*} O ⨯ ι'_* O` (the structure maps) and
`closedCoverFrameMap u : L ⟶ ι_{C*} O ⨯ ι'_* O` (the frame transposes, the leaf
factor scaled by a global section `u`), together with `schemeBaseSections`, the
base field mapped into sections through a structure morphism. The route's remaining
theorems (both maps isomorphisms onto the matching subsheaf, hence `L ≅ O_X`) are
recorded in `LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

section EqToIsoApp

variable {X Y : Scheme.{u}}

/-- Equality transport for the actual adjunction, for the functor-level equality
isomorphism applied at an object (the form used by `componentChartFrame`). -/
theorem schemeModulePullback_homEquiv_eqToIso_app {f g : X ⟶ Y} (e : f = g)
    (M : Y.Modules) (N : X.Modules) (a : (schemeModulePullback g).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv M N
        (((eqToIso (congrArg schemeModulePullback e)).app M).hom ≫ a) ≫
      (eqToIso (congrArg schemeModulePushforward e)).hom.app N =
        (schemeModulePullbackPushforwardAdjunction g).homEquiv M N a := by
  subst e
  simp only [eqToIso_refl, Iso.refl_hom, Iso.app_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

end EqToIsoApp

section ChartFrameTranspose

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens) (L : InvertibleSheaf X)
  (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf)

/-- The inner part of the chart frame: the frame pulled back to `Z_S ∩ U`. -/
def chartFrameInner
    (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :
    (schemeModulePullback ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).obj L.obj ⟶
      _root_.SheafOfModules.unit (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme.ringCatSheaf :=
  (schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι
    (componentUnionInclusion X S)).inv.app L.obj ≫
    (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).map frame.hom ≫
    (schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).hom

/-- The chart frame after the composition comparison and the equality transport. -/
def chartFrameRest
    (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :
    (schemeModulePullback ((componentUnionChartIso X S U).hom ≫
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S))).obj L.obj ⟶
      _root_.SheafOfModules.unit
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf :=
  (schemeModulePullbackCompIso (componentUnionChartIso X S U).hom
    ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).inv.app L.obj ≫
    (schemeModulePullback (componentUnionChartIso X S U).hom).map (chartFrameInner X S U L frame) ≫
    (schemeModulePullbackUnitIso (componentUnionChartIso X S U).hom).hom

/-- The forward map of the chart frame is the composition comparison, the equality
transport, and the remaining maps. -/
theorem componentChartFrame_hom :
    (componentChartFrame X S U L frame).hom =
      (schemeModulePullbackCompIso
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U)) U.2.fromSpec).hom.app
          L.obj ≫
        ((eqToIso (congrArg schemeModulePullback
          (closedComponentInclusion_fromSpec X S U))).app L.obj).hom ≫
        chartFrameRest X S U L frame := rfl

theorem compIso_hom_app_chartFrameRest :
    (schemeModulePullbackCompIso (componentUnionChartIso X S U).hom
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).hom.app L.obj ≫
      chartFrameRest X S U L frame =
    (schemeModulePullback (componentUnionChartIso X S U).hom).map (chartFrameInner X S U L frame) ≫
      (schemeModulePullbackUnitIso (componentUnionChartIso X S U).hom).hom := by
  unfold chartFrameRest
  exact Iso.hom_inv_id_app_assoc _ _ _

theorem compIso_hom_app_chartFrameInner :
    (schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι
        (componentUnionInclusion X S)).hom.app L.obj ≫ chartFrameInner X S U L frame =
    (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).map frame.hom ≫
      (schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).hom := by
  unfold chartFrameInner
  exact Iso.hom_inv_id_app_assoc _ _ _

set_option maxHeartbeats 800000 in
/-- First half of identification (c): the double transpose of the chart frame,
transported, is the transpose of `chartFrameRest` along the composite
`e.hom ≫ (V.ι ≫ ι)`. -/
theorem componentChartFrame_transpose_aux₁ :
    (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).homEquiv _ _
          (componentChartFrame X S U L frame).hom) ≫
      (eqToIso (congrArg schemeModulePushforward (closedComponentInclusion_fromSpec X S U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf) =
    (schemeModulePullbackPushforwardAdjunction ((componentUnionChartIso X S U).hom ≫
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S))).homEquiv _ _
        (chartFrameRest X S U L frame) := by
  -- e2: the first composition comparison
  have e2 : (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).homEquiv _ _
        ((schemeModulePullbackCompIso
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U)) U.2.fromSpec).hom.app
            L.obj ≫
          ((eqToIso (congrArg schemeModulePullback
            (closedComponentInclusion_fromSpec X S U))).app L.obj).hom ≫
          chartFrameRest X S U L frame)) =
      (schemeModulePullbackPushforwardAdjunction
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U) ≫ U.2.fromSpec)).homEquiv
        _ _ (((eqToIso (congrArg schemeModulePullback
            (closedComponentInclusion_fromSpec X S U))).app L.obj).hom ≫
          chartFrameRest X S U L frame) :=
    schemeModulePullbackCompIso_homEquiv _ _ _ _ _
  -- e3: equality transport
  have e3 : (schemeModulePullbackPushforwardAdjunction
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U) ≫ U.2.fromSpec)).homEquiv
        _ _ (((eqToIso (congrArg schemeModulePullback
            (closedComponentInclusion_fromSpec X S U))).app L.obj).hom ≫
          chartFrameRest X S U L frame) ≫
      (eqToIso (congrArg schemeModulePushforward (closedComponentInclusion_fromSpec X S U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf) =
      (schemeModulePullbackPushforwardAdjunction ((componentUnionChartIso X S U).hom ≫
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S))).homEquiv _ _
        (chartFrameRest X S U L frame) :=
    schemeModulePullback_homEquiv_eqToIso_app (closedComponentInclusion_fromSpec X S U) L.obj _
      (chartFrameRest X S U L frame)
  have s1 := congrArg
    (fun z : L.obj ⟶ (schemeModulePushforward U.2.fromSpec).obj
        ((schemeModulePushforward
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).obj
          (_root_.SheafOfModules.unit
            (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf)) =>
      z ≫ (eqToIso (congrArg schemeModulePushforward
        (closedComponentInclusion_fromSpec X S U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf))
    (congrArg (fun z => (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).homEquiv _ _ z))
      (componentChartFrame_hom X S U L frame))
  have s2 := congrArg
    (fun z : L.obj ⟶ (schemeModulePushforward U.2.fromSpec).obj
        ((schemeModulePushforward
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).obj
          (_root_.SheafOfModules.unit
            (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf)) =>
      z ≫ (eqToIso (congrArg schemeModulePushforward
        (closedComponentInclusion_fromSpec X S U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf)) e2
  exact s1.trans (s2.trans e3)

set_option maxHeartbeats 800000 in
/-- Second half of identification (c): the transpose of `chartFrameRest` along the
composite is the transpose of the global frame pushed to the piece. -/
theorem componentChartFrame_transpose_aux₂ :
    (schemeModulePullbackPushforwardAdjunction ((componentUnionChartIso X S U).hom ≫
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S))).homEquiv _ _
        (chartFrameRest X S U L frame) =
    (componentFrameTranspose X S L frame ≫
      (schemeModulePushforward (componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ U.1).ι)) ≫
      (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom) := by
  have hu_e : (schemeModulePullbackPushforwardAdjunction
      (componentUnionChartIso X S U).hom).homEquiv _ _
        (schemeModulePullbackUnitIso (componentUnionChartIso X S U).hom).hom =
      structureToPushforwardUnit (componentUnionChartIso X S U).hom :=
    schemeModulePullbackUnitHom_adjunction (componentUnionChartIso X S U).hom
  have hu_V : (schemeModulePullbackPushforwardAdjunction
      (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).homEquiv _ _
        (schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).hom =
      structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ U.1).ι :=
    schemeModulePullbackUnitHom_adjunction (componentUnionInclusion X S ⁻¹ᵁ U.1).ι
  -- e4: the second composition comparison
  have e4 : (schemeModulePullbackPushforwardAdjunction
      ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction (componentUnionChartIso X S U).hom).homEquiv _ _
          ((schemeModulePullbackCompIso (componentUnionChartIso X S U).hom
            ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).hom.app L.obj ≫
            chartFrameRest X S U L frame)) =
      (schemeModulePullbackPushforwardAdjunction ((componentUnionChartIso X S U).hom ≫
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S))).homEquiv _ _
        (chartFrameRest X S U L frame) :=
    schemeModulePullbackCompIso_homEquiv _ _ _ _ _
  -- e5: the chart identification transposes to the structure map
  have e5 : (schemeModulePullbackPushforwardAdjunction (componentUnionChartIso X S U).hom).homEquiv
      _ _ ((schemeModulePullback (componentUnionChartIso X S U).hom).map
          (chartFrameInner X S U L frame) ≫
        (schemeModulePullbackUnitIso (componentUnionChartIso X S U).hom).hom) =
      chartFrameInner X S U L frame ≫
        structureToPushforwardUnit (componentUnionChartIso X S U).hom := by
    rw [Adjunction.homEquiv_naturality_left, hu_e]
  -- e6: naturality on the right for the composite `V.ι ≫ ι`
  have e6 : (schemeModulePullbackPushforwardAdjunction
      ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        (chartFrameInner X S U L frame ≫
          structureToPushforwardUnit (componentUnionChartIso X S U).hom) =
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        (chartFrameInner X S U L frame) ≫
      (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom) :=
    Adjunction.homEquiv_naturality_right _ _ _
  -- e7: the third composition comparison
  have e7 : (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction
        (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).homEquiv _ _
        ((schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι
          (componentUnionInclusion X S)).hom.app L.obj ≫ chartFrameInner X S U L frame)) =
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        (chartFrameInner X S U L frame) :=
    schemeModulePullbackCompIso_homEquiv _ _ _ _ _
  -- e8: the frame followed by the structure map
  have e8 : (schemeModulePullbackPushforwardAdjunction
      (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).homEquiv _ _
        ((schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).map frame.hom ≫
          (schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).hom) =
      frame.hom ≫ structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ U.1).ι := by
    rw [Adjunction.homEquiv_naturality_left, hu_V]
  -- e9: naturality on the right for `ι`
  have e9 : (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _
      (frame.hom ≫ structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ U.1).ι) =
      componentFrameTranspose X S L frame ≫
        (schemeModulePushforward (componentUnionInclusion X S)).map
          (structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ U.1).ι) :=
    Adjunction.homEquiv_naturality_right _ _ _
  have s5 := congrArg
    (fun z : (schemeModulePullback (componentUnionChartIso X S U).hom).obj
        ((schemeModulePullback ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
          componentUnionInclusion X S)).obj L.obj) ⟶
        _root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf =>
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (componentUnionChartIso X S U).hom).homEquiv _ _ z))
    (compIso_hom_app_chartFrameRest X S U L frame)
  have s6 := congrArg
    (fun z : (schemeModulePullback ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).obj L.obj ⟶
        (schemeModulePushforward (componentUnionChartIso X S U).hom).obj
          (_root_.SheafOfModules.unit
            (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf) =>
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S)).homEquiv _ _ z)
    e5
  have s8 := congrArg
    (fun z : L.obj ⟶ (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).obj
        (_root_.SheafOfModules.unit
          (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme.ringCatSheaf) =>
      z ≫ (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom)) e7.symm
  have s9 := congrArg
    (fun z : (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).obj
        ((schemeModulePullback (componentUnionInclusion X S)).obj L.obj) ⟶
        _root_.SheafOfModules.unit
          (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme.ringCatSheaf =>
      (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).homEquiv _ _ z) ≫
      (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom))
    (compIso_hom_app_chartFrameInner X S U L frame)
  have s10 := congrArg
    (fun z : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ⟶
        (schemeModulePushforward (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).obj
          (_root_.SheafOfModules.unit
            (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme.ringCatSheaf) =>
      (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _ z ≫
      (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom)) e8
  have s11 := congrArg
    (fun z : L.obj ⟶ (schemeModulePushforward (componentUnionInclusion X S)).obj
        ((schemeModulePushforward (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).obj
          (_root_.SheafOfModules.unit
            (componentUnionInclusion X S ⁻¹ᵁ U.1).toScheme.ringCatSheaf)) =>
      z ≫ (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom)) e9
  exact e4.symm.trans (s5.trans (s6.trans (e6.trans (s8.trans (s9.trans (s10.trans s11))))))

set_option maxHeartbeats 800000 in
/-- Identification (c) in adjunction form: the double transpose of the affine chart
frame (along the affine closed immersion, then along `fromSpec`), pushed forward
through `closedComponentInclusion_fromSpec`, is the transpose of the global frame
pushed forward to the piece `Z_S ∩ U ≅ Spec (Γ(X,U) ⧸ I_S)`. The budget (the
project's accepted scoped level) covers the strict pushforward-composition
unification in the statement. -/
theorem componentChartFrame_transpose :
    (schemeModulePullbackPushforwardAdjunction U.2.fromSpec).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).homEquiv _ _
          (componentChartFrame X S U L frame).hom) ≫
      (eqToIso (congrArg schemeModulePushforward (closedComponentInclusion_fromSpec X S U))).hom.app
        (_root_.SheafOfModules.unit
          (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf) =
    (componentFrameTranspose X S L frame ≫
      (schemeModulePushforward (componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ U.1).ι)) ≫
      (schemeModulePushforward ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫
        componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionChartIso X S U).hom) :=
  (componentChartFrame_transpose_aux₁ X S U L frame).trans
    (componentChartFrame_transpose_aux₂ X S U L frame)

end ChartFrameTranspose

section MatchingMaps

variable {Y : Scheme.{u}} {k : Type u} [Field k]

/-- The base field mapped into the sections over an open, through a structure morphism. -/
def schemeBaseSections (g : Y ⟶ Spec (CommRingCat.of k)) (W : Y.Opens) : k →+* Γ(Y, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop ≫
    Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom

variable (X : Scheme.{u}) [NoetherianSpace X] (C : ↥(irreducibleComponents X))

/-- The canonical closed-cover map of the structure sheaf: the two structure maps
into the pushforwards of the structure sheaves of the leaf component and of the
union of the other components. -/
def closedCoverStructureMap :
    _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (schemeModulePushforward (componentUnionInclusion X {C})).obj
          (_root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf) ⨯
        (schemeModulePushforward (componentUnionInclusion X ({C}ᶜ))).obj
          (_root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) :=
  prod.lift (structureToPushforwardUnit (componentUnionInclusion X {C}))
    (structureToPushforwardUnit (componentUnionInclusion X ({C}ᶜ)))

variable (L : InvertibleSheaf X)
  (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
  (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf)

/-- The canonical closed-cover map of the line bundle: the transposes of the two
component frames, the leaf factor scaled by a global section `u` of the leaf
component (to be taken as the node scalar). -/
def closedCoverFrameMap (u : Γ(componentUnionScheme X {C}, ⊤)) :
    L.obj ⟶
      (schemeModulePushforward (componentUnionInclusion X {C})).obj
          (_root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf) ⨯
        (schemeModulePushforward (componentUnionInclusion X ({C}ᶜ))).obj
          (_root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) :=
  prod.lift
    (componentFrameTranspose X {C} L frameC ≫
      (schemeModulePushforward (componentUnionInclusion X {C})).map (schemeScalarEnd u))
    (componentFrameTranspose X ({C}ᶜ) L frameC')

end MatchingMaps

end KltDP.Geometry.RationalTreePicard
