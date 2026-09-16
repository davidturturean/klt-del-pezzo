import KltDP.Geometry.RationalTreePicardRestrictionPullbackSections
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# The transpose of the open trivialization derived from a component frame

For an open `V` of a reduced curve lying inside a component union `Z_S`, the
trivialization `componentOpenFrame` of `L|_V` is the preimage, under the pullback
along the isomorphism `Z_S ∩ V → V`, of the pulled-back frame. Its
pullback-adjunction transpose `L ⟶ (V.ι)_* O_V` is computed here by adjunction
calculus: pushed forward to the closed piece `Z_S ∩ V` it is the transpose of the
frame pushed forward to the same piece (`componentOpenFrame_transpose`). This is
route item (i) for the `leafOpen` and `complementOpen` charts of the leaf-node
atlas, in the form used by `hleafT`/`hcomplT`.

Also recorded: on an open inside a component union, a unit trivialization of `L`
is determined by its pullback along the restricted closed immersion
(`componentOpen_unitIso_ext`), which is the isomorphism there.

Not done here: the corresponding computation for the chart trivialization
`leafChartOpenUnitIso` (through `isoSpec` and the affine closed-frame descent),
and the comparison of the two transposes on the overlaps. See
`LEMMA22_PROGRESS.md` for the exact remaining equations and the assessment.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

variable (X : Scheme.{u}) [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  (S : Set ↥(irreducibleComponents X)) (V : X.Opens)
  (hV : (V : Set X) ⊆ componentClosedUnion X S) (L : InvertibleSheaf X)

include hV in
/-- On an open inside a component union, a unit trivialization is determined by its
pullback along the restricted closed immersion (an isomorphism there). -/
theorem componentOpen_unitIso_ext
    (a b : (schemeModulePullback V.ι).obj L.obj ≅
      _root_.SheafOfModules.unit V.toScheme.ringCatSheaf)
    (h : (schemeModulePullback (componentUnionInclusion X S ∣_ V)).map a.hom ≫
        (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).hom =
      (schemeModulePullback (componentUnionInclusion X S ∣_ V)).map b.hom ≫
        (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).hom) : a = b := by
  haveI : IsIso (componentUnionInclusion X S ∣_ V) :=
    componentUnionInclusion_restrict_isIso X S V hV
  exact unitIso_ext_of_pullback_isIso (componentUnionInclusion X S ∣_ V) a b h

variable (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
  _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf)

/-- The transpose of the frame along the closed immersion of the component union. -/
abbrev componentFrameTranspose :
    L.obj ⟶ (schemeModulePushforward (componentUnionInclusion X S)).obj
      (_root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :=
  (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv L.obj _
    frame.hom

/-- The last two maps of the pulled-back frame chain: the frame pulled back to the
closed piece over `V`, followed by the unit comparison. -/
def openFrameTail :
    (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ V).ι).obj
        ((schemeModulePullback (componentUnionInclusion X S)).obj L.obj) ⟶
      _root_.SheafOfModules.unit (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf :=
  (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ V).ι).map frame.hom ≫
    (schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ V).ι).hom

/-- The pulled-back frame chain after the composition comparisons of `(g, V.ι)`. -/
def openFrameRest :
    (schemeModulePullback ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫
        componentUnionInclusion X S)).obj L.obj ⟶
      _root_.SheafOfModules.unit (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf :=
  (schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ V).ι
    (componentUnionInclusion X S)).inv.app L.obj ≫ openFrameTail X S V L frame

/-- The forward map of the pulled-back frame chain, as the composition comparison,
the equality transport, and the remaining original maps. -/
theorem componentOpenFrameChain_hom :
    (componentOpenFrameChain X S V L frame).hom =
      (schemeModulePullbackCompIso (componentUnionInclusion X S ∣_ V) V.ι).hom.app L.obj ≫
        (eqToIso (congrArg (fun k => (schemeModulePullback k).obj L.obj)
          (morphismRestrict_ι (componentUnionInclusion X S) V))).hom ≫
        openFrameRest X S V L frame := rfl

/-- The composition comparison cancels against its inverse in the chain. -/
theorem compIso_hom_app_openFrameRest :
    (schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ V).ι
        (componentUnionInclusion X S)).hom.app L.obj ≫ openFrameRest X S V L frame =
      openFrameTail X S V L frame := by
  unfold openFrameRest
  exact Iso.hom_inv_id_app_assoc _ _ _

set_option maxHeartbeats 800000 in
/-- The transpose of the open trivialization, pushed forward to the closed piece
`Z_S ∩ V`, is the transpose of the frame pushed forward to the same piece. The
heartbeat budget covers the repeated strict pushforward-composition unification. -/
theorem componentOpenFrame_transpose :
    (pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame) ≫
      (schemeModulePushforward V.ι).map
        (structureToPushforwardUnit (componentUnionInclusion X S ∣_ V))) ≫
      (eqToIso (congrArg schemeModulePushforward
        (morphismRestrict_ι (componentUnionInclusion X S) V))).hom.app
        (_root_.SheafOfModules.unit
          (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf) =
    componentFrameTranspose X S L frame ≫
      (schemeModulePushforward (componentUnionInclusion X S)).map
        (structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ V).ι) := by
  have hu_g : (schemeModulePullbackPushforwardAdjunction
      (componentUnionInclusion X S ∣_ V)).homEquiv _ _
        (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).hom =
      structureToPushforwardUnit (componentUnionInclusion X S ∣_ V) :=
    schemeModulePullbackUnitHom_adjunction (componentUnionInclusion X S ∣_ V)
  have hu_j : (schemeModulePullbackPushforwardAdjunction
      (componentUnionInclusion X S ⁻¹ᵁ V).ι).homEquiv _ _
        (schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ V).ι).hom =
      structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ V).ι :=
    schemeModulePullbackUnitHom_adjunction (componentUnionInclusion X S ⁻¹ᵁ V).ι
  -- e1: the transpose composed with the structure map is a single transpose
  have e1 : pullbackTrivializationTranspose L.obj V (componentOpenFrame X S V hV L frame) ≫
      (schemeModulePushforward V.ι).map
        (structureToPushforwardUnit (componentUnionInclusion X S ∣_ V)) =
      (schemeModulePullbackPushforwardAdjunction V.ι).homEquiv _ _
        ((componentOpenFrame X S V hV L frame).hom ≫
          structureToPushforwardUnit (componentUnionInclusion X S ∣_ V)) :=
    (Adjunction.homEquiv_naturality_right _ _ _).symm
  -- e2: the pullback identity, transposed along the restricted closed immersion
  have e2 : (componentOpenFrame X S V hV L frame).hom ≫
      structureToPushforwardUnit (componentUnionInclusion X S ∣_ V) =
      (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S ∣_ V)).homEquiv _ _
        ((schemeModulePullbackCompIso (componentUnionInclusion X S ∣_ V) V.ι).hom.app L.obj ≫
          (eqToIso (congrArg (fun k => (schemeModulePullback k).obj L.obj)
            (morphismRestrict_ι (componentUnionInclusion X S) V))).hom ≫
          openFrameRest X S V L frame) := by
    rw [← componentOpenFrameChain_hom, ← componentOpenFrame_pullback X S V hV L frame,
      Adjunction.homEquiv_naturality_left, hu_g]
  -- e3: composition comparison
  have e3 : (schemeModulePullbackPushforwardAdjunction V.ι).homEquiv _ _
      ((schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S ∣_ V)).homEquiv _ _
        ((schemeModulePullbackCompIso (componentUnionInclusion X S ∣_ V) V.ι).hom.app L.obj ≫
          (eqToIso (congrArg (fun k => (schemeModulePullback k).obj L.obj)
            (morphismRestrict_ι (componentUnionInclusion X S) V))).hom ≫
          openFrameRest X S V L frame)) =
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ∣_ V) ≫ V.ι)).homEquiv _ _
        ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj L.obj)
          (morphismRestrict_ι (componentUnionInclusion X S) V))).hom ≫
          openFrameRest X S V L frame) :=
    schemeModulePullbackCompIso_homEquiv _ _ _ _ _
  -- e4: equality transport of the composite
  have e4 : (schemeModulePullbackPushforwardAdjunction
      ((componentUnionInclusion X S ∣_ V) ≫ V.ι)).homEquiv _ _
        ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj L.obj)
          (morphismRestrict_ι (componentUnionInclusion X S) V))).hom ≫
          openFrameRest X S V L frame) ≫
      (eqToIso (congrArg schemeModulePushforward
        (morphismRestrict_ι (componentUnionInclusion X S) V))).hom.app _ =
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        (openFrameRest X S V L frame) :=
    schemeModulePullback_homEquiv_eqToIso (morphismRestrict_ι (componentUnionInclusion X S) V)
      L.obj _ (openFrameRest X S V L frame)
  -- e5: the other composition comparison, with the cancelling comparison inserted
  have e5 : (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _
        ((schemeModulePullbackPushforwardAdjunction
          (componentUnionInclusion X S ⁻¹ᵁ V).ι).homEquiv _ _
          ((schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ V).ι
            (componentUnionInclusion X S)).hom.app L.obj ≫ openFrameRest X S V L frame)) =
      (schemeModulePullbackPushforwardAdjunction
        ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫ componentUnionInclusion X S)).homEquiv _ _
        (openFrameRest X S V L frame) :=
    schemeModulePullbackCompIso_homEquiv _ _ _ _ _
  -- e6: the tail transposes to the frame followed by the structure map
  have e6 : (schemeModulePullbackPushforwardAdjunction
      (componentUnionInclusion X S ⁻¹ᵁ V).ι).homEquiv _ _ (openFrameTail X S V L frame) =
      frame.hom ≫ structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ V).ι := by
    unfold openFrameTail
    rw [Adjunction.homEquiv_naturality_left, hu_j]
  -- e7: naturality on the right
  have e7 : (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _
      (frame.hom ≫ structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ V).ι) =
      componentFrameTranspose X S L frame ≫
        (schemeModulePushforward (componentUnionInclusion X S)).map
          (structureToPushforwardUnit (componentUnionInclusion X S ⁻¹ᵁ V).ι) :=
    Adjunction.homEquiv_naturality_right _ _ _
  -- assemble by transitivity; every intermediate term matches syntactically
  exact (congrArg
      (fun z : L.obj ⟶ (schemeModulePushforward V.ι).obj
          ((schemeModulePushforward (componentUnionInclusion X S ∣_ V)).obj
            (_root_.SheafOfModules.unit
              (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf)) =>
        z ≫ (eqToIso (congrArg schemeModulePushforward
          (morphismRestrict_ι (componentUnionInclusion X S) V))).hom.app
          (_root_.SheafOfModules.unit
            (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf)) e1).trans
    ((congrArg
      (fun z : (schemeModulePullback V.ι).obj L.obj ⟶
          (schemeModulePushforward (componentUnionInclusion X S ∣_ V)).obj
            (_root_.SheafOfModules.unit
              (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf) =>
        (schemeModulePullbackPushforwardAdjunction V.ι).homEquiv _ _ z ≫
          (eqToIso (congrArg schemeModulePushforward
            (morphismRestrict_ι (componentUnionInclusion X S) V))).hom.app
            (_root_.SheafOfModules.unit
              (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf)) e2).trans
    ((congrArg
      (fun z : L.obj ⟶ (schemeModulePushforward V.ι).obj
          ((schemeModulePushforward (componentUnionInclusion X S ∣_ V)).obj
            (_root_.SheafOfModules.unit
              (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf)) =>
        z ≫ (eqToIso (congrArg schemeModulePushforward
          (morphismRestrict_ι (componentUnionInclusion X S) V))).hom.app
          (_root_.SheafOfModules.unit
            (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf)) e3).trans
    (e4.trans
    (e5.symm.trans
    ((congrArg
      (fun z : (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ V).ι).obj
          ((schemeModulePullback (componentUnionInclusion X S)).obj L.obj) ⟶
          _root_.SheafOfModules.unit
            (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf =>
        (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _
          ((schemeModulePullbackPushforwardAdjunction
            (componentUnionInclusion X S ⁻¹ᵁ V).ι).homEquiv _ _ z))
      (compIso_hom_app_openFrameRest X S V L frame)).trans
    ((congrArg
      (fun z : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ⟶
          (schemeModulePushforward (componentUnionInclusion X S ⁻¹ᵁ V).ι).obj
            (_root_.SheafOfModules.unit
              (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf) =>
        (schemeModulePullbackPushforwardAdjunction (componentUnionInclusion X S)).homEquiv _ _ z)
      e6).trans e7))))))

end KltDP.Geometry.RationalTreePicard
