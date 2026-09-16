import KltDP.Examples.FrobeniusExceptionalFrameTransition
import KltDP.Geometry.ProjectiveLinePicardExponent
import KltDP.Geometry.OpenFrameTransitionCoefficient

/-!
# Original exceptional frames on the standard projective-line atlas

The original Rees-equation frames are transported through the actual
chart isomorphisms to the original standard opens. They give an actual
Over-site atlas, actual extracted transition units and an actual recovery
isomorphism. The original Picard exponent can therefore be computed from
these units, without assuming a cocycle presentation of the conormal.

The original adjunctions identify the extracted unit with the proved
Laurent frame change. The original Proj overlap maps then identify it
with the existing ratio section, giving the actual conormal Picard value
one. No divisor degree, self-intersection, or O(1) identification is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusExceptionalPicardExponent

open KltDP.Geometry SchemeModuleRestriction
open FrobeniusExceptionalProjectiveLine FrobeniusExceptionalLine
open ProjectiveLineComparison ProjectiveLineTransitionExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private def chartOpenIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (hU : f.opensRange = U) : Y ≅ U.toScheme :=
  f.isoOpensRange ≪≫ X.isoOfEq hU

private theorem chartOpenIso_hom_ι {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U) :
    (chartOpenIso f U hU).hom ≫ U.ι = f := by
  simp only [chartOpenIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]

private theorem chartOpenIso_inv_comp {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U) :
    (chartOpenIso f U hU).inv ≫ f = U.ι := by
  simp only [chartOpenIso, Iso.trans_inv, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, Scheme.isoOfEq_inv_ι]

/-- An original frame along an open chart becomes a frame on its actual
image open through the original unit and composition comparisons. -/
private def frameOnImageOpen {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (U : X.Opens) (hU : f.opensRange = U) (M : X.Modules)
    (e : _root_.SheafOfModules.unit Y.ringCatSheaf ≅ (schemeModulePullback f).obj M) :
    _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M :=
  (schemeModulePullbackUnitIso (chartOpenIso f U hU).inv).symm ≪≫
    (schemeModulePullback (chartOpenIso f U hU).inv).mapIso e ≪≫
      (schemeModulePullbackCompIso (chartOpenIso f U hU).inv f).app M ≪≫
        (eqToIso (congrArg schemeModulePullback (chartOpenIso_inv_comp f U hU))).app M ≪≫
          ((restrictionIsoPullback U.ι).app M).symm

/-- The transported frame retains the original normalized pullback map. -/
private theorem frameOnImageOpen_comparison {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit Y.ringCatSheaf ≅ (schemeModulePullback f).obj M) :
    (frameOnImageOpen f U hU M e).hom ≫ (restrictionIsoPullback U.ι).hom.app M =
      schemeModulePullbackFrame (chartOpenIso f U hU).inv e.hom ≫
        (schemeModulePullbackCompIso (chartOpenIso f U hU).inv f).hom.app M ≫
          (eqToIso (congrArg schemeModulePullback (chartOpenIso_inv_comp f U hU))).hom.app M := by
  simp only [frameOnImageOpen, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, schemeModulePullbackFrame]

private theorem frameComposite_congr {X Y Z : Scheme.{u}}
    {g g' : Z ⟶ Y} (hg : g = g') (f : Y ⟶ X) (l : Z ⟶ X)
    (hl : g ≫ f = l) (hl' : g' ≫ f = l) (M : X.Modules)
    (s : _root_.SheafOfModules.unit Y.ringCatSheaf ⟶ (schemeModulePullback f).obj M) :
    schemeModulePullbackFrame g s ≫ (schemeModulePullbackCompIso g f).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hl)).hom.app M =
      schemeModulePullbackFrame g' s ≫ (schemeModulePullbackCompIso g' f).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hl')).hom.app M := by
  subst g'
  rfl

private theorem imageOpenComposite {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (z : Z ⟶ Y) (l : Z ⟶ X) (hz : z ≫ f = l) :
    (z ≫ (chartOpenIso f U hU).hom) ≫ U.ι = l := by
  rw [Category.assoc, chartOpenIso_hom_ι, hz]

/-- Pulling the transported original open frame to another actual chart,
then using the original composition comparison. -/
private def frameFromImageOpen {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit Y.ringCatSheaf ≅ (schemeModulePullback f).obj M)
    (z : Z ⟶ Y) (l : Z ⟶ X) (hz : z ≫ f = l) :
    _root_.SheafOfModules.unit Z.ringCatSheaf ⟶ (schemeModulePullback l).obj M :=
  schemeModulePullbackFrame (z ≫ (chartOpenIso f U hU).hom)
      ((frameOnImageOpen f U hU M e).hom ≫ (restrictionIsoPullback U.ι).hom.app M) ≫
    (schemeModulePullbackCompIso (z ≫ (chartOpenIso f U hU).hom) U.ι).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback (imageOpenComposite f U hU z l hz))).hom.app M

/-- The new open-frame route is exactly the original chart-frame route.
Only the actual chart isomorphism and original composition maps cancel. -/
private theorem frameFromImageOpen_eq {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit Y.ringCatSheaf ≅ (schemeModulePullback f).obj M)
    (z : Z ⟶ Y) (l : Z ⟶ X) (hz : z ≫ f = l) :
    frameFromImageOpen f U hU M e z l hz =
      schemeModulePullbackFrame z e.hom ≫ (schemeModulePullbackCompIso z f).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hz)).hom.app M := by
  have hq : (z ≫ (chartOpenIso f U hU).hom) ≫ (chartOpenIso f U hU).inv = z := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold frameFromImageOpen
  rw [frameOnImageOpen_comparison]
  refine (schemeModulePullbackFrame_flatten
    (z ≫ (chartOpenIso f U hU).hom) (chartOpenIso f U hU).inv f U.ι l
    (chartOpenIso_inv_comp f U hU) (imageOpenComposite f U hU z l hz) e.hom).trans ?_
  exact frameComposite_congr hq f l
    ((congrArg (fun q : Z ⟶ Y => q ≫ f) hq).trans hz) hz M e.hom

/-- The inverse of the original restriction comparison is normalized by
the original two adjunctions. -/
private theorem restriction_homEquiv_inv {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (N : Y.Modules)
    (a : (restriction f).obj M ⟶ N) :
    (schemeModulePullbackPushforwardAdjunction f).homEquiv M N
        ((restrictionIsoPullback f).inv.app M ≫ a) =
      (restrictionAdjunction f).homEquiv M N a := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (restrictionAdjunction f) (schemeModulePullbackPushforwardAdjunction f) M
  have hn := (restrictionAdjunction f).homEquiv_naturality_right
    ((restrictionIsoPullback f).hom.app M)
    ((restrictionIsoPullback f).inv.app M ≫ a)
  change (restrictionAdjunction f).homEquiv _ _
      ((restrictionIsoPullback f).hom.app M) =
    (schemeModulePullbackPushforwardAdjunction f).unit.app M at h
  rw [h, ← Adjunction.homEquiv_unit] at hn
  simpa only [Iso.hom_inv_id_app_assoc] using hn.symm

/-- An original standard-open frame, normalized on an actual morphism
into that open. Every comparison is one of the original scheme maps. -/
private def normalizedOpenFrameIso {X Z : Scheme.{u}} (U : X.Opens)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (q : Z ⟶ U.toScheme) (l : Z ⟶ X) (h : q ≫ U.ι = l) :
    _root_.SheafOfModules.unit Z.ringCatSheaf ≅ (schemeModulePullback l).obj M :=
  (schemeModulePullbackUnitIso q).symm ≪≫
    (schemeModulePullback q).mapIso (e ≪≫ (restrictionIsoPullback U.ι).app M) ≪≫
      (schemeModulePullbackCompIso q U.ι).app M ≪≫
        (eqToIso (congrArg schemeModulePullback h)).app M

/-- Adjoining the inverse frame removes the canonical pullback
comparisons and leaves the original restriction adjunction. -/
private theorem normalizedOpenFrameIso_inv_homEquiv {X Z : Scheme.{u}} (U : X.Opens)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (q : Z ⟶ U.toScheme) :
    (schemeModulePullbackPushforwardAdjunction (q ≫ U.ι)).homEquiv M
        (_root_.SheafOfModules.unit Z.ringCatSheaf)
        (normalizedOpenFrameIso U M e q (q ≫ U.ι) rfl).inv =
      (restrictionAdjunction U.ι).homEquiv M
        ((schemeModulePushforward q).obj (_root_.SheafOfModules.unit Z.ringCatSheaf))
        (e.inv ≫ structureToPushforwardUnit q) := by
  rw [← schemeModulePullbackCompIso_homEquiv q U.ι]
  simp only [normalizedOpenFrameIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, eqToIso_refl, Iso.app_inv, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [schemeModulePullbackUnitIso, asIso_hom]
  rw [schemeModuleUnit_homEquiv, Category.assoc, restriction_homEquiv_inv]

/-- Evaluating an inverse open frame on the Over site uses the original
inverse structure map and the original image-preimage section restriction. -/
private theorem openChartToOverUnitIso_inv_app {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (W : X.Opens) (hW : W ≤ U) (s : M.val.obj (op W)) :
    (U.ι.app W)
        ((openChartToOverUnitIso U M e).inv.val.app
          (op (Over.mk (homOfLE hW))) s) =
      e.inv.val.app (op (U.ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset U.ι.base (W : Set X))).op s) := by
  letI : IsIso (U.ι.app W) := Scheme.Hom.isIso_app U.ι W (by simpa using hW)
  change (asIso (U.ι.app W)).hom
      ((asIso (U.ι.app W)).inv
        (e.inv.val.app (op (U.ι ⁻¹ᵁ W))
          (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
            (Set.image_preimage_subset U.ι.base (W : Set X))).op s))) = _
  exact Iso.inv_hom_id_apply _ _

/-- The inverse normalized pullback frame has exactly the original
Over-site section coordinates after the actual structural ring map. -/
private theorem normalizedOpenFrameIso_inv_app {X Z : Scheme.{u}} (U : X.Opens)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (q : Z ⟶ U.toScheme) (l : Z ⟶ X) (h : q ≫ U.ι = l)
    (W : X.Opens) (hW : W ≤ U) (s : M.val.obj (op W)) :
    ((schemeModulePullbackPushforwardAdjunction l).homEquiv M
        (_root_.SheafOfModules.unit Z.ringCatSheaf)
        (normalizedOpenFrameIso U M e q l h).inv).val.app (op W) s =
      l.app W ((openChartToOverUnitIso U M e).inv.val.app
        (op (Over.mk (homOfLE hW))) s) := by
  subst l
  rw [normalizedOpenFrameIso_inv_homEquiv, Adjunction.homEquiv_unit]
  change q.app (U.ι ⁻¹ᵁ W)
      (e.inv.val.app (op (U.ι ⁻¹ᵁ W))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W) (y := W)
          (Set.image_preimage_subset U.ι.base (W : Set X))).op s)) =
    q.app (U.ι ⁻¹ᵁ W)
      (U.ι.app W ((openChartToOverUnitIso U M e).inv.val.app
        (op (Over.mk (homOfLE hW))) s))
  rw [openChartToOverUnitIso_inv_app]

/-- A proved scalar change of the actual normalized frames gives the
same scalar after the original section-ring map. This is a consequence
of the original adjunctions, rather than an assumed atlas comparison. -/
private theorem openFrame_coefficient {X Z : Scheme.{u}} (U V W : X.Opens)
    (hWU : W ≤ U) (hWV : W ≤ V) (M : X.Modules)
    (eU : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (eV : _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅ (restriction V.ι).obj M)
    (qU : Z ⟶ U.toScheme) (qV : Z ⟶ V.toScheme) (l : Z ⟶ X)
    (hU : qU ≫ U.ι = l) (hV : qV ≫ V.ι = l)
    (hW : ⊤ ≤ l ⁻¹ᵁ W) (r : Γ(Z, ⊤))
    (he : (normalizedOpenFrameIso V M eV qV l hV).hom =
      schemeScalarEnd r ≫ (normalizedOpenFrameIso U M eU qU l hU).hom) :
    l.appLE W ⊤ hW
      ((openChartToOverUnitIso U M eU).inv.val.app
        (op (Over.mk (homOfLE hWU)))
        ((openChartToOverUnitIso V M eV).hom.val.app
          (op (Over.mk (homOfLE hWV))) (1 : Γ(X, W)))) = r := by
  exact KltDP.Geometry.OpenFrameTransitionCoefficient.coefficient
    U V W hWU hWV M eU eV qU qV l hU hV hW r he

variable {k : Type u} [Field k]

/-- The original first exceptional chart has the actual first standard open as image. -/
theorem leftToProjectiveLine_opensRange :
    (leftToProjectiveLine (k := k)).opensRange = chartOpen k 0 :=
  (Scheme.Hom.opensRange_comp_of_isIso (leftChartIso (k := k)).hom
    (chartImmersion k 0)).trans (chartImmersion_opensRange k 0)

/-- The original second exceptional chart has the second standard open as image. -/
theorem rightToProjectiveLine_opensRange :
    (rightToProjectiveLine (k := k)).opensRange = chartOpen k 1 :=
  (Scheme.Hom.opensRange_comp_of_isIso (rightChartIso (k := k)).hom
    (chartImmersion k 1)).trans (chartImmersion_opensRange k 1)

/-- The original u-equation frame, now on the actual first standard open. -/
def leftOpenFrame :
    _root_.SheafOfModules.unit (chartOpen k 0).toScheme.ringCatSheaf ≅
      (restriction (chartOpen k 0).ι).obj (conormalLine (k := k)).obj :=
  frameOnImageOpen leftToProjectiveLine (chartOpen k 0) leftToProjectiveLine_opensRange
    conormalLine.obj FrobeniusExceptionalChartFrames.leftFrameIso

/-- The original v-equation frame on the actual second standard open. -/
def rightOpenFrame :
    _root_.SheafOfModules.unit (chartOpen k 1).toScheme.ringCatSheaf ≅
      (restriction (chartOpen k 1).ι).obj (conormalLine (k := k)).obj :=
  frameOnImageOpen rightToProjectiveLine (chartOpen k 1) rightToProjectiveLine_opensRange
    conormalLine.obj FrobeniusExceptionalChartFrames.rightFrameIso

open FrobeniusBlowupContact KltDP.Geometry.AffineBlowup

/-- The original left open frame on the actual exceptional overlap. -/
def leftOpenOverlapFrame :
    _root_.SheafOfModules.unit
      (exceptionalOverlapScheme (centerIdeal (k := k)) centerU centerV).ringCatSheaf ⟶
        (schemeModulePullback FrobeniusExceptionalChartFrames.overlapToProjectiveLine).obj
          (conormalLine (k := k)).obj :=
  frameFromImageOpen leftToProjectiveLine (chartOpen k 0) leftToProjectiveLine_opensRange
    conormalLine.obj FrobeniusExceptionalChartFrames.leftFrameIso
    (exceptionalOverlapLeftMorphism (centerIdeal (k := k)) centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine rfl

/-- The same normalization of the original right open frame. -/
def rightOpenOverlapFrame :
    _root_.SheafOfModules.unit
      (exceptionalOverlapScheme (centerIdeal (k := k)) centerU centerV).ringCatSheaf ⟶
        (schemeModulePullback FrobeniusExceptionalChartFrames.overlapToProjectiveLine).obj
          (conormalLine (k := k)).obj :=
  frameFromImageOpen rightToProjectiveLine (chartOpen k 1) rightToProjectiveLine_opensRange
    conormalLine.obj FrobeniusExceptionalChartFrames.rightFrameIso
    (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine_right.symm

theorem leftOpenOverlapFrame_eq :
    leftOpenOverlapFrame (k := k) = FrobeniusExceptionalChartFrames.leftOverlapFrameIso.hom := by
  simpa only [leftOpenOverlapFrame, FrobeniusExceptionalChartFrames.leftOverlapFrameIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, schemeModulePullbackFrame,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.assoc] using
    frameFromImageOpen_eq leftToProjectiveLine (chartOpen k 0) leftToProjectiveLine_opensRange
      conormalLine.obj FrobeniusExceptionalChartFrames.leftFrameIso
      (exceptionalOverlapLeftMorphism (centerIdeal (k := k)) centerU centerV)
      FrobeniusExceptionalChartFrames.overlapToProjectiveLine rfl

-- Normalize the original frame composition before specializing the exceptional charts.
private theorem frameFromImageOpen_eq_iso_hom {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit Y.ringCatSheaf ≅ (schemeModulePullback f).obj M)
    (z : Z ⟶ Y) (l : Z ⟶ X) (hz : z ≫ f = l) :
    frameFromImageOpen f U hU M e z l hz =
      ((schemeModulePullbackUnitIso z).symm ≪≫
        (schemeModulePullback z).mapIso e ≪≫
          (schemeModulePullbackCompIso z f).app M ≪≫
            (eqToIso (congrArg schemeModulePullback hz)).app M).hom := by
  rw [frameFromImageOpen_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    schemeModulePullbackFrame, Category.assoc]

theorem rightOpenOverlapFrame_eq :
    rightOpenOverlapFrame (k := k) = FrobeniusExceptionalChartFrames.rightOverlapFrameIso.hom := by
  exact frameFromImageOpen_eq_iso_hom rightToProjectiveLine (chartOpen k 1)
    rightToProjectiveLine_opensRange conormalLine.obj
    FrobeniusExceptionalChartFrames.rightFrameIso
    (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine_right.symm

/-- These transported standard-open frames retain the proved original
Laurent transition on the actual exceptional overlap. -/
theorem openOverlapFrames_laurent :
    rightOpenOverlapFrame (k := k) =
      schemeScalarEnd
        ((Scheme.ΓSpecIso (CommRingCat.of
          (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv
            ((FrobeniusExceptionalOverlap.exceptionalOverlapLaurentEquiv (k := k)).symm
              (LaurentPolynomial.T 1))) ≫ leftOpenOverlapFrame (k := k) := by
  rw [leftOpenOverlapFrame_eq, rightOpenOverlapFrame_eq,
    ← FrobeniusExceptionalFrameTransition.actualOverlapFrameChange_laurent]
  exact FrobeniusExceptionalChartFrames.actualOverlapFrameChange_hom_leftFrame.symm

/-- The two actual frames, indexed by the original standard charts. -/
def originalOpenFrame (i : Fin 2) :
    _root_.SheafOfModules.unit (chartOpen k i).toScheme.ringCatSheaf ≅
      (restriction (chartOpen k i).ι).obj (conormalLine (k := k)).obj := by
  exact Fin.cases
    (motive := fun j : Fin 2 =>
      _root_.SheafOfModules.unit (chartOpen k j).toScheme.ringCatSheaf ≅
        (restriction (chartOpen k j).ι).obj (conormalLine (k := k)).obj)
    (leftOpenFrame (k := k))
    (Fin.cases
      (motive := fun j : Fin 1 =>
        _root_.SheafOfModules.unit (chartOpen k j.succ).toScheme.ringCatSheaf ≅
          (restriction (chartOpen k j.succ).ι).obj (conormalLine (k := k)).obj)
      (rightOpenFrame (k := k)) (fun j => Fin.elim0 j)) i

/-- The atlas is constructed from the original equation frames and the
proved standard-open cover, with no chosen affine-line trivializations. -/
def originalAtlas : KltDP.SheafOfModules.LocalTrivializations
    (R := (projectiveSpace k 1).ringCatSheaf) (conormalLine (k := k)).obj :=
  localTrivializationsOfOpenCharts conormalLine.obj (standardOpens k)
    (fun x => by
      have hx : x ∈ ⨆ i : ULift.{u} (Fin 2), standardOpens k i := by
        rw [ProjectiveLineSheafExponent.standardCover k conormalLine]
        trivial
      exact Opens.mem_iSup.mp hx)
    (fun i => originalOpenFrame i.down)

/-- Its chart objects are exactly the original standard opens. -/
theorem originalAtlas_X (i : ULift.{u} (Fin 2)) :
    (originalAtlas (k := k)).X i = standardOpens k i := rfl

/-- Extracting unit coordinates cancels only the actual singleton-free
comparison used to express the original open frame on the Over site. -/
theorem originalAtlas_unitIso_hom (i : ULift.{u} (Fin 2)) :
    ((originalAtlas (k := k)).unitIso i).hom =
      (openChartToOverUnitIso (standardOpens k i) conormalLine.obj
        (originalOpenFrame i.down)).inv := by
  simp only [originalAtlas, KltDP.SheafOfModules.LocalTrivializations.unitIso,
    localTrivializationsOfOpenCharts, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem originalAtlas_unitIso_inv (i : ULift.{u} (Fin 2)) :
    ((originalAtlas (k := k)).unitIso i).inv =
      (openChartToOverUnitIso (standardOpens k i) conormalLine.obj
        (originalOpenFrame i.down)).hom := by
  exact (Iso.inv_eq_inv ((originalAtlas (k := k)).unitIso i)
    (openChartToOverUnitIso (standardOpens k i) conormalLine.obj
      (originalOpenFrame i.down)).symm).mpr (originalAtlas_unitIso_hom (k := k) i)

/-- The actual section-ring units extracted from the original conormal atlas. -/
def originalUnits : ∀ i j : ULift.{u} (Fin 2),
    Γ(projectiveSpace k 1, standardOpens k i ⊓ standardOpens k j)ˣ :=
  TransitionUnitExtraction.transitionUnits (projectiveSpace k 1) conormalLine.obj originalAtlas

/-- The extracted original units satisfy the actual cocycle identities. -/
theorem originalUnits_isCocycle :
    TransitionUnitGluing.IsCocycle (projectiveSpace k 1) (standardOpens k)
      (originalUnits (k := k)) :=
  TransitionUnitExtraction.transitionUnits_isCocycle (projectiveSpace k 1)
    conormalLine.obj originalAtlas

/-- The actual original conormal is recovered from these extracted units. -/
def originalRecoveryIso : (conormalLine (k := k)).obj ≅
    TransitionUnitGluing.moduleSheaf (projectiveSpace k 1) (standardOpens k) originalUnits :=
  TransitionUnitExtraction.recoveryIso (projectiveSpace k 1) conormalLine.obj originalAtlas

/-- The existing conormal exponent is computed by its original equation atlas. -/
theorem conormalExponent_eq_originalCocycle :
    ProjectiveLineSheafExponent.exponent k (conormalLine (k := k)) =
      cocycleExponent k (originalUnits (k := k)) :=
  ProjectiveLineSheafExponent.exponent_eq_of_iso_to_glued k conormalLine originalUnits
    originalUnits_isCocycle originalRecoveryIso

/-- The original Picard class uses this same actual conormal atlas exponent. -/
theorem picardValue_eq_originalCocycle :
    ProjectiveLinePicardExponent.value k (conormalLine (k := k)).toPic =
      cocycleExponent k (originalUnits (k := k)) := by
  rw [ProjectiveLinePicardExponent.value_toPic, conormalExponent_eq_originalCocycle]

private def overlapLeftToOpen :
    exceptionalOverlapScheme (centerIdeal (k := k)) centerU centerV ⟶
      (chartOpen k 0).toScheme :=
  exceptionalOverlapLeftMorphism centerIdeal centerU centerV ≫
    (chartOpenIso leftToProjectiveLine (chartOpen k 0)
      leftToProjectiveLine_opensRange).hom

private def overlapRightToOpen :
    exceptionalOverlapScheme (centerIdeal (k := k)) centerU centerV ⟶
      (chartOpen k 1).toScheme :=
  exceptionalOverlapRightMorphism centerIdeal centerU centerV ≫
    (chartOpenIso rightToProjectiveLine (chartOpen k 1)
      rightToProjectiveLine_opensRange).hom

private theorem overlapLeftToOpen_ι :
    overlapLeftToOpen (k := k) ≫ (chartOpen k 0).ι =
      FrobeniusExceptionalChartFrames.overlapToProjectiveLine :=
  imageOpenComposite leftToProjectiveLine (chartOpen k 0) leftToProjectiveLine_opensRange
    (exceptionalOverlapLeftMorphism centerIdeal centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine rfl

private theorem overlapRightToOpen_ι :
    overlapRightToOpen (k := k) ≫ (chartOpen k 1).ι =
      FrobeniusExceptionalChartFrames.overlapToProjectiveLine :=
  imageOpenComposite rightToProjectiveLine (chartOpen k 1) rightToProjectiveLine_opensRange
    (exceptionalOverlapRightMorphism centerIdeal centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine_right.symm

private theorem overlap_preimage_top :
    ⊤ ≤ (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)) ⁻¹ᵁ
      ProjectiveLineSections.overlapOpen k := by
  intro x hx
  rw [ProjectiveLineSections.overlapOpen_eq_inf]
  constructor
  · change (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).base x ∈
      chartOpen k 0
    rw [← overlapLeftToOpen_ι]
    exact ((overlapLeftToOpen (k := k)).base x).property
  · change (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).base x ∈
      chartOpen k 1
    rw [← overlapRightToOpen_ι]
    exact ((overlapRightToOpen (k := k)).base x).property

set_option maxRecDepth 4096 in
private theorem originalUnits_overlap_value :
    (overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩) :
      Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k)) =
      (openChartToOverUnitIso (chartOpen k 0) conormalLine.obj leftOpenFrame).inv.val.app
        (op (Over.mk (homOfLE (ProjectiveLineSections.overlapOpen_le_left k))))
        ((openChartToOverUnitIso (chartOpen k 1) conormalLine.obj rightOpenFrame).hom.val.app
          (op (Over.mk (homOfLE (ProjectiveLineSections.overlapOpen_le_right k))))
          (1 : Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k))) := by
  conv =>
    lhs
    simp only [overlapRestriction, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, originalUnits, TransitionUnitExtraction.transitionUnits]
  rw [TransitionUnitExtraction.transitionUnitOn_restrict]
  simp only [TransitionUnitExtraction.transitionUnitOn, KltDP.Module.transitionUnit_val,
    TransitionUnitExtraction.chartEquiv_apply, TransitionUnitExtraction.chartEquiv_symm_apply,
    originalAtlas_unitIso_hom, originalAtlas_unitIso_inv]
  rfl

-- The two presentations use the same unit, pullback, restriction and composition maps.
private theorem normalizedOpenFrameIso_image_eq {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit Y.ringCatSheaf ≅ (schemeModulePullback f).obj M)
    (z : Z ⟶ Y) (l : Z ⟶ X) (hz : z ≫ f = l) :
    (normalizedOpenFrameIso U M (frameOnImageOpen f U hU M e)
      (z ≫ (chartOpenIso f U hU).hom) l (imageOpenComposite f U hU z l hz)).hom =
        frameFromImageOpen f U hU M e z l hz := by
  simp only [normalizedOpenFrameIso, frameFromImageOpen, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, schemeModulePullbackFrame, Category.assoc]

private theorem normalized_leftOpenOverlapFrame :
    (normalizedOpenFrameIso (chartOpen k 0) conormalLine.obj leftOpenFrame
      overlapLeftToOpen FrobeniusExceptionalChartFrames.overlapToProjectiveLine
      overlapLeftToOpen_ι).hom = leftOpenOverlapFrame (k := k) := by
  exact normalizedOpenFrameIso_image_eq leftToProjectiveLine (chartOpen k 0)
    leftToProjectiveLine_opensRange conormalLine.obj
    FrobeniusExceptionalChartFrames.leftFrameIso
    (exceptionalOverlapLeftMorphism (centerIdeal (k := k)) centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine rfl

private theorem normalized_rightOpenOverlapFrame :
    (normalizedOpenFrameIso (chartOpen k 1) conormalLine.obj rightOpenFrame
      overlapRightToOpen FrobeniusExceptionalChartFrames.overlapToProjectiveLine
      overlapRightToOpen_ι).hom = rightOpenOverlapFrame (k := k) := by
  exact normalizedOpenFrameIso_image_eq rightToProjectiveLine (chartOpen k 1)
    rightToProjectiveLine_opensRange conormalLine.obj
    FrobeniusExceptionalChartFrames.rightFrameIso
    (exceptionalOverlapRightMorphism (centerIdeal (k := k)) centerU centerV)
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine_right.symm

/-- The actual extracted transition, mapped along the original exceptional
overlap morphism, is the original Laurent-T scalar on that overlap. -/
theorem originalUnits_overlap_pullback :
    (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
      (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top
      (overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩) :
        Γ(projectiveSpace k 1, ProjectiveLineSections.overlapOpen k)) =
      (Scheme.ΓSpecIso (CommRingCat.of
        (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv
          ((FrobeniusExceptionalOverlap.exceptionalOverlapLaurentEquiv (k := k)).symm
            (LaurentPolynomial.T 1)) := by
  rw [originalUnits_overlap_value]
  apply openFrame_coefficient (chartOpen k 0) (chartOpen k 1)
    (ProjectiveLineSections.overlapOpen k)
    (ProjectiveLineSections.overlapOpen_le_left k)
    (ProjectiveLineSections.overlapOpen_le_right k) conormalLine.obj
    leftOpenFrame rightOpenFrame overlapLeftToOpen overlapRightToOpen
    FrobeniusExceptionalChartFrames.overlapToProjectiveLine
    overlapLeftToOpen_ι overlapRightToOpen_ι overlap_preimage_top
  rw [normalized_rightOpenOverlapFrame, normalized_leftOpenOverlapFrame]
  exact openOverlapFrames_laurent

attribute [local instance] MvPolynomial.gradedAlgebra

private def projectiveOverlapOpenIso :
    (ProjectiveLineSections.overlapOpen k).toScheme ≅
      Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)) :=
  Proj.basicOpenIsoSpec (grading k)
    ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X k (0 : Fin 2))
      (MvPolynomial.isHomogeneous_X k (1 : Fin 2))) (by decide)

private def exceptionalOverlapOpenIso :
    exceptionalOverlapScheme (centerIdeal (k := k)) centerU centerV ≅
      (ProjectiveLineSections.overlapOpen k).toScheme :=
  overlapIso ≪≫ (projectiveOverlapOpenIso (k := k)).symm

private theorem exceptionalOverlapOpenIso_hom_ι :
    (exceptionalOverlapOpenIso (k := k)).hom ≫ (ProjectiveLineSections.overlapOpen k).ι =
      FrobeniusExceptionalChartFrames.overlapToProjectiveLine := by
  change _ = exceptionalOverlapLeftMorphism (centerIdeal (k := k)) centerU centerV ≫
    (leftChartIso.hom ≫ chartImmersion k 0)
  rw [← Category.assoc, overlapIso_left, Category.assoc]
  simpa only [exceptionalOverlapOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    toOverlapLeft, chartImmersion, projectiveOverlapOpenIso, Proj.awayι] using
    congrArg (fun f : Spec (CommRingCat.of (ProjectiveLineComparison.overlapRing k)) ⟶
        projectiveSpace k 1 => (overlapIso (k := k)).hom ≫ f)
      (Proj.SpecMap_awayMap_awayι (grading k)
        (MvPolynomial.isHomogeneous_X k (0 : Fin 2)) (by decide)
        (MvPolynomial.isHomogeneous_X k (1 : Fin 2)) rfl).symm

private theorem overlap_appLE_eq :
    (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
        (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top =
      (ProjectiveLineSections.overlapOpen k).topIso.inv ≫
        (exceptionalOverlapOpenIso (k := k)).hom.appTop := by
  have congr_appLE {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
      (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
      f.appLE U V hf = g.appLE U V hg := by
    subst g
    rfl
  have H := Scheme.appLE_comp_appLE (exceptionalOverlapOpenIso (k := k)).hom
    (ProjectiveLineSections.overlapOpen k).ι
    (ProjectiveLineSections.overlapOpen k) ⊤ ⊤
    (ProjectiveLineSections.overlapOpen k).ι_preimage_self.ge le_rfl
  have hcomp : ⊤ ≤ ((exceptionalOverlapOpenIso (k := k)).hom ≫
      (ProjectiveLineSections.overlapOpen k).ι) ⁻¹ᵁ
        ProjectiveLineSections.overlapOpen k := by
    rw [exceptionalOverlapOpenIso_hom_ι]
    exact overlap_preimage_top
  have H' := congr_appLE exceptionalOverlapOpenIso_hom_ι
    (ProjectiveLineSections.overlapOpen k) ⊤ hcomp overlap_preimage_top
  calc
    _ = ((exceptionalOverlapOpenIso (k := k)).hom ≫
        (ProjectiveLineSections.overlapOpen k).ι).appLE
          (ProjectiveLineSections.overlapOpen k) ⊤ hcomp := H'.symm
    _ = _ := by
      simpa only [Scheme.Hom.appLE_eq_app, Scheme.Opens.ι_appLE,
        Scheme.Opens.topIso_inv, eqToHom_op] using H.symm

private theorem awayToSection_overlap_appLE :
    Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) ≫
      (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
        (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top =
      CommRingCat.ofHom (overlapRingEquiv (k := k)).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of
          (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv := by
  have hc : Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) ≫
      (ProjectiveLineSections.overlapOpen k).topIso.inv =
    (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv ≫
      (projectiveOverlapOpenIso (k := k)).hom.appTop := by
    simp only [projectiveOverlapOpenIso, Proj.basicOpenIsoSpec_hom,
      Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc,
      ProjectiveLineSections.overlapOpen]
  calc
    _ = (Proj.awayToSection (grading k)
          ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1) ≫
        (ProjectiveLineSections.overlapOpen k).topIso.inv) ≫
      (projectiveOverlapOpenIso (k := k)).inv.appTop ≫
        (overlapIso (k := k)).hom.appTop := by
          simp only [overlap_appLE_eq, exceptionalOverlapOpenIso, Iso.trans_hom,
            Iso.symm_hom, Scheme.comp_appTop, Category.assoc]
    _ = (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv ≫
        ((projectiveOverlapOpenIso (k := k)).hom.appTop ≫
          (projectiveOverlapOpenIso (k := k)).inv.appTop) ≫
        (overlapIso (k := k)).hom.appTop := by
          simp only [hc, Category.assoc]
    _ = (Scheme.ΓSpecIso (CommRingCat.of (ProjectiveLineComparison.overlapRing k))).inv ≫
        (overlapIso (k := k)).hom.appTop := by
          simp only [← Scheme.comp_appTop, Iso.inv_hom_id, Scheme.id_appTop,
            Category.comp_id, Category.id_comp]
    _ = _ := (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (overlapRingEquiv (k := k)).toRingHom)).symm

/-- The actual section map of the exceptional overlap is inverse to the
previously constructed quotient-to-P1 section equivalence. -/
theorem overlap_appLE_overlapToSections
    (r : exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV) :
    (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
      (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top
      (overlapToSectionsEquiv r) =
      (Scheme.ΓSpecIso (CommRingCat.of
        (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv r := by
  have H := ConcreteCategory.congr_hom (awayToSection_overlap_appLE (k := k))
    ((overlapRingEquiv (k := k)).symm r)
  change (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
      (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top
      ((Proj.awayToSection (grading k)
        ((MvPolynomial.X 0 : homogeneousRing k) * MvPolynomial.X 1)).hom
          ((overlapRingEquiv (k := k)).symm r)) =
    (Scheme.ΓSpecIso (CommRingCat.of
      (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv
        ((overlapRingEquiv (k := k)) ((overlapRingEquiv (k := k)).symm r)) at H
  rw [← overlapToSectionsEquiv_overlapRing, RingEquiv.apply_symm_apply] at H
  exact H

private theorem overlap_appLE_injective : Function.Injective
    ((FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
      (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top) := by
  intro a b h
  obtain ⟨r, rfl⟩ := (overlapToSectionsEquiv (k := k)).surjective a
  obtain ⟨s, rfl⟩ := (overlapToSectionsEquiv (k := k)).surjective b
  rw [overlap_appLE_overlapToSections, overlap_appLE_overlapToSections] at h
  exact congrArg (overlapToSectionsEquiv (k := k))
    ((Scheme.ΓSpecIso (CommRingCat.of
      (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).commRingCatIsoToRingEquiv.symm.injective h)

/-- The unit extracted from the original conormal frames is the actual
quotient ratio section, with its previously proved Laurent coordinate. -/
theorem originalUnits_eq_conormalRatioSection :
    overlapRestriction k (originalUnits (k := k) ⟨0⟩ ⟨1⟩) =
      conormalRatioSection (k := k) := by
  apply Units.ext
  apply overlap_appLE_injective
  rw [originalUnits_overlap_pullback]
  change _ = (FrobeniusExceptionalChartFrames.overlapToProjectiveLine (k := k)).appLE
    (ProjectiveLineSections.overlapOpen k) ⊤ overlap_preimage_top
    (overlapToSectionsEquiv (exceptionalOverlapTransitionUnit
      (centerIdeal (k := k)) centerU centerV))
  rw [overlap_appLE_overlapToSections]
  apply congrArg (Scheme.ΓSpecIso (CommRingCat.of
    (exceptionalOverlapRing (centerIdeal (k := k)) centerU centerV))).inv
  apply (FrobeniusExceptionalOverlap.exceptionalOverlapLaurentEquiv (k := k)).injective
  rw [RingEquiv.apply_symm_apply]
  exact FrobeniusExceptionalConormal.transitionUnit_image.symm

/-- The original transported exceptional conormal has exponent one in
the existing projective-line transition convention. -/
theorem conormalExponent_eq_one :
    ProjectiveLineSheafExponent.exponent k (conormalLine (k := k)) = 1 := by
  rw [conormalExponent_eq_originalCocycle, cocycleExponent,
    originalUnits_eq_conormalRatioSection, conormalRatioSection_exponent]

/-- The existing Picard class of the original exceptional conormal has
value one. This computes that actual class, with no prescribed degree. -/
theorem conormalPicardValue_eq_one :
    ProjectiveLinePicardExponent.value k (conormalLine (k := k)).toPic = 1 := by
  rw [ProjectiveLinePicardExponent.value_toPic, conormalExponent_eq_one]

end KltDP.Examples.FrobeniusExceptionalPicardExponent
