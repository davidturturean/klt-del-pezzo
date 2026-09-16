import KltDP.Geometry.ModuleOpenOver
import KltDP.Geometry.SchemeModulePullbackCoherence
import KltDP.Geometry.SchemeModuleUnitCoherence
import KltDP.Geometry.PrincipalKernelSheaf

/-!
# Original open-frame changes and their section coefficients

A scalar relation between normalized pullback frames determines the actual
Over-site coefficient after the original section-ring map. The proof uses
the original restriction/pullback adjunctions and the original unit maps.
This exposes a narrow public version of the previously reviewed private
proof slice in FrobeniusExceptionalPicardExponent. That frozen source is
unchanged; no private declaration is imported by name.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenFrameTransitionCoefficient

open SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

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
def normalizedFrameIso {X Z : Scheme.{u}} (U : X.Opens)
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
private theorem normalizedFrameIso_inv_homEquiv {X Z : Scheme.{u}} (U : X.Opens)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (q : Z ⟶ U.toScheme) :
    (schemeModulePullbackPushforwardAdjunction (q ≫ U.ι)).homEquiv M
        (_root_.SheafOfModules.unit Z.ringCatSheaf)
        (normalizedFrameIso U M e q (q ≫ U.ι) rfl).inv =
      (restrictionAdjunction U.ι).homEquiv M
        ((schemeModulePushforward q).obj (_root_.SheafOfModules.unit Z.ringCatSheaf))
        (e.inv ≫ structureToPushforwardUnit q) := by
  rw [← schemeModulePullbackCompIso_homEquiv q U.ι]
  simp only [normalizedFrameIso, Iso.trans_inv, Iso.symm_inv,
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
private theorem normalizedFrameIso_inv_app {X Z : Scheme.{u}} (U : X.Opens)
    (M : X.Modules)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (q : Z ⟶ U.toScheme) (l : Z ⟶ X) (h : q ≫ U.ι = l)
    (W : X.Opens) (hW : W ≤ U) (s : M.val.obj (op W)) :
    ((schemeModulePullbackPushforwardAdjunction l).homEquiv M
        (_root_.SheafOfModules.unit Z.ringCatSheaf)
        (normalizedFrameIso U M e q l h).inv).val.app (op W) s =
      l.app W ((openChartToOverUnitIso U M e).inv.val.app
        (op (Over.mk (homOfLE hW))) s) := by
  subst l
  rw [normalizedFrameIso_inv_homEquiv, Adjunction.homEquiv_unit]
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
theorem coefficient {X Z : Scheme.{u}} (U V W : X.Opens)
    (hWU : W ≤ U) (hWV : W ≤ V) (M : X.Modules)
    (eU : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (eV : _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅ (restriction V.ι).obj M)
    (qU : Z ⟶ U.toScheme) (qV : Z ⟶ V.toScheme) (l : Z ⟶ X)
    (hU : qU ≫ U.ι = l) (hV : qV ≫ V.ι = l)
    (hW : ⊤ ≤ l ⁻¹ᵁ W) (r : Γ(Z, ⊤))
    (he : (normalizedFrameIso V M eV qV l hV).hom =
      schemeScalarEnd r ≫ (normalizedFrameIso U M eU qU l hU).hom) :
    l.appLE W ⊤ hW
      ((openChartToOverUnitIso U M eU).inv.val.app
        (op (Over.mk (homOfLE hWU)))
        ((openChartToOverUnitIso V M eV).hom.val.app
          (op (Over.mk (homOfLE hWV))) (1 : Γ(X, W)))) = r := by
  let a := normalizedFrameIso U M eU qU l hU
  let b := normalizedFrameIso V M eV qV l hV
  have hi : a.inv = b.inv ≫ schemeScalarEnd r := by
    apply (cancel_epi b.hom).mp
    rw [Iso.hom_inv_id_assoc]
    change b.hom ≫ a.inv = _
    rw [he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let s : M.val.obj (op W) := (openChartToOverUnitIso V M eV).hom.val.app
    (op (Over.mk (homOfLE hWV))) (1 : Γ(X, W))
  have hs : (openChartToOverUnitIso V M eV).inv.val.app
      (op (Over.mk (homOfLE hWV))) s = (1 : Γ(X, W)) := by
    exact ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over V)
      (op (Over.mk (homOfLE hWV)))).mapIso
        (openChartToOverUnitIso V M eV)).toLinearEquiv.symm_apply_apply (1 : Γ(X, W))
  have H := congrArg (fun f =>
    ((schemeModulePullbackPushforwardAdjunction l).homEquiv M
      (_root_.SheafOfModules.unit Z.ringCatSheaf) f).val.app (op W) s) hi
  change ((schemeModulePullbackPushforwardAdjunction l).homEquiv M
      (_root_.SheafOfModules.unit Z.ringCatSheaf) a.inv).val.app (op W) s =
    ((schemeModulePullbackPushforwardAdjunction l).homEquiv M
      (_root_.SheafOfModules.unit Z.ringCatSheaf)
      (b.inv ≫ schemeScalarEnd r)).val.app (op W) s at H
  rw [Adjunction.homEquiv_naturality_right] at H
  change ((schemeModulePullbackPushforwardAdjunction l).homEquiv M
      (_root_.SheafOfModules.unit Z.ringCatSheaf) a.inv).val.app (op W) s =
    (schemeScalarEnd r).val.app (op (l ⁻¹ᵁ W))
      (((schemeModulePullbackPushforwardAdjunction l).homEquiv M
        (_root_.SheafOfModules.unit Z.ringCatSheaf) b.inv).val.app (op W) s) at H
  rw [normalizedFrameIso_inv_app U M eU qU l hU W hWU,
    normalizedFrameIso_inv_app V M eV qV l hV W hWV,
    hs, map_one, schemeScalarEnd_app, one_mul] at H
  have H' := congrArg (fun t : Γ(Z, l ⁻¹ᵁ W) =>
    Z.presheaf.map (homOfLE hW).op t) H
  change l.appLE W ⊤ hW
      ((openChartToOverUnitIso U M eU).inv.val.app
        (op (Over.mk (homOfLE hWU))) s) = _ at H'
  convert H' using 1
  change r = (Z.presheaf.map (homOfLE (le_top : l ⁻¹ᵁ W ≤ ⊤)).op ≫
    Z.presheaf.map (homOfLE hW).op) r
  rw [← Z.presheaf.map_comp]
  change r = Z.presheaf.map (𝟙 (op (⊤ : Z.Opens))) r
  rw [Z.presheaf.map_id]
  rfl

/-- Equality of original opens transports an actual restriction frame. -/
def frameOfOpenEq {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : U = V)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M) :
    _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ≅ (restriction V.ι).obj M :=
  h ▸ e

/-- The transported map retains its original composite with the open inclusion. -/
theorem mapOfOpenEq_ι {X Z : Scheme.{u}} {U V : X.Opens} (h : U = V)
    (q : Z ⟶ U.toScheme) :
    (q ≫ eqToHom (congrArg (fun W : X.Opens => W.toScheme) h)) ≫ V.ι = q ≫ U.ι := by
  subst V
  simp only [eqToHom_refl, Category.comp_id]

/-- Transport along equality of original opens preserves the normalized actual frame. -/
theorem normalizedFrameIso_frameOfOpenEq {X Z : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : U = V)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    (q : Z ⟶ U.toScheme) (l : Z ⟶ X) (hU : q ≫ U.ι = l)
    (hV : (q ≫ eqToHom (congrArg (fun W : X.Opens => W.toScheme) h)) ≫ V.ι = l) :
    normalizedFrameIso V M (frameOfOpenEq M h e)
      (q ≫ eqToHom (congrArg (fun W : X.Opens => W.toScheme) h)) l hV =
        normalizedFrameIso U M e q l hU := by
  subst V
  simp only [frameOfOpenEq, eqToHom_refl, Category.comp_id]

end KltDP.Geometry.OpenFrameTransitionCoefficient
