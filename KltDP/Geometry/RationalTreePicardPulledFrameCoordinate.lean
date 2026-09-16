import KltDP.Geometry.RationalTreePicardPulledSectionTransport

/-!
# The pulled-back frames have coordinate `1`: `PulledFrameCoordinate`, and the final statements

BRIEF17. The frame-coordinate identity `PulledFrameCoordinate` of
`RationalTreePicardPullbackGluedFrames` is proved by lane D's `hpull` method (tactic-built
isomorphisms wrapped in constants, `congrArg` and generic `rfl` steps, generic statements over a
variable module instantiated propositionally):

* the chart frame `chartFrame i` of the glued sheaf has coordinate `1` in the chart
  (`trivialization_chartFrame`, `chartIsoOn_hom_app_chartFrame`), hence the restriction-form and
  pullback-form chart trivializations send (the adjunction-unit image of / the pulled-back section of)
  the frame to `1` (`chartRestrictionIso_hom_val_app_unit`, `chartPullbackIso_hom_val_app_pulledSection`);
* generically, for a trivialization `t` of `M` on `U` sending the pulled-back section of `s` to `1`, the
  pulled-back trivialization `pulledChartIso f M U t` sends the doubly pulled-back section of `s` to `1`
  (`pulledChartIso_hom_val_app_doublePulled`): every comparison entering `pulledChartIso` transports
  pulled-back sections (the lemmas of `RationalTreePicardPulledSectionTransport`), the transport along
  the equality of preimage opens commutes with the remaining comparisons
  (`PresheafOfModules.naturality_apply`), and the structure-module comparison sends the pulled-back `1`
  to `1`;
* the chart coordinate of the pulled-back atlas is the inverse section-ring isomorphism of the
  pulled-back trivialization on the pulled-back section (`chartEquiv_pulledAtlas_apply`, through
  the accepted `chartEquiv_ofOpenCharts` and `openChartCoordinate_eq_openSectionsInv`).

Consequences: `pulledFrameCoordinate : PulledFrameCoordinate.{u}`,
`pullbackGluedClass : PullbackGluedClass.{u}`, and the unconditional surjectivity half
`multidegreeHom_surjective_final`, hence `multidegreeHom_bijective_final` and the group isomorphism
`multidegreeMulEquiv_final : X.Pic ≃* (components → Multiplicative ℤ)` for a reduced Noetherian curve
over an algebraically closed field with tree component-point incidence graph, transverse branch germs
and components identified with the projective line (`lem:tree-picard`).

Two scoped heartbeat budgets (`800000`, within the lane's documented limit) are used: for the
core identity `pulledChartIso_hom_val_app_doublePulled` (a chain of ten `congrArg`/comparison
steps on large terms) and for its restatement at the definitionally equal form of the preimage open
(`((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U` versus `(f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U)`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

open TransitionUnitGluing TransitionUnitExtraction SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section GluedChartFrame

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)

/-- The chart frame has coordinate `1` in its chart. -/
theorem trivialization_chartFrame (i : ι) :
    trivialization X U g hc i le_rfl (chartFrame U g hc i) = 1 :=
  (trivialization X U g hc i le_rfl).apply_symm_apply 1

/-- The over-site chart isomorphism sends the chart frame to `1`. -/
theorem chartIsoOn_hom_app_chartFrame (i : ι) :
    (chartIsoOn X U g hc i le_rfl).hom.val.app (overTop (U i)) (chartFrame U g hc i) =
      (1 : Γ(X, U i)) :=
  (chartIsoOn_hom_app_apply X U g hc i le_rfl (overTop (U i)) (chartFrame U g hc i)).trans
    (trivialization_chartFrame U g hc i)

/-- The restriction-form chart trivialization is the preimage of the over-site chart composite. -/
theorem openToOverFunctor_map_chartRestrictionIso_hom (i : ι) :
    (openToOverFunctor (U i)).map (chartRestrictionIso U g hc i).hom =
      (openToOverRestrictionIso (U i) (moduleSheaf X U g) ≪≫ chartIsoOn X U g hc i le_rfl ≪≫
        openToOverUnitIso (U i)).hom :=
  (openToOverFunctor (U i)).map_preimage _

/-- The restriction-form chart trivialization sends the adjunction-unit image of the chart frame
to `1`. -/
theorem chartRestrictionIso_hom_val_app_unit (i : ι) :
    (chartRestrictionIso U g hc i).hom.val.app (op ((U i).ι ⁻¹ᵁ (U i)))
        (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
          (chartFrame U g hc i)) =
      (1 : Γ((U i).toScheme, (U i).ι ⁻¹ᵁ (U i))) := by
  have h1 : (chartRestrictionIso U g hc i).hom.val.app (op ((U i).ι ⁻¹ᵁ (U i)))
      (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
        (chartFrame U g hc i)) =
      ((openToOverFunctor (U i)).map (chartRestrictionIso U g hc i).hom).val.app (overTop (U i))
        (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
          (chartFrame U g hc i)) :=
    (openToOverFunctor_map_val_app' (U i) (chartRestrictionIso U g hc i).hom
      (Over.mk (homOfLE (le_rfl : U i ≤ U i)))
      (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
        (chartFrame U g hc i))).symm
  have h2 := congrArg
    (fun q : (openToOverFunctor (U i)).obj ((restriction (U i).ι).obj (moduleSheaf X U g)) ⟶
        (openToOverFunctor (U i)).obj (_root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf) =>
      q.val.app (overTop (U i))
        (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
          (chartFrame U g hc i)))
    (openToOverFunctor_map_chartRestrictionIso_hom U g hc i)
  have h3 : (openToOverRestrictionIso (U i) (moduleSheaf X U g) ≪≫ chartIsoOn X U g hc i le_rfl ≪≫
        openToOverUnitIso (U i)).hom.val.app (overTop (U i))
        (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
          (chartFrame U g hc i)) =
      (openToOverUnitIso (U i)).hom.val.app (overTop (U i))
        ((chartIsoOn X U g hc i le_rfl).hom.val.app (overTop (U i))
          ((openToOverRestrictionIso (U i) (moduleSheaf X U g)).hom.val.app (overTop (U i))
            (((restrictionAdjunction (U i).ι).unit.app (moduleSheaf X U g)).val.app (op (U i))
              (chartFrame U g hc i)))) := rfl
  have h4 := openToOverRestrictionIso_hom_app_unit' (U i) (moduleSheaf X U g) (chartFrame U g hc i)
  have h5 := chartIsoOn_hom_app_chartFrame U g hc i
  have h6 := openToOverUnitIso_hom_app_one' (U i)
  exact h1.trans (h2.trans (h3.trans ((congrArg (fun y => (openToOverUnitIso (U i)).hom.val.app
    (overTop (U i)) ((chartIsoOn X U g hc i le_rfl).hom.val.app (overTop (U i)) y)) h4).trans
    ((congrArg (fun y => (openToOverUnitIso (U i)).hom.val.app (overTop (U i)) y) h5).trans h6))))

/-- The pullback-form chart trivialization, unfolded. -/
theorem chartPullbackIso_hom (i : ι) :
    (chartPullbackIso U g hc i).hom =
      (restrictionIsoPullback (U i).ι).inv.app (moduleSheaf X U g) ≫
        (chartRestrictionIso U g hc i).hom := rfl

/-- The pullback-form chart trivialization sends the pulled-back chart frame to `1`. -/
theorem chartPullbackIso_hom_val_app_pulledSection (i : ι) :
    (chartPullbackIso U g hc i).hom.val.app (op ((U i).ι ⁻¹ᵁ (U i)))
        (pulledSection (U i).ι (moduleSheaf X U g) (U i) (chartFrame U g hc i)) =
      (1 : Γ((U i).toScheme, (U i).ι ⁻¹ᵁ (U i))) := by
  have h1 := congrArg
    (fun q : (schemeModulePullback (U i).ι).obj (moduleSheaf X U g) ⟶
        _root_.SheafOfModules.unit (U i).toScheme.ringCatSheaf =>
      q.val.app (op ((U i).ι ⁻¹ᵁ (U i)))
        (pulledSection (U i).ι (moduleSheaf X U g) (U i) (chartFrame U g hc i)))
    (chartPullbackIso_hom U g hc i)
  have h2 := pulledHom_comp_val_app ((restrictionIsoPullback (U i).ι).inv.app (moduleSheaf X U g))
    (chartRestrictionIso U g hc i).hom (op ((U i).ι ⁻¹ᵁ (U i)))
    (pulledSection (U i).ι (moduleSheaf X U g) (U i) (chartFrame U g hc i))
  have h3 := congrArg
    (fun y => (chartRestrictionIso U g hc i).hom.val.app (op ((U i).ι ⁻¹ᵁ (U i))) y)
    (restrictionIsoPullback_inv_app_pulledSection_unit' (U i).ι (moduleSheaf X U g) (U i)
      (chartFrame U g hc i))
  exact h1.trans (h2.trans (h3.trans (chartRestrictionIso_hom_val_app_unit U g hc i)))

end GluedChartFrame

section PulledChart

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (M : X.Modules)
  (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf)
  (s : M.val.obj (op U))

/-- The transport morphism between the two forms of the preimage open. -/
abbrev restrictEqHom : op (((f ∣_ U) ≫ U.ι) ⁻¹ᵁ U) ⟶ op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U) :=
  (eqToHom (congrArg (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => m ⁻¹ᵁ U)
    (morphismRestrict_ι f U).symm)).op

/-- The doubly pulled-back section. -/
abbrev doublePulled :
    ((schemeModulePullback (f ⁻¹ᵁ U).ι).obj ((schemeModulePullback f).obj M)).val.obj
      (op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) :=
  pulledSection (f ⁻¹ᵁ U).ι ((schemeModulePullback f).obj M) (f ⁻¹ᵁ U) (pulledSection f M U s)

/-- The iterated pulled-back section through the restricted morphism. -/
abbrev restrictedPulled :
    ((schemeModulePullback (f ∣_ U)).obj ((schemeModulePullback U.ι).obj M)).val.obj
      (op ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))) :=
  pulledSection (f ∣_ U) ((schemeModulePullback U.ι).obj M) (U.ι ⁻¹ᵁ U) (pulledSection U.ι M U s)

/-- The pulled-back trivialization, unfolded. -/
theorem pulledChartIso_hom :
    (pulledChartIso f M U t).hom =
      (schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).hom.app M ≫
        ((eqToIso (congrArg (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => (schemeModulePullback m).obj M)
          (morphismRestrict_ι f U).symm)).hom ≫
        ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M ≫
        ((schemeModulePullback (f ∣_ U)).map t.hom ≫
          (schemeModulePullbackUnitIso (f ∣_ U)).hom))) := rfl

set_option maxHeartbeats 800000 in
/-- **The core identity**, at the composite form of the preimage open: if the trivialization `t`
sends the pulled-back section of `s` to `1`, the pulled-back trivialization sends the doubly
pulled-back section of `s` to `1`. -/
theorem pulledChartIso_hom_val_app_doublePulled
    (ht : t.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U s) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U))) :
    (pulledChartIso f M U t).hom.val.app (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) (doublePulled f U M s) =
      (1 : Γ((f ⁻¹ᵁ U).toScheme, ((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) := by
  have hT := congrArg
    (fun q : (schemeModulePullback (f ⁻¹ᵁ U).ι).obj ((schemeModulePullback f).obj M) ⟶
        _root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf =>
      q.val.app (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) (doublePulled f U M s))
    (pulledChartIso_hom f U M t)
  have hc1 := pulledHom_comp_val_app ((schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).hom.app M)
    ((eqToIso (congrArg (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => (schemeModulePullback m).obj M)
        (morphismRestrict_ι f U).symm)).hom ≫
      ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M ≫
      ((schemeModulePullback (f ∣_ U)).map t.hom ≫ (schemeModulePullbackUnitIso (f ∣_ U)).hom)))
    (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) (doublePulled f U M s)
  have e1 : ((schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f).hom.app M).val.app
      (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) (doublePulled f U M s) =
      pulledSection ((f ⁻¹ᵁ U).ι ≫ f) M U s :=
    compIso_hom_val_app_pulledSection f (f ⁻¹ᵁ U).ι M U s
  have hc2 := pulledHom_comp_val_app
    (eqToIso (congrArg (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => (schemeModulePullback m).obj M)
      (morphismRestrict_ι f U).symm)).hom
    ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M ≫
      ((schemeModulePullback (f ∣_ U)).map t.hom ≫ (schemeModulePullbackUnitIso (f ∣_ U)).hom))
    (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) (pulledSection ((f ⁻¹ᵁ U).ι ≫ f) M U s)
  have e2 : (eqToIso (congrArg (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => (schemeModulePullback m).obj M)
      (morphismRestrict_ι f U).symm)).hom.val.app (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U))
      (pulledSection ((f ⁻¹ᵁ U).ι ≫ f) M U s) =
      ((schemeModulePullback ((f ∣_ U) ≫ U.ι)).obj M).val.map (restrictEqHom f U)
        (pulledSection ((f ∣_ U) ≫ U.ι) M U s) :=
    eqToIso_hom_val_app_pulledSection (morphismRestrict_ι f U).symm M U s
  have hc3 := pulledHom_comp_val_app ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M)
    ((schemeModulePullback (f ∣_ U)).map t.hom ≫ (schemeModulePullbackUnitIso (f ∣_ U)).hom)
    (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U))
    (((schemeModulePullback ((f ∣_ U) ≫ U.ι)).obj M).val.map (restrictEqHom f U)
      (pulledSection ((f ∣_ U) ≫ U.ι) M U s))
  have e3 : ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M).val.app
      (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U))
      (((schemeModulePullback ((f ∣_ U) ≫ U.ι)).obj M).val.map (restrictEqHom f U)
        (pulledSection ((f ∣_ U) ≫ U.ι) M U s)) =
      ((schemeModulePullback (f ∣_ U)).obj ((schemeModulePullback U.ι).obj M)).val.map
        (restrictEqHom f U) (restrictedPulled f U M s) :=
    (PresheafOfModules.naturality_apply ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M).val
      (restrictEqHom f U) (pulledSection ((f ∣_ U) ≫ U.ι) M U s)).trans
      (congrArg (fun y => ((schemeModulePullback (f ∣_ U)).obj
        ((schemeModulePullback U.ι).obj M)).val.map (restrictEqHom f U) y)
        (compIso_inv_val_app_pulledSection U.ι (f ∣_ U) M U s))
  have hc4 := pulledHom_comp_val_app ((schemeModulePullback (f ∣_ U)).map t.hom)
    (schemeModulePullbackUnitIso (f ∣_ U)).hom (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U))
    (((schemeModulePullback (f ∣_ U)).obj ((schemeModulePullback U.ι).obj M)).val.map
      (restrictEqHom f U) (restrictedPulled f U M s))
  have e4 : ((schemeModulePullback (f ∣_ U)).map t.hom).val.app (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U))
      (((schemeModulePullback (f ∣_ U)).obj ((schemeModulePullback U.ι).obj M)).val.map
        (restrictEqHom f U) (restrictedPulled f U M s)) =
      ((schemeModulePullback (f ∣_ U)).obj
        (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)).val.map (restrictEqHom f U)
        (pulledSection (f ∣_ U) (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) (U.ι ⁻¹ᵁ U)
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U))) :=
    (PresheafOfModules.naturality_apply ((schemeModulePullback (f ∣_ U)).map t.hom).val
      (restrictEqHom f U) (restrictedPulled f U M s)).trans
      (congrArg (fun y => ((schemeModulePullback (f ∣_ U)).obj
        (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)).val.map (restrictEqHom f U) y)
        ((pullback_map_val_app_pulledSection (f ∣_ U) t.hom (U.ι ⁻¹ᵁ U)
          (pulledSection U.ι M U s)).trans
          (congrArg (fun y => pulledSection (f ∣_ U)
            (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) (U.ι ⁻¹ᵁ U) y) ht)))
  have e5 : (schemeModulePullbackUnitIso (f ∣_ U)).hom.val.app (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U))
      (((schemeModulePullback (f ∣_ U)).obj
        (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf)).val.map (restrictEqHom f U)
        (pulledSection (f ∣_ U) (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) (U.ι ⁻¹ᵁ U)
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)))) =
      (1 : Γ((f ⁻¹ᵁ U).toScheme, ((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) :=
    (PresheafOfModules.naturality_apply (schemeModulePullbackUnitIso (f ∣_ U)).hom.val
      (restrictEqHom f U) (pulledSection (f ∣_ U)
        (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) (U.ι ⁻¹ᵁ U)
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U)))).trans
      ((congrArg (fun y => (_root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf).val.map
        (restrictEqHom f U) y)
        ((unitIso_hom_val_app_pulledSection (f ∣_ U) (U.ι ⁻¹ᵁ U)
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U))).trans (app_one (f ∣_ U) (U.ι ⁻¹ᵁ U)))).trans
        (unit_val_map_one' (f ⁻¹ᵁ U).toScheme _))
  have v1 := congrArg (fun y => ((eqToIso (congrArg
      (fun m : (f ⁻¹ᵁ U).toScheme ⟶ X => (schemeModulePullback m).obj M)
      (morphismRestrict_ι f U).symm)).hom ≫
      ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M ≫
      ((schemeModulePullback (f ∣_ U)).map t.hom ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom))).val.app
      (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) y) e1
  have v2 := congrArg (fun y => ((schemeModulePullbackCompIso (f ∣_ U) U.ι).inv.app M ≫
      ((schemeModulePullback (f ∣_ U)).map t.hom ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom)).val.app
      (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) y) e2
  have v3 := congrArg (fun y => ((schemeModulePullback (f ∣_ U)).map t.hom ≫
      (schemeModulePullbackUnitIso (f ∣_ U)).hom).val.app
      (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) y) e3
  have v4 := congrArg (fun y => (schemeModulePullbackUnitIso (f ∣_ U)).hom.val.app
      (op (((f ⁻¹ᵁ U).ι ≫ f) ⁻¹ᵁ U)) y) e4
  exact hT.trans (hc1.trans (v1.trans (hc2.trans (v2.trans (hc3.trans (v3.trans
    (hc4.trans (v4.trans e5))))))))

set_option maxHeartbeats 800000 in
/-- The core identity at the atlas form of the preimage open (the two forms are definitionally
equal; this restatement is the only place where a scoped heartbeat budget is used). -/
theorem pulledChartIso_hom_val_app_doublePulled'
    (ht : t.hom.val.app (op (U.ι ⁻¹ᵁ U)) (pulledSection U.ι M U s) =
      (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ U))) :
    (pulledChartIso f M U t).hom.val.app (op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) (doublePulled f U M s) =
      (1 : Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ U))) :=
  pulledChartIso_hom_val_app_doublePulled f U M t s ht

end PulledChart

section AtlasEvaluation

variable {Y : Scheme.{u}} (N : Y.Modules)

/-- The chart coordinate of an atlas of pullback charts, on a section: the inverse section-ring
isomorphism of the trivialization evaluated on the pulled-back section (accepted
`chartEquiv_ofOpenCharts`, `openChartCoordinate_eq_openSectionsInv`). -/
theorem chartEquiv_ofPullbackCharts_apply {ι : Type u} (W : ι → Y.Opens)
    (hW : ∀ y : Y, ∃ i, y ∈ W i)
    (t : ∀ i, (schemeModulePullback (W i).ι).obj N ≅
      _root_.SheafOfModules.unit (W i).toScheme.ringCatSheaf)
    (i : ι) (x : N.val.obj (op (W i))) :
    chartEquiv Y N (localTrivializationsOfOpenCharts N W hW
        (fun i => openChartOfPullback N (W i) (t i))) i le_rfl x =
      openSectionsInv (W i) le_rfl
        ((t i).hom.val.app (op ((W i).ι ⁻¹ᵁ (W i))) (pulledSection (W i).ι N (W i) x)) :=
  (chartEquiv_ofOpenCharts N W hW (fun i => openChartOfPullback N (W i) (t i)) i le_rfl x).trans
    ((openChartCoordinate_eq_openSectionsInv N (W i) (t i) le_rfl x).trans
      (congrArg (fun y => openSectionsInv (W i) le_rfl y)
        (homEquiv_val_app_pulledSection (W i).ι N _ (t i).hom (W i) x)))

end AtlasEvaluation

section Assembly

variable {X Y : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g) (f : Y ⟶ X)

/-- The chart coordinate of the pulled-back atlas on a section. -/
theorem chartEquiv_pulledAtlas_apply (hU : (⨆ i, U i) = ⊤) (i : ι)
    (x : ((schemeModulePullback f).obj (moduleSheaf X U g)).val.obj (op (f ⁻¹ᵁ U i))) :
    chartEquiv Y _ (pulledAtlas U g hc f hU) i le_rfl x =
      openSectionsInv (f ⁻¹ᵁ U i) le_rfl
        ((pulledChartIso f (moduleSheaf X U g) (U i) (chartPullbackIso U g hc i)).hom.val.app
          (op ((f ⁻¹ᵁ U i).ι ⁻¹ᵁ (f ⁻¹ᵁ U i)))
          (pulledSection (f ⁻¹ᵁ U i).ι ((schemeModulePullback f).obj (moduleSheaf X U g))
            (f ⁻¹ᵁ U i) x)) :=
  chartEquiv_ofPullbackCharts_apply ((schemeModulePullback f).obj (moduleSheaf X U g))
    (fun i => f ⁻¹ᵁ U i) _
    (fun i => pulledChartIso f (moduleSheaf X U g) (U i) (chartPullbackIso U g hc i)) i x

/-- **Every pulled-back chart frame has coordinate `1` in the pulled-back chart.** -/
theorem pulledFrameCoordinate : PulledFrameCoordinate.{u} := by
  intro Y X f ι U g hc hU i
  have h1 := chartEquiv_pulledAtlas_apply U g hc f hU i (pulledFrame U g hc f i)
  have h2 := pulledChartIso_hom_val_app_doublePulled' f (U i) (moduleSheaf X U g)
    (chartPullbackIso U g hc i) (chartFrame U g hc i)
    (chartPullbackIso_hom_val_app_pulledSection U g hc i)
  exact h1.trans ((congrArg (fun y => openSectionsInv (f ⁻¹ᵁ U i) le_rfl y) h2).trans
    (map_one (openSectionsInv (f ⁻¹ᵁ U i) le_rfl)))

/-- **The Picard class of the pullback of a cocycle-glued line bundle is the class of the
pulled-back cocycle.** -/
theorem pullbackGluedClass : PullbackGluedClass.{u} :=
  pullbackGluedClass_of_coordinate pulledFrameCoordinate

end Assembly

section Final

variable (k : Type u) [Field k] [IsAlgClosed k]
  (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (hdim : topologicalKrullDim X ≤ 1) (hTree : (componentPointIncidenceGraph X).IsTree)
  (htrans : HasTransverseComponentBranches X)
  (e : ∀ C : ↥(irreducibleComponents X), componentUnionScheme X {C} ≅ projectiveSpace k 1)

omit [IsAlgClosed k] [IsLocallyNoetherian X] in
include hdim hTree in
/-- The surjectivity half of `lem:tree-picard`, unconditional: on a reduced Noetherian curve with
tree component-point incidence graph, every integer vector of component exponents is realized by a
line bundle. -/
theorem multidegreeHom_surjective_final : Function.Surjective (multidegreeHom k X e) :=
  multidegreeHom_surjective_of_pullbackGluedClass k X hdim hTree e pullbackGluedClass

include f hdim hTree htrans in
/-- `lem:tree-picard`, unconditional: the multidegree homomorphism is bijective. -/
theorem multidegreeHom_bijective_final : Function.Bijective (multidegreeHom k X e) :=
  rationalTreePicard_of_pullbackGluedClass k X f hdim hTree htrans e pullbackGluedClass

/-- The Picard group of the rational tree as the free abelian group on its components (written
with Mathlib's multiplicative type tag). -/
def multidegreeMulEquiv_final : X.Pic ≃* (↥(irreducibleComponents X) → Multiplicative ℤ) :=
  MulEquiv.ofBijective (multidegreeHom k X e)
    (multidegreeHom_bijective_final k X f hdim hTree htrans e)

end Final

end KltDP.Geometry.RationalTreePicard
