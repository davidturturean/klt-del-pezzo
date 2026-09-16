import KltDP.Geometry.RationalTreePicardOpenChartTransition

/-!
# Open-chart coordinates through the pullback adjunction

The accepted comparison `restrictionIsoPullback f : restriction f ≅ schemeModulePullback f`
is an `Adjunction.leftAdjointUniq`. Its characterization is adjunction-theoretic:
under the restriction adjunction, `(restrictionIsoPullback f).hom.app M ≫ ψ` is the
pullback-adjunction transpose of `ψ` (`restrictionIsoPullback_homEquiv`). Since the
restriction adjunction's unit acts on sections by the original restriction map,
this gives the section-level evaluation needed for the atlas coordinates: for an
open chart `openChartOfPullback M U t` obtained from a pullback trivialization
`t : (schemeModulePullback U.ι).obj M ≅ unit`, the coordinate of a section `s` over
`W ≤ U`, read on the open subscheme through the section-ring isomorphism `U.ι.app W`,
is the transpose `t♯ : M ⟶ (U.ι)_* O_U` evaluated on `s`
(`openChartCoordinate_ofPullback`, `openChartCoordinate_eq_openSectionsInv`).

For the leaf-node atlas, all three charts are of this form. The two coordinate
equations `hleaf`/`hcompl` of `RationalTreePicardOpenChartTransition` are therefore
equivalent to equations between the transposes of the three pullback trivializations
on the overlaps, read back into `Γ(X, W)` through the inverse section-ring
isomorphisms (`leafNodeUnitIsoOfTransposes`). The leaf gauge unit is taken as the
image of the derived node scalar `LeafNodeChart.chartScalar` under the structure
morphism (`nodeScalarGauge`, `leafNodeUnitIsoOfScalarTransposes`).

What is NOT proved here: the two transpose equations themselves (hypotheses
`hleafT`, `hcomplT` below). They are the exact remaining coherence statement: the
pullback-adjunction transposes of `leafChartOpenUnitIso` (chart, through `isoSpec`
and the affine closed-frame descent) and of `leafOpenUnitIso` /
`complementOpenUnitIso` (through the restricted closed immersions) agree on
`U ∩ leafOpen` up to the node scalar and on `U ∩ complementOpen`. Computing those
transposes is adjunction calculus over the accepted
`SchemeModulePullbackCoherence` lemmas and the chart identities of
`RationalTreePicardLeafNodeCompatibility`; no new hypothesis is involved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction TransitionUnitExtraction TransitionUnitGluing

section RestrictionPullback

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (N : Y.Modules)

/-- Under the restriction adjunction, the restriction/pullback comparison followed
by a morphism is the pullback-adjunction transpose of that morphism. -/
theorem restrictionIsoPullback_homEquiv (ψ : (schemeModulePullback f).obj M ⟶ N) :
    (restrictionAdjunction f).homEquiv M N ((restrictionIsoPullback f).hom.app M ≫ ψ) =
      (schemeModulePullbackPushforwardAdjunction f).homEquiv M N ψ := by
  unfold restrictionIsoPullback
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

end RestrictionPullback

section PullbackCharts

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

/-- The open chart of an atlas obtained from a pullback trivialization, in the form
used by the leaf-node atlas. -/
abbrev openChartOfPullback
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :
    _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M :=
  t.symm ≪≫ ((restrictionIsoPullback U.ι).app M).symm

/-- The pullback-adjunction transpose of a pullback trivialization: a morphism of
module sheaves on `X` into the pushforward of the structure sheaf of the open. -/
abbrev pullbackTrivializationTranspose
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M ⟶ (schemeModulePushforward U.ι).obj (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  (schemeModulePullbackPushforwardAdjunction U.ι).homEquiv M _ t.hom

theorem openChartOfPullback_inv
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (openChartOfPullback M U t).inv = (restrictionIsoPullback U.ι).hom.app M ≫ t.hom := by
  simp only [openChartOfPullback, Iso.trans_inv, Iso.symm_inv, Iso.app_hom]

/-- The restriction-adjunction transpose of the inverse open chart is the
pullback-adjunction transpose of the pullback trivialization. -/
theorem openChartOfPullback_homEquiv
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (restrictionAdjunction U.ι).homEquiv M _ (openChartOfPullback M U t).inv =
      pullbackTrivializationTranspose M U t := by
  rw [openChartOfPullback_inv]
  exact restrictionIsoPullback_homEquiv U.ι M _ t.hom

/-- The coordinate of a section in a pullback chart, read on the open subscheme,
is the transpose evaluated on the section. -/
theorem openChartCoordinate_ofPullback
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf)
    {W : X.Opens} (hW : W ≤ U) (s : M.val.obj (op W)) :
    U.ι.app W (openChartCoordinate M U (openChartOfPullback M U t) hW s) =
      (pullbackTrivializationTranspose M U t).val.app (op W) s := by
  rw [openChartCoordinate_app]
  have h := congrArg
    (fun φ : M ⟶ (schemeModulePushforward U.ι).obj
      (_root_.SheafOfModules.unit U.toScheme.ringCatSheaf) => φ.val.app (op W) s)
    (openChartOfPullback_homEquiv M U t)
  exact h

/-- The inverse section-ring isomorphism of an open immersion on a subopen. -/
def openSectionsInv (V : X.Opens) {W : X.Opens} (hW : W ≤ V) :
    Γ(V.toScheme, V.ι ⁻¹ᵁ W) →+* Γ(X, W) :=
  haveI : IsIso (V.ι.app W) := Scheme.Hom.isIso_app V.ι W (by simpa using hW)
  (asIso (V.ι.app W)).commRingCatIsoToRingEquiv.symm.toRingHom

theorem openSectionsInv_app (V : X.Opens) {W : X.Opens} (hW : W ≤ V) (r : Γ(X, W)) :
    openSectionsInv V hW (V.ι.app W r) = r := by
  haveI : IsIso (V.ι.app W) := Scheme.Hom.isIso_app V.ι W (by simpa using hW)
  exact (asIso (V.ι.app W)).commRingCatIsoToRingEquiv.symm_apply_apply r

/-- The coordinate of a section in a pullback chart is the transpose evaluated on the
section, read back into `Γ(X, W)` through the inverse section-ring isomorphism. -/
theorem openChartCoordinate_eq_openSectionsInv
    (t : (schemeModulePullback U.ι).obj M ≅ _root_.SheafOfModules.unit U.toScheme.ringCatSheaf)
    {W : X.Opens} (hW : W ≤ U) (s : M.val.obj (op W)) :
    openChartCoordinate M U (openChartOfPullback M U t) hW s =
      openSectionsInv U hW ((pullbackTrivializationTranspose M U t).val.app (op W) s) := by
  rw [← openChartCoordinate_ofPullback M U t hW s]
  exact (openSectionsInv_app U hW _).symm

variable {ι : Type u} (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
  (t : ∀ i, (schemeModulePullback (V i).ι).obj M ≅
    _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf)

/-- For an atlas of pullback charts, a unit relating the two transposes on the
overlap (read back into `Γ(X, W)`) is the extracted transition unit. -/
theorem transitionUnits_ofPullbackCharts (i j : ι) (u : Γ(X, V i ⊓ V j)ˣ)
    (hu : ∀ s : M.val.obj (op (V i ⊓ V j)),
      (u : Γ(X, V i ⊓ V j)) *
        openSectionsInv (V j) inf_le_right
          ((pullbackTrivializationTranspose M (V j) (t j)).val.app (op (V i ⊓ V j)) s) =
      openSectionsInv (V i) inf_le_left
        ((pullbackTrivializationTranspose M (V i) (t i)).val.app (op (V i ⊓ V j)) s)) :
    transitionUnits X M
      (localTrivializationsOfOpenCharts M V hV (fun i => openChartOfPullback M (V i) (t i))) i j = u :=
  transitionUnits_ofOpenCharts M V hV (fun i => openChartOfPullback M (V i) (t i)) i j u
    (fun s => by
      rw [openChartCoordinate_eq_openSectionsInv, openChartCoordinate_eq_openSectionsInv]
      exact hu s)

end PullbackCharts

section LeafAtlas

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
  (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})

/-- The transpose of the chart trivialization: a morphism `L ⟶ (U.ι)_* O_U` on `X`. -/
abbrev leafChartTranspose :
    L.obj ⟶ (schemeModulePushforward U.1.ι).obj
      (_root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf) :=
  pullbackTrivializationTranspose L.obj U.1 (leafChartOpenUnitIso L f h frameC frameC')

/-- The transpose of the leaf-open trivialization. -/
abbrev leafOpenTranspose :
    L.obj ⟶ (schemeModulePushforward (leafOpen X C).ι).obj
      (_root_.SheafOfModules.unit (leafOpen X C).toScheme.ringCatSheaf) :=
  pullbackTrivializationTranspose L.obj (leafOpen X C) (leafOpenUnitIso L frameC)

/-- The transpose of the complement-open trivialization. -/
abbrev complementOpenTranspose :
    L.obj ⟶ (schemeModulePushforward (complementOpen X C).ι).obj
      (_root_.SheafOfModules.unit (complementOpen X C).toScheme.ringCatSheaf) :=
  pullbackTrivializationTranspose L.obj (complementOpen X C) (complementOpenUnitIso L frameC')

/-- The chart coordinate of the leaf-node atlas is the chart transpose. -/
theorem leafNodeCoverIso_chart_coordinate {W : X.Opens} (hWU : W ≤ U.1)
    (s : L.obj.val.obj (op W)) :
    openChartCoordinate L.obj U.1 (leafNodeCoverIso L f h frameC frameC' ⟨.chart⟩) hWU s =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s) :=
  openChartCoordinate_eq_openSectionsInv L.obj U.1 (leafChartOpenUnitIso L f h frameC frameC')
    hWU s

/-- The leaf coordinate of the leaf-node atlas is the leaf transpose. -/
theorem leafNodeCoverIso_leaf_coordinate {W : X.Opens} (hWl : W ≤ leafOpen X C)
    (s : L.obj.val.obj (op W)) :
    openChartCoordinate L.obj (leafOpen X C)
        (leafNodeCoverIso L f h frameC frameC' ⟨.leaf⟩) hWl s =
      openSectionsInv (leafOpen X C) hWl ((leafOpenTranspose L frameC).val.app (op W) s) :=
  openChartCoordinate_eq_openSectionsInv L.obj (leafOpen X C) (leafOpenUnitIso L frameC) hWl s

/-- The complement coordinate of the leaf-node atlas is the complement transpose. -/
theorem leafNodeCoverIso_complement_coordinate {W : X.Opens} (hWc : W ≤ complementOpen X C)
    (s : L.obj.val.obj (op W)) :
    openChartCoordinate L.obj (complementOpen X C)
        (leafNodeCoverIso L f h frameC frameC' ⟨.complement⟩) hWc s =
      openSectionsInv (complementOpen X C) hWc
        ((complementOpenTranspose L frameC').val.app (op W) s) :=
  openChartCoordinate_eq_openSectionsInv L.obj (complementOpen X C)
    (complementOpenUnitIso L frameC') hWc s

/-- The gluing step, conditional on the two transpose equations on the overlaps.
These equations are the remaining coherence statement of connection 3. -/
def leafNodeUnitIsoOfTransposes (β : Γ(X, leafOpen X C)ˣ)
    (hleafT : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C)
      (s : L.obj.val.obj (op W)),
      res X hWl (β : Γ(X, leafOpen X C)) *
        openSectionsInv (leafOpen X C) hWl ((leafOpenTranspose L frameC).val.app (op W) s) =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s))
    (hcomplT : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWc : W ≤ complementOpen X C)
      (s : L.obj.val.obj (op W)),
      openSectionsInv (complementOpen X C) hWc
          ((complementOpenTranspose L frameC').val.app (op W) s) =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  leafNodeUnitIsoOfCoordinates L f h frameC frameC' hcut β
    (fun W hWU hWl s => by
      rw [leafNodeCoverIso_leaf_coordinate, leafNodeCoverIso_chart_coordinate]
      exact hleafT W hWU hWl s)
    (fun W hWU hWc s => by
      rw [leafNodeCoverIso_complement_coordinate, leafNodeCoverIso_chart_coordinate]
      exact hcomplT W hWU hWc s)

/-- The base field mapped into the sections over an open of the curve, through the
structure morphism. -/
def baseSections (W : X.Opens) : k →+* Γ(X, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
    X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom

/-- The leaf gauge unit determined by the derived node scalar of the frames. -/
def nodeScalarGauge : Γ(X, leafOpen X C)ˣ :=
  Units.map (baseSections f (leafOpen X C)).toMonoidHom (h.chartScalar L f frameC frameC')

/-- The gluing step with the leaf gauge unit taken as the image of the derived node
scalar; conditional on the two transpose equations. -/
def leafNodeUnitIsoOfScalarTransposes
    (hleafT : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C)
      (s : L.obj.val.obj (op W)),
      res X hWl (nodeScalarGauge L f h frameC frameC' : Γ(X, leafOpen X C)) *
        openSectionsInv (leafOpen X C) hWl ((leafOpenTranspose L frameC).val.app (op W) s) =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s))
    (hcomplT : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWc : W ≤ complementOpen X C)
      (s : L.obj.val.obj (op W)),
      openSectionsInv (complementOpen X C) hWc
          ((complementOpenTranspose L frameC').val.app (op W) s) =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s)) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  leafNodeUnitIsoOfTransposes L f h frameC frameC' hcut (nodeScalarGauge L f h frameC frameC')
    hleafT hcomplT

end LeafAtlas

end KltDP.Geometry.RationalTreePicard
