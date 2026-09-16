import KltDP.Geometry.RationalTreePicardLeafNodeCompatibility
import KltDP.Geometry.RationalTreePicardPullbackEquivalence
import KltDP.Geometry.RationalTreePicardComponentComplementClosure
import KltDP.Geometry.ModuleOpenOver
import KltDP.Geometry.TransitionUnitRecovery
import KltDP.Geometry.TransitionUnitConstant
import KltDP.Geometry.TransitionUnitGauge
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The three-open cover of a leaf node and its atlas of the line bundle

Toward gluing the leaf-node chart trivialization with the component frames
(connection 3), this module supplies the actual open cover and the actual
trivializations on each open.

* Open pieces of a component union. For a reduced scheme `X`, an open `V` whose
  points lie in the closed component union `Z_S` is an open of `Z_S` itself: the
  restricted closed immersion `Z_S ∩ V → V` is a surjective closed immersion
  into a reduced scheme, hence an isomorphism (pinned
  `isIso_of_isClosedImmersion_of_surjective`). A frame of `L|_{Z_S}` therefore
  trivializes `L` on `V` (`componentOpenFrame`).
* The complement of the node. With `C` the leaf component and `q` its unique
  intersection point with the other components, `X ∖ {q}` is the disjoint union
  of the opens `leafOpen = X ∖ Z_{Cᶜ} ⊆ C` and `complementOpen = X ∖ C ⊆ Z_{Cᶜ}`;
  together with any affine chart `U ∋ q` these cover `X`.
* The atlas. `L` is trivialized on `U` by the leaf-node chart trivialization
  (transported from `Spec Γ(X,U)` through the affine `isoSpec`), on `leafOpen`
  by the leaf frame and on `complementOpen` by the complement frame. These form
  an actual `LocalTrivializations` atlas `leafNodeAtlas` of `L.obj`.
* The generic gluing step. For any atlas whose extracted transition units are a
  coboundary, the accepted recovery, gauge and identity-cocycle isomorphisms give
  a trivialization (`unitIsoOfGauge`).

What remains for the gluing (not proved here, not assumed anywhere): the
transition units of `leafNodeAtlas` are the node scalar on `U ∩ leafOpen` and `1`
elsewhere, hence a coboundary. This is the comparison, on the open `U ∩ leafOpen`
inside the leaf component, of the chart trivialization (whose pullback to the
leaf closed piece is the scalar multiple of the frame, by
`LeafNodeChart.chartUnitOpenIso_pullback_left`) with `componentOpenFrame`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction

section OpenPiece

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X)) (V : X.Opens)
  (hV : (V : Set X) ⊆ componentClosedUnion X S)

/-- The restriction of the actual closed immersion of a component union to an
open contained in that union is a closed immersion. -/
instance componentUnionInclusion_restrict_isClosedImmersion :
    IsClosedImmersion (componentUnionInclusion X S ∣_ V) :=
  IsLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance V

include hV in
/-- Over an open contained in the component union, the restricted closed
immersion is surjective on points. -/
theorem componentUnionInclusion_restrict_surjective :
    Surjective (componentUnionInclusion X S ∣_ V) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨y, hyV⟩ := y
  have hy : y ∈ Set.range (componentUnionInclusion X S).base := by
    rw [range_componentUnionInclusion]
    exact hV hyV
  obtain ⟨x, hx⟩ := hy
  have hxV : x ∈ componentUnionInclusion X S ⁻¹ᵁ V := by
    change (componentUnionInclusion X S).base x ∈ V
    rw [hx]
    exact hyV
  refine ⟨(⟨x, hxV⟩ : ↥(componentUnionInclusion X S ⁻¹ᵁ V)), ?_⟩
  apply Subtype.ext
  exact (morphismRestrict_base_coe (componentUnionInclusion X S) V ⟨x, hxV⟩).trans hx

include hV in
/-- An open of a reduced scheme lying in a component union is an open of the
reduced closed union: the restricted closed immersion is an isomorphism. -/
theorem componentUnionInclusion_restrict_isIso [AlgebraicGeometry.IsReduced X] :
    IsIso (componentUnionInclusion X S ∣_ V) := by
  haveI := componentUnionInclusion_restrict_surjective X S V hV
  haveI : AlgebraicGeometry.IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  exact isIso_of_isClosedImmersion_of_surjective _

variable [AlgebraicGeometry.IsReduced X] (L : InvertibleSheaf X)

/-- The pullback of a frame on the component union to the restricted closed piece
over `V`, through the pullback-composition and unit comparisons. -/
def componentOpenFrameChain
    (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :
    (schemeModulePullback (componentUnionInclusion X S ∣_ V)).obj
        ((schemeModulePullback V.ι).obj L.obj) ≅
      _root_.SheafOfModules.unit
        ((componentUnionInclusion X S ⁻¹ᵁ V).toScheme.ringCatSheaf) :=
  (schemeModulePullbackCompIso (componentUnionInclusion X S ∣_ V) V.ι).app L.obj ≪≫
    eqToIso (congrArg (fun k => (schemeModulePullback k).obj L.obj)
      (morphismRestrict_ι (componentUnionInclusion X S) V)) ≪≫
    ((schemeModulePullbackCompIso (componentUnionInclusion X S ⁻¹ᵁ V).ι
      (componentUnionInclusion X S)).app L.obj).symm ≪≫
    (schemeModulePullback (componentUnionInclusion X S ⁻¹ᵁ V).ι).mapIso frame ≪≫
    schemeModulePullbackUnitIso (componentUnionInclusion X S ⁻¹ᵁ V).ι

/-- A frame of the original line bundle on the component union trivializes it
on every open of the reduced scheme contained in that union: the trivialization is
the preimage of the pulled-back frame under the (fully faithful) pullback along the
restricted closed immersion, which is an isomorphism there. -/
def componentOpenFrame
    (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :
    (schemeModulePullback V.ι).obj L.obj ≅
      _root_.SheafOfModules.unit V.toScheme.ringCatSheaf :=
  haveI : IsIso (componentUnionInclusion X S ∣_ V) :=
    componentUnionInclusion_restrict_isIso X S V hV
  (schemeModulePullback (componentUnionInclusion X S ∣_ V)).preimageIso
    (componentOpenFrameChain X S V L frame ≪≫
      (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).symm)

/-- The open trivialization pulls back, along the restricted closed immersion, to
the pulled-back frame. -/
theorem componentOpenFrame_pullback
    (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :
    (schemeModulePullback (componentUnionInclusion X S ∣_ V)).map
        (componentOpenFrame X S V hV L frame).hom ≫
      (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).hom =
    (componentOpenFrameChain X S V L frame).hom := by
  haveI : IsIso (componentUnionInclusion X S ∣_ V) :=
    componentUnionInclusion_restrict_isIso X S V hV
  show (schemeModulePullback (componentUnionInclusion X S ∣_ V)).map
      ((schemeModulePullback (componentUnionInclusion X S ∣_ V)).preimage
        (componentOpenFrameChain X S V L frame ≪≫
          (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).symm).hom) ≫
      (schemeModulePullbackUnitIso (componentUnionInclusion X S ∣_ V)).hom = _
  rw [Functor.map_preimage, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

end OpenPiece

section NodeComplement

variable (X : Scheme.{u}) [NoetherianSpace X] (C : ↥(irreducibleComponents X))

/-- The open complement of the other components: the leaf component minus its
intersection with the others. -/
abbrev leafOpen : X.Opens := componentUnionComplementOpen X ({C}ᶜ)

/-- The open complement of the leaf component. -/
abbrev complementOpen : X.Opens := componentUnionComplementOpen X {C}

theorem mem_leafOpen_iff (x : X) :
    x ∈ leafOpen X C ↔ x ∉ componentClosedUnion X ({C}ᶜ) := Iff.rfl

theorem mem_complementOpen_iff (x : X) :
    x ∈ complementOpen X C ↔ x ∉ componentClosedUnion X {C} := Iff.rfl

/-- Points of the leaf open lie on the leaf component. -/
theorem leafOpen_subset : (leafOpen X C : Set X) ⊆ componentClosedUnion X {C} := by
  intro x hx
  have hcover : x ∈ (componentClosedUnion X {C} : Set X) ∪ componentClosedUnion X ({C}ᶜ) := by
    rw [componentClosedUnion_union_compl]
    exact Set.mem_univ x
  exact hcover.resolve_right ((mem_leafOpen_iff X C x).mp hx)

/-- Points of the complement open lie on the union of the other components. -/
theorem complementOpen_subset :
    (complementOpen X C : Set X) ⊆ componentClosedUnion X ({C}ᶜ) := by
  intro x hx
  have hcover : x ∈ (componentClosedUnion X {C} : Set X) ∪ componentClosedUnion X ({C}ᶜ) := by
    rw [componentClosedUnion_union_compl]
    exact Set.mem_univ x
  exact hcover.resolve_left ((mem_complementOpen_iff X C x).mp hx)

/-- The two opens are disjoint. -/
theorem leafOpen_inf_complementOpen : leafOpen X C ⊓ complementOpen X C = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hcover : x ∈ (componentClosedUnion X {C} : Set X) ∪ componentClosedUnion X ({C}ᶜ) := by
    rw [componentClosedUnion_union_compl]
    exact Set.mem_univ x
  rcases hcover with h | h
  · exact absurd h ((mem_complementOpen_iff X C x).mp hx.2)
  · exact absurd h ((mem_leafOpen_iff X C x).mp hx.1)

variable {q : X} (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})

include hcut in
/-- Away from the node, every point lies in one of the two opens; the node lies
in neither. -/
theorem mem_leafOpen_or_complementOpen_iff (x : X) :
    (x ∈ leafOpen X C ∨ x ∈ complementOpen X C) ↔ x ≠ q := by
  have hC : ∀ y : X, y ∈ componentClosedUnion X {C} ↔ y ∈ C.1 := fun y => by
    rw [← SetLike.mem_coe, coe_componentClosedUnion_singleton]
  rw [mem_leafOpen_iff, mem_complementOpen_iff, hC]
  constructor
  · intro h hxq
    rw [hxq] at h
    have hq : q ∈ C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) := by
      rw [hcut]
      exact Set.mem_singleton q
    rcases h with h | h
    · exact h hq.2
    · exact h hq.1
  · intro hne
    by_contra h
    push_neg at h
    have hx : x ∈ C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) := ⟨h.2, h.1⟩
    rw [hcut] at hx
    exact hne hx

include hcut in
/-- An affine chart through the node and the two opens cover the curve. -/
theorem leafNode_cover (U : X.Opens) (hq : q ∈ U) (x : X) :
    x ∈ U ∨ x ∈ leafOpen X C ∨ x ∈ complementOpen X C := by
  by_cases hx : x = q
  · left
    rw [hx]
    exact hq
  · exact Or.inr ((mem_leafOpen_or_complementOpen_iff X C hcut x).mpr hx)

end NodeComplement

section Atlas

/-- The three charts of the leaf-node cover. -/
inductive LeafCoverIndex : Type
  | chart
  | leaf
  | complement

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

/-- The leaf frame trivializes `L` on the leaf open. -/
def leafOpenUnitIso :
    (schemeModulePullback (leafOpen X C).ι).obj L.obj ≅
      _root_.SheafOfModules.unit (leafOpen X C).toScheme.ringCatSheaf :=
  componentOpenFrame X {C} (leafOpen X C) (leafOpen_subset X C) L frameC

/-- The complement frame trivializes `L` on the complement open. -/
def complementOpenUnitIso :
    (schemeModulePullback (complementOpen X C).ι).obj L.obj ≅
      _root_.SheafOfModules.unit (complementOpen X C).toScheme.ringCatSheaf :=
  componentOpenFrame X ({C}ᶜ) (complementOpen X C) (complementOpen_subset X C) L frameC'

/-- The affine chart inclusion is the affine identification followed by the
original `fromSpec`. -/
theorem affineOpen_ι_eq_isoSpec_fromSpec (W : X.affineOpens) :
    W.1.ι = W.2.isoSpec.hom ≫ W.2.fromSpec := by
  rw [← W.2.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- The leaf-node chart trivialization, transported to the open subscheme `U`. -/
def leafChartOpenUnitIso :
    (schemeModulePullback U.1.ι).obj L.obj ≅
      _root_.SheafOfModules.unit U.1.toScheme.ringCatSheaf :=
  (eqToIso (congrArg schemeModulePullback (affineOpen_ι_eq_isoSpec_fromSpec U))).app L.obj ≪≫
    ((schemeModulePullbackCompIso U.2.isoSpec.hom U.2.fromSpec).app L.obj).symm ≪≫
    (schemeModulePullback U.2.isoSpec.hom).mapIso
      (LeafNodeChart.chartUnitIso L f h frameC frameC') ≪≫
    schemeModulePullbackUnitIso U.2.isoSpec.hom

/-- The opens of the leaf-node cover. -/
def leafNodeCoverOpens (C : ↥(irreducibleComponents X)) (U : X.affineOpens) :
    ULift.{u} LeafCoverIndex → X.Opens
  | ⟨.chart⟩ => U.1
  | ⟨.leaf⟩ => leafOpen X C
  | ⟨.complement⟩ => complementOpen X C

variable (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})

include h hcut in
/-- The three opens cover the curve. -/
theorem leafNodeCoverOpens_cover (x : X) : ∃ i, x ∈ leafNodeCoverOpens C U i := by
  rcases leafNode_cover X C hcut U.1 hq x with hx | hx | hx
  · exact ⟨⟨.chart⟩, hx⟩
  · exact ⟨⟨.leaf⟩, hx⟩
  · exact ⟨⟨.complement⟩, hx⟩

/-- The trivializations of `L` on the three opens, as required by the actual
atlas constructor. -/
def leafNodeCoverIso (i : ULift.{u} LeafCoverIndex) :
    _root_.SheafOfModules.unit (leafNodeCoverOpens C U i).toScheme.ringCatSheaf ≅
      (restriction (leafNodeCoverOpens C U i).ι).obj L.obj :=
  match i with
  | ⟨.chart⟩ =>
    (leafChartOpenUnitIso L f h frameC frameC').symm ≪≫
      ((restrictionIsoPullback U.1.ι).app L.obj).symm
  | ⟨.leaf⟩ =>
    (leafOpenUnitIso L frameC).symm ≪≫
      ((restrictionIsoPullback (leafOpen X C).ι).app L.obj).symm
  | ⟨.complement⟩ =>
    (complementOpenUnitIso L frameC').symm ≪≫
      ((restrictionIsoPullback (complementOpen X C).ι).app L.obj).symm

/-- The actual atlas of the original line bundle on the leaf-node cover. -/
def leafNodeAtlas : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj :=
  localTrivializationsOfOpenCharts L.obj (leafNodeCoverOpens C U)
    (leafNodeCoverOpens_cover h hcut) (leafNodeCoverIso L f h frameC frameC')

@[simp]
theorem leafNodeAtlas_X (i : ULift.{u} LeafCoverIndex) :
    (leafNodeAtlas L f h frameC frameC' hcut).X i = leafNodeCoverOpens C U i := rfl

end Atlas

section Gauge

open TransitionUnitGluing TransitionUnitExtraction

variable (X : Scheme.{u}) (M : X.Modules)
  (t : KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) M)

/-- Any actual atlas whose extracted transition units are a coboundary
trivializes the module sheaf: recovery from the atlas, the gauge isomorphism
to the identity cocycle, and the identity-cocycle unit comparison. -/
def unitIsoOfGauge (b : ∀ i : t.I, Γ(X, t.X i)ˣ)
    (hb : IsGauge X t.X (transitionUnits X M t) (oneUnits X t.X) b) :
    M ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  recoveryIso X M t ≪≫ gaugeIso X t.X (transitionUnits X M t) (oneUnits X t.X) b hb ≪≫
    (unitIsoOne X t.X (chartOpens_cover X M t)).symm

end Gauge

end KltDP.Geometry.RationalTreePicard
