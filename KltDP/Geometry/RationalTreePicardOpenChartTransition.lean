import KltDP.Geometry.RationalTreePicardLeafNodeCover
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Transition units of an atlas of open-subscheme trivializations

An atlas built by `localTrivializationsOfOpenCharts` from scheme-level
trivializations `e i : unit (V i) ≅ (restriction (V i).ι).obj M` has, on a
subopen `W ≤ V i`, the coordinate map
`openChartCoordinate M (V i) (e i) hW : M(W) → Γ(X, W)`, the evaluation of the
over-site inverse `(openChartToOverUnitIso (V i) M (e i)).inv`. This module proves:

* `chartEquiv_ofOpenCharts`: the atlas chart coordinate `chartEquiv` is exactly
  this coordinate map;
* `transitionUnitOn_ofOpenCharts` / `transitionUnits_ofOpenCharts`: a unit `u`
  with `u * coord_j s = coord_i s` for all sections `s` over the overlap is the
  extracted transition unit `transitionUnits t i j`.

For the leaf-node atlas `leafNodeAtlas` this reduces the coboundary property to
two coordinate equations, one on `U ⊓ leafOpen` (with the leaf gauge unit `β`)
and one on `U ⊓ complementOpen` (with unit `1`); the diagonal equations follow
from the extracted cocycle, and the `leafOpen`/`complementOpen` overlap is empty,
so its section ring is a subsingleton. `leafNodeAtlas_isGauge` proves the gauge
property from those two equations and `leafNodeUnitIsoOfCoordinates` concludes
`L.obj ≅ unit` through `unitIsoOfGauge`.

The two coordinate equations are hypotheses of these last two declarations; they
are NOT proved here. They are the exact remaining coherence statement of the
gluing step (connection 3): the comparison, through `openChartToOverUnitIso`, of
the chart trivialization `leafChartOpenUnitIso` (built from the affine closed-frame
descent) with `leafOpenUnitIso` and `complementOpenUnitIso` (built from the
component frames through the restricted closed immersions). Everything else in the
gluing step is proved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction TransitionUnitExtraction TransitionUnitGluing

section OpenChartCoordinates

variable {X : Scheme.{u}} (M : X.Modules)

/-- The over-site coordinate of an open-subscheme trivialization on a subopen
`W ≤ U`: evaluation of the inverse of `openChartToOverUnitIso` on sections. -/
def openChartCoordinate (U : X.Opens)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    {W : X.Opens} (hW : W ≤ U) (s : M.val.obj (op W)) : Γ(X, W) :=
  (openChartToOverUnitIso U M e).inv.val.app (op (Over.mk (homOfLE hW))) s

/-- The coordinate, read on the open subscheme through the original section-ring
isomorphism of the open immersion, is the evaluation of the scheme-level inverse
trivialization on the restricted section. -/
theorem openChartCoordinate_app (U : X.Opens)
    (e : _root_.SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restriction U.ι).obj M)
    {W : X.Opens} (hW : W ≤ U) (s : M.val.obj (op W)) :
    U.ι.app W (openChartCoordinate M U e hW s) =
      e.inv.val.app (op (U.overEquivalence.functor.obj (Over.mk (homOfLE hW))))
        (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W)
          (Set.image_preimage_subset _ _)).op s) := by
  haveI : IsIso (U.ι.app W) := Scheme.Hom.isIso_app U.ι W (by simpa using hW)
  change U.ι.app W ((openToOverUnitLinearEquiv U (Over.mk (homOfLE hW))).symm
    (e.inv.val.app (op (U.overEquivalence.functor.obj (Over.mk (homOfLE hW))))
      (M.val.map (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ W)
        (Set.image_preimage_subset _ _)).op s))) = _
  exact (asIso (U.ι.app W)).commRingCatIsoToRingEquiv.apply_symm_apply _

variable {ι : Type u} (V : ι → X.Opens) (hV : ∀ x : X, ∃ i, x ∈ V i)
  (e : ∀ i, _root_.SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅
    (restriction (V i).ι).obj M)

/-- The unit isomorphism of an atlas of open charts is the inverse of the
over-site chart isomorphism. -/
theorem unitIso_ofOpenCharts_hom (i : ι) :
    ((localTrivializationsOfOpenCharts M V hV e).unitIso i).hom =
      (openChartToOverUnitIso (V i) M (e i)).inv := by
  change ((_root_.SheafOfModules.freeUniqueIsoUnit (R := X.ringCatSheaf.over (V i)) PUnit ≪≫
      openChartToOverUnitIso (V i) M (e i)).symm ≪≫
      _root_.SheafOfModules.freeUniqueIsoUnit (R := X.ringCatSheaf.over (V i)) PUnit).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The atlas chart coordinate is the over-site coordinate of the open chart. -/
theorem chartEquiv_ofOpenCharts (i : ι) {W : X.Opens} (hWi : W ≤ V i)
    (s : M.val.obj (op W)) :
    chartEquiv X M (localTrivializationsOfOpenCharts M V hV e) i hWi s =
      openChartCoordinate M (V i) (e i) hWi s := by
  rw [chartEquiv_apply]
  exact congrArg
    (fun φ : M.over (V i) ⟶ _root_.SheafOfModules.unit (X.ringCatSheaf.over (V i)) =>
      φ.val.app (op (Over.mk (homOfLE hWi))) s)
    (unitIso_ofOpenCharts_hom M V hV e i)

/-- A unit relating the two open-chart coordinates on a common subopen is the
extracted transition unit there. -/
theorem transitionUnitOn_ofOpenCharts (i j : ι) {W : X.Opens} (hWi : W ≤ V i) (hWj : W ≤ V j)
    (u : Γ(X, W)ˣ)
    (hu : ∀ s : M.val.obj (op W),
      (u : Γ(X, W)) * openChartCoordinate M (V j) (e j) hWj s =
        openChartCoordinate M (V i) (e i) hWi s) :
    transitionUnitOn X M (localTrivializationsOfOpenCharts M V hV e) i j hWi hWj = u := by
  apply KltDP.Module.transitionUnit_eq_of
  intro s
  rw [chartEquiv_ofOpenCharts M V hV e j hWj s, chartEquiv_ofOpenCharts M V hV e i hWi s]
  exact hu s

/-- The extracted transition unit of an atlas of open charts is determined by
the coordinate relation on the overlap. -/
theorem transitionUnits_ofOpenCharts (i j : ι) (u : Γ(X, V i ⊓ V j)ˣ)
    (hu : ∀ s : M.val.obj (op (V i ⊓ V j)),
      (u : Γ(X, V i ⊓ V j)) * openChartCoordinate M (V j) (e j) inf_le_right s =
        openChartCoordinate M (V i) (e i) inf_le_left s) :
    transitionUnits X M (localTrivializationsOfOpenCharts M V hV e) i j = u :=
  transitionUnitOn_ofOpenCharts M V hV e i j inf_le_left inf_le_right u hu

end OpenChartCoordinates

/-- Sections over an open equal to the empty open form a subsingleton ring. -/
theorem subsingleton_sections_of_eq_bot {X : Scheme.{u}} {W : X.Opens} (hW : W = ⊥) :
    Subsingleton Γ(X, W) :=
  CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hW)

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

/-- The gauge family on the leaf-node cover: the identity on the chart and on
the complement open, a given unit `β` on the leaf open. -/
def leafGauge (β : Γ(X, leafOpen X C)ˣ) :
    ∀ i : ULift.{u} LeafCoverIndex, Γ(X, leafNodeCoverOpens C U i)ˣ
  | ⟨.chart⟩ => 1
  | ⟨.leaf⟩ => β
  | ⟨.complement⟩ => 1

/-- The leaf-node atlas written in the open-chart form used by the transition
lemmas; it is definitionally `leafNodeAtlas`. -/
abbrev leafNodeChartAtlas :
    KltDP.SheafOfModules.LocalTrivializations (R := X.ringCatSheaf) L.obj :=
  localTrivializationsOfOpenCharts L.obj (leafNodeCoverOpens C U)
    (leafNodeCoverOpens_cover h hcut) (leafNodeCoverIso L f h frameC frameC')

theorem leafNodeChartAtlas_eq :
    leafNodeChartAtlas L f h frameC frameC' hcut = leafNodeAtlas L f h frameC frameC' hcut := rfl

/-- The unit `res β` on the chart/leaf overlap. -/
abbrev leafGaugeChartLeafUnit (β : Γ(X, leafOpen X C)ˣ) : Γ(X, U.1 ⊓ leafOpen X C)ˣ :=
  Units.map (res X (inf_le_right : U.1 ⊓ leafOpen X C ≤ leafOpen X C)).toMonoidHom β

/-- The unit `res β` on the leaf/chart overlap. -/
abbrev leafGaugeLeafChartUnit (β : Γ(X, leafOpen X C)ˣ) : Γ(X, leafOpen X C ⊓ U.1)ˣ :=
  Units.map (res X (inf_le_left : leafOpen X C ⊓ U.1 ≤ leafOpen X C)).toMonoidHom β

set_option maxHeartbeats 800000 in
/-- The two coordinate equations imply that the extracted transition units of
the leaf-node atlas form a coboundary. The `leafOpen`/`complementOpen` overlap is
empty; the diagonal equations come from the extracted cocycle. -/
theorem leafNodeAtlas_isGauge (β : Γ(X, leafOpen X C)ˣ)
    (hleaf : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C)
      (s : L.obj.val.obj (op W)),
      res X hWl (β : Γ(X, leafOpen X C)) *
        openChartCoordinate L.obj (leafOpen X C)
          (leafNodeCoverIso L f h frameC frameC' ⟨.leaf⟩) hWl s =
      openChartCoordinate L.obj U.1 (leafNodeCoverIso L f h frameC frameC' ⟨.chart⟩) hWU s)
    (hcompl : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWc : W ≤ complementOpen X C)
      (s : L.obj.val.obj (op W)),
      openChartCoordinate L.obj (complementOpen X C)
          (leafNodeCoverIso L f h frameC frameC' ⟨.complement⟩) hWc s =
      openChartCoordinate L.obj U.1 (leafNodeCoverIso L f h frameC frameC' ⟨.chart⟩) hWU s) :
    IsGauge X (leafNodeChartAtlas L f h frameC frameC' hcut).X
      (transitionUnits X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut))
      (oneUnits X (leafNodeChartAtlas L f h frameC frameC' hcut).X) (leafGauge β) := by
  have hcoc := transitionUnits_isCocycle X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut)
  -- the chart/leaf transition
  have hcl : transitionUnits X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut)
      ⟨.chart⟩ ⟨.leaf⟩ = leafGaugeChartLeafUnit β :=
    transitionUnits_ofOpenCharts L.obj (leafNodeCoverOpens C U) (leafNodeCoverOpens_cover h hcut)
      (leafNodeCoverIso L f h frameC frameC') ⟨.chart⟩ ⟨.leaf⟩ (leafGaugeChartLeafUnit β)
      (fun s => hleaf _ inf_le_left inf_le_right s)
  have hlc : transitionUnits X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut)
      ⟨.leaf⟩ ⟨.chart⟩ = (leafGaugeLeafChartUnit β)⁻¹ :=
    transitionUnits_ofOpenCharts L.obj (leafNodeCoverOpens C U) (leafNodeCoverOpens_cover h hcut)
      (leafNodeCoverIso L f h frameC frameC') ⟨.leaf⟩ ⟨.chart⟩ (leafGaugeLeafChartUnit β)⁻¹
      (fun s =>
        (congrArg (fun z => Units.val ((leafGaugeLeafChartUnit β)⁻¹) * z)
          (hleaf _ inf_le_right inf_le_left s).symm).trans
          (Units.inv_mul_cancel_left (leafGaugeLeafChartUnit β) _))
  -- the chart/complement transition
  have hcc : transitionUnits X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut)
      ⟨.chart⟩ ⟨.complement⟩ = 1 :=
    transitionUnits_ofOpenCharts L.obj (leafNodeCoverOpens C U) (leafNodeCoverOpens_cover h hcut)
      (leafNodeCoverIso L f h frameC frameC') ⟨.chart⟩ ⟨.complement⟩ 1
      (fun s => (one_mul _).trans (hcompl _ inf_le_left inf_le_right s))
  have hcc' : transitionUnits X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut)
      ⟨.complement⟩ ⟨.chart⟩ = 1 :=
    transitionUnits_ofOpenCharts L.obj (leafNodeCoverOpens C U) (leafNodeCoverOpens_cover h hcut)
      (leafNodeCoverIso L f h frameC frameC') ⟨.complement⟩ ⟨.chart⟩ 1
      (fun s => (one_mul _).trans (hcompl _ inf_le_right inf_le_left s).symm)
  -- the empty overlaps
  have hlcpl : leafOpen X C ⊓ complementOpen X C = ⊥ := leafOpen_inf_complementOpen X C
  have hcpll : complementOpen X C ⊓ leafOpen X C = ⊥ := by
    rw [inf_comm]
    exact leafOpen_inf_complementOpen X C
  intro i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j
  · -- chart, chart
    rw [hcoc.unit_self]
    simp only [leafGauge, oneUnits, Units.val_one, map_one, one_mul, mul_one]
  · -- chart, leaf
    rw [hcl]
    simp only [leafGauge, oneUnits, Units.val_one, map_one, one_mul]
    try rfl
  · -- chart, complement
    rw [hcc]
    simp only [leafGauge, oneUnits, Units.val_one, map_one, one_mul, mul_one]
  · -- leaf, chart
    rw [hlc]
    simp only [leafGauge, oneUnits, Units.val_one, map_one, one_mul, mul_one]
    exact Units.mul_inv (leafGaugeLeafChartUnit β)
  · -- leaf, leaf
    rw [hcoc.unit_self]
    simp only [leafGauge, oneUnits, Units.val_one, one_mul, mul_one]
  · -- leaf, complement
    exact @Subsingleton.elim _ (subsingleton_sections_of_eq_bot hlcpl) _ _
  · -- complement, chart
    rw [hcc']
    simp only [leafGauge, oneUnits, Units.val_one, map_one, one_mul, mul_one]
  · -- complement, leaf
    exact @Subsingleton.elim _ (subsingleton_sections_of_eq_bot hcpll) _ _
  · -- complement, complement
    rw [hcoc.unit_self]
    simp only [leafGauge, oneUnits, Units.val_one, map_one, one_mul, mul_one]

/-- The gluing step, conditional on the two coordinate equations: the original
line bundle is trivial. The two equations are the remaining coherence statement of
connection 3 and are hypotheses here, not results. -/
def leafNodeUnitIsoOfCoordinates (β : Γ(X, leafOpen X C)ˣ)
    (hleaf : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C)
      (s : L.obj.val.obj (op W)),
      res X hWl (β : Γ(X, leafOpen X C)) *
        openChartCoordinate L.obj (leafOpen X C)
          (leafNodeCoverIso L f h frameC frameC' ⟨.leaf⟩) hWl s =
      openChartCoordinate L.obj U.1 (leafNodeCoverIso L f h frameC frameC' ⟨.chart⟩) hWU s)
    (hcompl : ∀ (W : X.Opens) (hWU : W ≤ U.1) (hWc : W ≤ complementOpen X C)
      (s : L.obj.val.obj (op W)),
      openChartCoordinate L.obj (complementOpen X C)
          (leafNodeCoverIso L f h frameC frameC' ⟨.complement⟩) hWc s =
      openChartCoordinate L.obj U.1 (leafNodeCoverIso L f h frameC frameC' ⟨.chart⟩) hWU s) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  unitIsoOfGauge X L.obj (leafNodeChartAtlas L f h frameC frameC' hcut) (leafGauge β)
    (leafNodeAtlas_isGauge L f h frameC frameC' hcut β hleaf hcompl)

end LeafAtlas

end KltDP.Geometry.RationalTreePicard
