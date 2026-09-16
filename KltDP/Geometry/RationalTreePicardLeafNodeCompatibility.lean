import KltDP.Geometry.RationalTreePicardRationalComponentFrame
import KltDP.Geometry.RationalTreePicardClosedFrameOpenRestriction

/-!
# Restriction identities of the leaf-node chart trivialization

The affine closed-frame trivialization `LeafNodeChart.frameUnitIso` and its
curve-level form `LeafNodeChart.chartUnitIso` were built from the accepted
`closedFrameUnitIso`. The lane module `RationalTreePicardClosedFrameOpenRestriction`
proves that the pullback of that isomorphism to the right closed piece is the
given right frame, and to the left closed piece is the given left frame after
multiplication by the lifted node scalar; the same holds after restriction to
every open of the affine chart. This module transports those identities to the
leaf-node objects without any new hypothesis.

Concretely, for the two original component ideals `I = componentChartIdeal X {C} U`
and `J = componentChartIdeal X {C}ᶜ U` of a leaf-node chart:

* the pullback of `chartUnitIso` along `Spec (Γ(X,U) ⧸ J) → Spec Γ(X,U)` is the
  transported complement frame `componentChartFrame X {C}ᶜ U L frameC'`;
* the pullback along `Spec (Γ(X,U) ⧸ I) → Spec Γ(X,U)`, followed by the scalar
  endomorphism of the lifted node scalar `LeafNodeChart.chartScalar`, is the
  transported leaf frame `componentChartFrame X {C} U L frameC`;
* both identities persist on every open `V` of the affine chart, with the
  restricted frames built from the SAME given frames.

These are the compatibility data needed to glue the chart trivialization with the
component frames over the complement of the node. Gluing itself, and the passage
from the affine chart to the open subscheme `U ⊆ X`, are not done here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

section AffineChart

variable {X : Scheme.{u}} [NoetherianSpace X] {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)
  (L : InvertibleSheaf (Spec (CommRingCat.of Γ(X, U.1))))
  (leftFrame : (schemeModulePullback
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).obj L.obj ≅
    _root_.SheafOfModules.unit
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U))).ringCatSheaf)
  (rightFrame : (schemeModulePullback
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).obj L.obj ≅
    _root_.SheafOfModules.unit
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X ({C}ᶜ) U))).ringCatSheaf)

/-- The ground-field node scalar of the two frames at the leaf node, derived
from the actual node transition of the frames (no scalar is supplied). -/
def LeafNodeChart.frameScalar : kˣ := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact closedFrameScalar k Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support L
    leftFrame rightFrame

/-- The lifted node scalar as an actual global section of the leaf closed piece. -/
def LeafNodeChart.frameScalarSection :
    Γ(Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U)), ⊤) := by
  letI := affineSectionsAlgebra f U.2
  exact closedLineLeftScalarSection Γ(X, U.1) (componentChartIdeal X {C} U)
    (h.frameScalar f L leftFrame rightFrame)

/-- Pullback of the affine leaf-node trivialization to the complement piece
is the given right frame. -/
theorem LeafNodeChart.frameUnitIso_pullback_right :
    (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).map
        (h.frameUnitIso f L leftFrame rightFrame).hom ≫
      (schemeModulePullbackUnitIso
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).hom =
    rightFrame.hom := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact closedFrameUnitIso_pullback_right k Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support L
    leftFrame rightFrame h.cover

/-- Pullback of the affine leaf-node trivialization to the leaf piece is the
given left frame after the lifted node scalar. -/
theorem LeafNodeChart.frameUnitIso_pullback_left :
    (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
        (h.frameUnitIso f L leftFrame rightFrame).hom ≫
      (schemeModulePullbackUnitIso
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).hom ≫
      schemeScalarEnd (h.frameScalarSection f L leftFrame rightFrame) =
    leftFrame.hom := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact closedFrameUnitIso_pullback_left k Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support L
    leftFrame rightFrame h.cover

section OpenRestriction

open SchemeModuleRestriction

variable (V : (Spec (CommRingCat.of Γ(X, U.1))).Opens)

/-- The restriction of the affine leaf-node trivialization to an open of the
chart, with the actual structure module of the open subscheme. -/
def LeafNodeChart.frameUnitOpenIso :
    (restriction V.ι).obj L.obj ≅ _root_.SheafOfModules.unit V.toScheme.ringCatSheaf :=
  (restriction V.ι).mapIso (h.frameUnitIso f L leftFrame rightFrame) ≪≫
    restrictionUnitIso V.ι

/-- On every open of the chart, the right pullback of the restricted
trivialization is the restriction of the given right frame. -/
theorem LeafNodeChart.frameUnitOpenIso_pullback_right :
    (schemeModulePullback
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)) ∣_ V)).map
        (h.frameUnitOpenIso f L leftFrame rightFrame V).hom ≫
      (schemeModulePullbackUnitIso
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)) ∣_ V)).hom =
    (closedComponentFrameOpenIso Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U) L
      rightFrame V).hom := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact closedFrameUnitOpenIso_pullback_right k Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support L
    leftFrame rightFrame h.cover V

/-- On every open of the chart, the left pullback of the restricted
trivialization is the restriction of the given left frame after the SAME
lifted node scalar. -/
theorem LeafNodeChart.frameUnitOpenIso_pullback_left :
    (schemeModulePullback
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ∣_ V)).map
        (h.frameUnitOpenIso f L leftFrame rightFrame V).hom ≫
      (schemeModulePullbackUnitIso
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ∣_ V)).hom ≫
      schemeScalarEnd
        (((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ⁻¹ᵁ V).ι.appTop
          (h.frameScalarSection f L leftFrame rightFrame)) =
    (closedComponentFrameOpenIso Γ(X, U.1) (componentChartIdeal X {C} U) L
      leftFrame V).hom := by
  letI := affineSectionsAlgebra f U.2
  letI : Algebra.FiniteType k Γ(X, U.1) := affineSectionsAlgebra_finiteType f U.2
  letI := h.isReduced
  exact closedFrameUnitOpenIso_pullback_left k Γ(X, U.1) (componentChartIdeal X {C} U)
    (componentChartIdeal X ({C}ᶜ) U) (U.2.primeIdealOf ⟨q, hq⟩) h.support L
    leftFrame rightFrame h.cover V

end OpenRestriction

end AffineChart

section Curve

variable {X : Scheme.{u}} [NoetherianSpace X] (L : InvertibleSheaf X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)
  (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
  (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf)

/-- The node scalar of the curve-level frames at the leaf-node chart. -/
def LeafNodeChart.chartScalar : kˣ :=
  h.frameScalar f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC')

/-- The lifted node scalar of the curve-level frames on the leaf piece. -/
def LeafNodeChart.chartScalarSection :
    Γ(Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X {C} U)), ⊤) :=
  h.frameScalarSection f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC')

/-- The chart trivialization pulls back to the transported complement frame. -/
theorem LeafNodeChart.chartUnitIso_pullback_right :
    (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).map
        (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
      (schemeModulePullbackUnitIso
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U))).hom =
    (componentChartFrame X ({C}ᶜ) U L frameC').hom :=
  h.frameUnitIso_pullback_right f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC')

/-- The chart trivialization pulls back to the transported leaf frame after
the lifted node scalar. -/
theorem LeafNodeChart.chartUnitIso_pullback_left :
    (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).map
        (LeafNodeChart.chartUnitIso L f h frameC frameC').hom ≫
      (schemeModulePullbackUnitIso
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U))).hom ≫
      schemeScalarEnd (h.chartScalarSection L f frameC frameC') =
    (componentChartFrame X {C} U L frameC).hom :=
  h.frameUnitIso_pullback_left f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC')

section OpenRestriction

open SchemeModuleRestriction

variable (V : (Spec (CommRingCat.of Γ(X, U.1))).Opens)

/-- The chart trivialization restricted to an open of the affine chart. -/
def LeafNodeChart.chartUnitOpenIso :
    (restriction V.ι).obj ((schemeModulePullback U.2.fromSpec).obj L.obj) ≅
      _root_.SheafOfModules.unit V.toScheme.ringCatSheaf :=
  h.frameUnitOpenIso f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC') V

/-- On every open of the chart, the right pullback of the restricted chart
trivialization is the restricted transported complement frame. -/
theorem LeafNodeChart.chartUnitOpenIso_pullback_right :
    (schemeModulePullback
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)) ∣_ V)).map
        (h.chartUnitOpenIso L f frameC frameC' V).hom ≫
      (schemeModulePullbackUnitIso
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)) ∣_ V)).hom =
    (closedComponentFrameOpenIso Γ(X, U.1) (componentChartIdeal X ({C}ᶜ) U)
      (pullbackInvertibleSheaf U.2.fromSpec L)
      (componentChartFrame X ({C}ᶜ) U L frameC') V).hom :=
  h.frameUnitOpenIso_pullback_right f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC') V

/-- On every open of the chart, the left pullback of the restricted chart
trivialization is the restricted transported leaf frame after the SAME
lifted node scalar. -/
theorem LeafNodeChart.chartUnitOpenIso_pullback_left :
    (schemeModulePullback
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ∣_ V)).map
        (h.chartUnitOpenIso L f frameC frameC' V).hom ≫
      (schemeModulePullbackUnitIso
        ((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ∣_ V)).hom ≫
      schemeScalarEnd
        (((closedComponentInclusion Γ(X, U.1) (componentChartIdeal X {C} U)) ⁻¹ᵁ V).ι.appTop
          (h.chartScalarSection L f frameC frameC')) =
    (closedComponentFrameOpenIso Γ(X, U.1) (componentChartIdeal X {C} U)
      (pullbackInvertibleSheaf U.2.fromSpec L)
      (componentChartFrame X {C} U L frameC) V).hom :=
  h.frameUnitOpenIso_pullback_left f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC') V

end OpenRestriction

end Curve

end KltDP.Geometry.RationalTreePicard
