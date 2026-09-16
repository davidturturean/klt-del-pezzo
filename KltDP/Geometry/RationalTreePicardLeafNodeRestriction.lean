import KltDP.Geometry.RationalTreePicardLeafNodeChart
import KltDP.Geometry.SchemeModuleFunctorial
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Component frames restrict to the closed pieces of a leaf-node chart

An actual frame of the pullback of an original line bundle `L` on `X` to a
closed component union `Z_S` restricts, through the existing chart
identification `Spec (Γ(X, U) ⧸ I_S) ≅ Z_S ∩ U`, to a frame of the pullback
of `L|_U` to the affine closed piece `Spec (Γ(X, U) ⧸ I_S)`. The transport
uses only the existing pullback composition and unit comparisons and the
proved equation `Spec(A/I) → Spec A → X = Spec(A/I) ≅ Z_S ∩ U → Z_S → X`.

Consequently an original line bundle on an actual reduced curve that is
trivialized on the leaf component union and on the union of the other
components is trivial on the leaf-node chart `Spec Γ(X, U)`, by the affine
closed-frame descent assembled in `RationalTreePicardLeafNodeChart`.

Remaining geometric hypotheses are those of `LeafNodeChart` (dimension one,
component-point tree, transverse branch germs); the two component frames are
inputs here. Producing them from degree zero on projective-line components,
and gluing the chart trivializations over a global cover with the tree
potential, are the next connections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X)) (U : X.affineOpens)

/-- The affine closed piece of a component union lies over the affine chart
through the existing chart identification and the original inclusions. -/
theorem closedComponentInclusion_fromSpec :
    closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U) ≫ U.2.fromSpec =
      (componentUnionChartIso X S U).hom ≫
        (componentUnionInclusion X S ⁻¹ᵁ U.1).ι ≫ componentUnionInclusion X S := by
  refine (componentUnionChartIso_hom_over X S U).symm.trans ?_
  rw [morphismRestrict_ι]

variable (L : InvertibleSheaf X)

/-- A frame of the pullback to a closed component union restricts to a frame
of the pullback of the chart restriction to the affine closed piece. -/
def componentChartFrame
    (frame : (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :
    (schemeModulePullback
        (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U))).obj
        ((schemeModulePullback U.2.fromSpec).obj L.obj) ≅
      _root_.SheafOfModules.unit
        (Spec (CommRingCat.of (Γ(X, U.1) ⧸ componentChartIdeal X S U))).ringCatSheaf :=
  let ι := componentUnionInclusion X S
  let V := ι ⁻¹ᵁ U.1
  let e := componentUnionChartIso X S U
  (schemeModulePullbackCompIso
      (closedComponentInclusion Γ(X, U.1) (componentChartIdeal X S U)) U.2.fromSpec).app
        L.obj ≪≫
    (eqToIso (congrArg schemeModulePullback
      (closedComponentInclusion_fromSpec X S U))).app L.obj ≪≫
    ((schemeModulePullbackCompIso e.hom (V.ι ≫ ι)).app L.obj).symm ≪≫
    (schemeModulePullback e.hom).mapIso
      (((schemeModulePullbackCompIso V.ι ι).app L.obj).symm ≪≫
        (schemeModulePullback V.ι).mapIso frame ≪≫
        schemeModulePullbackUnitIso V.ι) ≪≫
    schemeModulePullbackUnitIso e.hom

section LeafNode

variable {X} {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)

/-- An original line bundle on the curve with actual frames on the leaf
component union and on the complementary union is trivial on the leaf-node
chart, by transport of the frames to the closed pieces and affine descent. -/
def LeafNodeChart.chartUnitIso
    (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
    (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) :
    (schemeModulePullback U.2.fromSpec).obj L.obj ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of Γ(X, U.1))).ringCatSheaf :=
  h.frameUnitIso f (pullbackInvertibleSheaf U.2.fromSpec L)
    (componentChartFrame X {C} U L frameC) (componentChartFrame X ({C}ᶜ) U L frameC')

end LeafNode

end KltDP.Geometry.RationalTreePicard
