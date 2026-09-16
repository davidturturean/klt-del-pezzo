import KltDP.Geometry.RationalTreePicardLeafNodeRestriction
import KltDP.Geometry.ProjectiveLineSheafExponent

/-!
# Component frames from exponent zero on a projective-line component

An actual frame of the pullback of an original line bundle `L` to a closed
component union `Z_S` was an input of the leaf-node chart trivialization.
Here that frame is produced from the manuscript's degree-zero hypothesis
in the form the project currently has for the projective line: if `Z_S` is
identified with `projectiveSpace k 1` by an actual scheme isomorphism `e`,
and the transition exponent (existing `ProjectiveLineSheafExponent.exponent`)
of the transported sheaf `e⁻¹^* (L|_{Z_S})` is zero, then the existing
`unitIsoOfExponentZero` trivializes it on the projective line, and pullback
along `e` with the proved identity/composition/unit comparisons of scheme
module pullback returns a frame of `L|_{Z_S}` itself. Conversely a frame
forces exponent zero, so the exponent-zero condition is intrinsic to `L|_{Z_S}`
and does not depend on the chosen identification.

Consequences at a leaf node `q` of an actual reduced Noetherian curve with
tree component-point incidence graph and transverse branch germs
(`LeafNodeChart`): an original line bundle on `X` with zero component exponent
on the leaf component `C` (a copy of the projective line) and an actual frame
on the union of the other components is trivial on every affine chart through
`q`. If the union of the other components is itself a copy of the projective
line with zero component exponent, no frame input remains: the chart
trivialization follows from the two exponent-zero conditions alone.

Remaining geometric hypotheses (stated, not derived here): the identifications
of the component unions with the projective line are inputs (the manuscript's
"components are copies of P^1"); the "degree zero" hypothesis is expressed as
the existing transition exponent, whose comparison with an independently
defined multidegree is still open; and the `LeafNodeChart` inputs (dimension
one, component-point tree, transverse branch germs) are inherited. Gluing the
chart trivializations over a global cover with the tree potential, and the
inductive passage to the complementary union, remain the next connections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

section Transport

variable {Y Z : Scheme.{u}} (e : Y ≅ Z)

/-- Pulling an actual module sheaf back along a scheme isomorphism and then
along its inverse returns the original sheaf, by the proved composition and
identity comparisons of scheme module pullback. -/
def pullbackInvPullbackIso (M : Y.Modules) :
    (schemeModulePullback e.hom).obj ((schemeModulePullback e.inv).obj M) ≅ M :=
  (schemeModulePullbackCompIso e.hom e.inv).app M ≪≫
    (eqToIso (congrArg schemeModulePullback e.hom_inv_id)).app M ≪≫
    (schemeModulePullbackIdIso Y).app M

/-- A trivialization of the transported sheaf on the target of an actual
scheme isomorphism gives a trivialization of the original sheaf on the source. -/
def unitIsoOfPullbackUnitIso (M : Y.Modules)
    (t : (schemeModulePullback e.inv).obj M ≅ _root_.SheafOfModules.unit Z.ringCatSheaf) :
    M ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  (pullbackInvPullbackIso e M).symm ≪≫ (schemeModulePullback e.hom).mapIso t ≪≫
    schemeModulePullbackUnitIso e.hom

/-- Conversely, a trivialization of the original sheaf transports to the target. -/
def pullbackUnitIsoOfUnitIso (M : Y.Modules)
    (t : M ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    (schemeModulePullback e.inv).obj M ≅ _root_.SheafOfModules.unit Z.ringCatSheaf :=
  (schemeModulePullback e.inv).mapIso t ≪≫ schemeModulePullbackUnitIso e.inv

end Transport

section ProjectiveLineChart

variable (k : Type u) [Field k] {Y : Scheme.{u}} (e : Y ≅ projectiveSpace k 1)

/-- The transition exponent of an invertible sheaf on a scheme identified with
the projective line, computed on the actual transported invertible sheaf. -/
def chartExponent (M : InvertibleSheaf Y) : ℤ :=
  ProjectiveLineSheafExponent.exponent k (pullbackInvertibleSheaf e.inv M)

/-- Zero chart exponent trivializes the original sheaf on the source scheme. -/
def unitIsoOfChartExponentZero (M : InvertibleSheaf Y) (h : chartExponent k e M = 0) :
    M.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf :=
  unitIsoOfPullbackUnitIso e M.obj
    (ProjectiveLineSheafExponent.unitIsoOfExponentZero k (pullbackInvertibleSheaf e.inv M) h)

/-- A trivialization of the original sheaf forces zero chart exponent. -/
theorem chartExponent_eq_zero_of_iso_unit (M : InvertibleSheaf Y)
    (t : M.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :
    chartExponent k e M = 0 :=
  ProjectiveLineSheafExponent.exponent_eq_zero_of_iso_unit k (pullbackInvertibleSheaf e.inv M)
    (pullbackUnitIsoOfUnitIso e M.obj t)

/-- Zero chart exponent is equivalent to an actual trivialization of the
original sheaf; in particular it does not depend on the identification. -/
theorem chartExponent_eq_zero_iff (M : InvertibleSheaf Y) :
    chartExponent k e M = 0 ↔
      Nonempty (M.obj ≅ _root_.SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨fun h => ⟨unitIsoOfChartExponentZero k e M h⟩,
    fun ⟨t⟩ => chartExponent_eq_zero_of_iso_unit k e M t⟩

/-- Two identifications with the projective line give the same zero-exponent
condition on the same original sheaf. -/
theorem chartExponent_eq_zero_congr (e' : Y ≅ projectiveSpace k 1) (M : InvertibleSheaf Y) :
    chartExponent k e M = 0 ↔ chartExponent k e' M = 0 := by
  rw [chartExponent_eq_zero_iff, chartExponent_eq_zero_iff]

end ProjectiveLineChart

section Component

variable (k : Type u) [Field k] (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X))
  (e : componentUnionScheme X S ≅ projectiveSpace k 1) (L : InvertibleSheaf X)

/-- The original line bundle restricted to the actual reduced closed union of
the selected components, as an invertible sheaf on that union. -/
abbrev componentUnionRestriction : InvertibleSheaf (componentUnionScheme X S) :=
  pullbackInvertibleSheaf (componentUnionInclusion X S) L

/-- The component exponent of `L` on the selected union, read through the
given identification of that union with the projective line. -/
def componentExponent : ℤ :=
  chartExponent k e (componentUnionRestriction X S L)

/-- Zero component exponent gives an actual frame of the pullback of `L` to
the selected closed component union. -/
def componentFrameOfExponentZero (h : componentExponent k X S e L = 0) :
    (schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf :=
  unitIsoOfChartExponentZero k e (componentUnionRestriction X S L) h

/-- The component exponent vanishes exactly when the pullback of `L` to the
selected union is trivial. -/
theorem componentExponent_eq_zero_iff :
    componentExponent k X S e L = 0 ↔
      Nonempty ((schemeModulePullback (componentUnionInclusion X S)).obj L.obj ≅
        _root_.SheafOfModules.unit (componentUnionScheme X S).ringCatSheaf) :=
  chartExponent_eq_zero_iff k e (componentUnionRestriction X S L)

end Component

section LeafNode

variable {X : Scheme.{u}} [NoetherianSpace X] (L : InvertibleSheaf X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)

/-- An original line bundle with zero component exponent on the leaf
component, identified with the projective line, and an actual frame on the
union of the other components is trivial on the leaf-node chart. -/
def LeafNodeChart.chartUnitIsoOfExponentZero
    (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (hzero : componentExponent k X {C} e L = 0)
    (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
      _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) :
    (schemeModulePullback U.2.fromSpec).obj L.obj ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of Γ(X, U.1))).ringCatSheaf :=
  LeafNodeChart.chartUnitIso L f h (componentFrameOfExponentZero k X {C} e L hzero) frameC'

/-- Two rational components meeting at a reduced node: when the leaf component
and the union of the other components are both identified with the projective
line and `L` has zero component exponent on each, `L` is trivial on every
affine chart through the node, with no frame input. -/
def LeafNodeChart.chartUnitIsoOfExponentZero₂
    (e : componentUnionScheme X {C} ≅ projectiveSpace k 1)
    (e' : componentUnionScheme X ({C}ᶜ) ≅ projectiveSpace k 1)
    (hzero : componentExponent k X {C} e L = 0)
    (hzero' : componentExponent k X ({C}ᶜ) e' L = 0) :
    (schemeModulePullback U.2.fromSpec).obj L.obj ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of Γ(X, U.1))).ringCatSheaf :=
  h.chartUnitIsoOfExponentZero L f e hzero
    (componentFrameOfExponentZero k X ({C}ᶜ) e' L hzero')

end LeafNode

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : Scheme.{u}) [NoetherianSpace X] [IsLocallyNoetherian X]
  [AlgebraicGeometry.IsReduced X] [Nontrivial ↥(irreducibleComponents X)]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

include f in
/-- On an actual reduced Noetherian curve with tree component-point incidence
graph and transverse branch germs, some component `C` meets the others in one
original point `q`, and every original line bundle with zero component exponent
on `C` (for any identification of `C` with the projective line) and an actual
frame on the other components is trivial on every affine chart through `q`. -/
theorem exists_leaf_chart_trivialization
    (hdim : topologicalKrullDim X ≤ 1)
    (hTree : (componentPointIncidenceGraph X).IsTree)
    (htrans : HasTransverseComponentBranches X) :
    ∃ (C : ↥(irreducibleComponents X)) (q : X),
      C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q} ∧
      ∀ (U : X.affineOpens) (hq : q ∈ U.1) (L : InvertibleSheaf X)
        (e : componentUnionScheme X {C} ≅ projectiveSpace k 1),
        componentExponent k X {C} e L = 0 →
        Nonempty ((schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
          _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf) →
        Nonempty ((schemeModulePullback U.2.fromSpec).obj L.obj ≅
          _root_.SheafOfModules.unit (Spec (CommRingCat.of Γ(X, U.1))).ringCatSheaf) := by
  obtain ⟨C, q, hcut, hcharts⟩ := exists_leafNodeChart X hdim hTree htrans
  refine ⟨C, q, hcut, fun U hq L e hzero ⟨frameC'⟩ => ?_⟩
  exact ⟨(hcharts U hq).chartUnitIsoOfExponentZero L f e hzero frameC'⟩

end Curve

end KltDP.Geometry.RationalTreePicard
