import KltDP.Geometry.ChartKaehlerFreeSheaf
import KltDP.Geometry.ModuleOpenOverEquivalence
import KltDP.Geometry.FiniteLocallyFreeCoherent

/-!
# The chart's free presentation of `Ω`, moved to the over site

`ChartKaehlerFreeSheaf.chartFreeIso` presents `Ω_{X/k}` on an affine chart as a free sheaf, but on
`U.toScheme` — indexed by opens of the *open subscheme*. The atlas needs it indexed by opens of `X`
lying below `U`, which is the over site `X.ringCatSheaf.over U`. That is route 1's third cost, and
the accepted tree already carries the bridge:

* `openToOverFunctor U : U.toScheme.Modules ⥤ SheafOfModules (X.ringCatSheaf.over U)`,
* `openToOverFreeIso U I : free (R := X.ringCatSheaf.over U) I ≅ (openToOverFunctor U).obj (free …)`,
* `openToOverRestrictionIso U M : (openToOverFunctor U).obj ((restriction U.ι).obj M) ≅ M.over U`.

* **`chartOverFreeIso`**: composing the three, a chart frame gives
  `free (R := X.ringCatSheaf.over U) I ≅ (baseRingSheaf f).over U`.
* **`chartOverFreeIsoFin`**: the `Fin n`-parameterised form, at index `ULift (Fin n)`.

This is the same three-step composition the accepted
`SmoothKaehlerLocallyFree.exists_finite_localBases` performs on its chosen index; the only difference
is that the index here comes from a given frame rather than from `Module.Free.ChooseBasisIndex`, so
the result is a named isomorphism rather than an existence statement.

**The two sheafification instances are re-declared.** `schemeOverHasWeakSheafify` and
`schemeOverWEqualsLocallyBijective` are accepted but are `local instance`s, which die at their
namespace `end` and do not reach importing modules; the accepted `SmoothKaehlerLocallyFree`
re-declares them for exactly this reason, and so must this module. They are named, as the rules
require.

Nothing is admitted here. This module does **not** produce a `Basis` of sections; that is
`KltDP.Compatibility.FreeSheafSections.freeSectionsBasis`, which is stated for an arbitrary site.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KltDP.Geometry.SchemeKaehlerSheaf KltDP.Geometry.SchemeModuleRestriction
open KltDP.Geometry.ChartKaehlerFreeSheaf

universe u

namespace KltDP.Geometry.ChartKaehlerOverFree

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- Re-declaration of the accepted sheafification instance on an over site: the accepted one is
`local` and does not reach importing modules. -/
local instance laneOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  schemeOverHasWeakSheafify X U

/-- Re-declaration of the accepted local-bijectivity instance on an over site, for the same reason. -/
local instance laneOverWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} :=
  schemeOverWEqualsLocallyBijective X U

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- **A chart frame presents `Ω_{X/k}` on the chart as a free sheaf, on the over site** — that is,
indexed by the opens of `X` lying below the chart, which is what the atlas consumes. -/
def chartOverFreeIso {U : X.Opens} (hU : IsAffineOpen U) {I : Type u} [Finite I] :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    Basis I Γ(X, U) (KaehlerDifferential k Γ(X, U)) →
      (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
        (baseRingSheaf f).over U) := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  intro b
  exact openToOverFreeIso U I ≪≫
    (openToOverFunctor U).mapIso (chartFreeIso f hU b) ≪≫
    openToOverRestrictionIso U (baseRingSheaf f)

/-- **The same, for a frame indexed by `Fin n`**, at index `ULift (Fin n)`. -/
def chartOverFreeIsoFin {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} :
    letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
    Basis (Fin n) Γ(X, U) (KaehlerDifferential k Γ(X, U)) →
      (_root_.SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ≅
        (baseRingSheaf f).over U) := by
  letI : Algebra k Γ(X, U) := (baseToAffineSectionsMap f hU).hom.toAlgebra
  exact fun b => chartOverFreeIso f hU (b.reindex (Equiv.ulift.{u, 0} (α := Fin n)).symm)

end KltDP.Geometry.ChartKaehlerOverFree
