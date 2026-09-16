import KltDP.Examples.FrobeniusGraphVerticalContact
import KltDP.Examples.FrobeniusVerticalFiberTranslated
import KltDP.Examples.FrobeniusTranslatedCharts
import KltDP.Examples.ProjectiveProductTranslation
import KltDP.Examples.FrobeniusGraphPicardClassCharts
import KltDP.Examples.FrobeniusProductPlaneChart

/-!
# The two presentations of the vertical fibre `x = c` agree (BRIEF48, Leg 2)

The divisor and the graph disagree about what "the equation of `x = c`" *is*, and nothing identified them:

* the **divisor** presents `x = c` as the pullback of `x = 0` along the translation. Its chart coefficient
  is `(verticalTranslation c).inv.app _ (verticalZeroChartEquation j)` — the *translate* of the coordinate
  `u`, by `verticalFiberDivisorAt_chart_coefficient`, which is `rfl`;
* **`FrobeniusGraphVerticalContact`** uses `fiberEquation c = ratio k 1 0 − constants k 1 c`, the equation
  of the point `c` **directly**, pulled back by `parameterMap 1` to `X₀ − C c`. The translation is absorbed
  there and never matched against the divisor's presentation.

This module supplies the identification, and only that. It is stated **entirely at ring and morphism
level**, never as a section transport: `f.app U` has type `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`, whose type mentions
`f`, so an equation between a translated section and an untranslated one is a dependent cast — the rule
established in Leg 1. Here the translated and untranslated charts genuinely have different opens
(`(verticalTranslation c).inv ⁻¹ᵁ productOpen 0 0` against `productOpen 0 0`), so a section-level equation
could not even be stated without one. Rewriting the *morphism* first avoids it completely.

* **`coordinateTranslation_uCoord_neg`** — the translate of `u` is `u − c` in `planeRing k`;
* **`firstCoordinateMap_parameterEquation`** — the P¹ equation `X − C c` of the point `c` maps to the same
  `u − c` under the accepted first-coordinate map;
* **`coordinateTranslation_uCoord_eq_pulledVertical`** — hence the translate of `u` **is** the image of the
  graph-side equation `pulledVerticalEquation c` of `FrobeniusGraphVerticalContact`. This is Leg 2: the two
  presentations are the same element of `planeRing k`;
* **`verticalTranslation_planeChart`** — the morphism-level join
  `planeChart ≫ (verticalTranslation c).inv = (planeTranslationIso (-c) (-0)).hom ≫ planeChart`, the form a
  consumer rewrites with *before* taking `app`;
Deliberately **not** stated here: that the divisor's chart open at `j = 0` is the plane chart's image.
It is true — `productChart 0 0 = planeChart` is accepted — but `f ''ᵁ ⊤` carries an `[IsOpenImmersion f]`
instance argument, so `congrArg (fun f => f ''ᵁ ⊤)` does not elaborate: the bound `f` has no such instance.
A third variant of the dependency family, running through a *typeclass* argument rather than through the
type. Leg 3 should reach it via `Opens.ext` and `Set.range _.base`, which carries no instance.

Everything is characteristic-free and holds for every `c`, `c = 0` included.

**Not proved here**: Leg 3 — the tower transport down the blowdown and the remaining chart-open
bookkeeping, where `c ≠ 0` first enters (through stage-puncture membership).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalTranslationEquation

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusProductPlaneChart FrobeniusTranslatedCharts
open ProjectiveProductTranslation
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphContact FrobeniusGraphVerticalContact
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- **The translate of the plane coordinate `u` is `u − c`.** The inverse vertical translation is
`productTranslation (-c) (-0)`, so the accepted `coordinateTranslation_u` gives `u + (-c)`. -/
theorem coordinateTranslation_uCoord_neg (c : k) :
    coordinateTranslation (-c) (-(0 : k)) (uCoord (k := k)) = uCoord - planeConstants c := by
  rw [coordinateTranslation_u, map_neg, ← sub_eq_add_neg]

/-- **The `P¹` equation of the point `c` maps to the same element.** `X − C c` is the equation of `t = c`
on the parameter line; the accepted first-coordinate map carries it to `u − c`. -/
theorem firstCoordinateMap_parameterEquation (c : k) :
    firstCoordinateMap (Polynomial.X - Polynomial.C c) = uCoord (k := k) - planeConstants c := by
  rw [map_sub, firstCoordinateMap_X, firstCoordinateMap_C]

/-- **Leg 2: the divisor's presentation and the graph's presentation are the same element.**
The translate of `u` — what the Cartier chart of `verticalFiberDivisorAt c` carries — is exactly the image
of `pulledVerticalEquation c`, the equation `FrobeniusGraphVerticalContact` pulls back along the graph's
first coordinate. Neither side is changed; they are identified. -/
theorem coordinateTranslation_uCoord_eq_pulledVertical (c : k) :
    coordinateTranslation (-c) (-(0 : k)) (uCoord (k := k)) =
      firstCoordinateMap (parameterPolynomialEquiv (pulledVerticalEquation c)) := by
  rw [coordinateTranslation_uCoord_neg, parameterPolynomialEquiv_pulledVerticalEquation,
    firstCoordinateMap_parameterEquation]

/-- The same, stated against the bare polynomial equation of the point `c`. -/
theorem coordinateTranslation_uCoord_eq_firstCoordinateMap (c : k) :
    coordinateTranslation (-c) (-(0 : k)) (uCoord (k := k)) =
      firstCoordinateMap (Polynomial.X - Polynomial.C c) := by
  rw [coordinateTranslation_uCoord_neg, firstCoordinateMap_parameterEquation]

/-- **The morphism-level translation/chart join for the vertical translation.** This is the form to
rewrite with *before* taking `app`; doing it in this order is what keeps every subsequent step free of a
dependent cast. -/
theorem verticalTranslation_planeChart (c : k) :
    planeChart ≫ (verticalTranslation (k := k) c).inv =
      (planeTranslationIso (-c) (-(0 : k))).hom ≫ planeChart := by
  rw [verticalTranslation_inv]
  exact planeChart_productTranslation (-c) (-(0 : k))

end KltDP.Examples.FrobeniusVerticalTranslationEquation

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusBlowupContact FrobeniusBlowupSmooth
open FrobeniusProductPlaneChart FrobeniusTranslatedCharts
open FrobeniusGraphContact FrobeniusGraphVerticalContact
open FrobeniusVerticalFiberTranslated FrobeniusVerticalTranslationEquation

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **F29: the two presentations of the vertical fibre `x = c` agree.** The Cartier chart of
`verticalFiberDivisorAt c` carries the *translate* of the plane coordinate `u`; the graph development
pulls back the equation of the point `c` directly. They are the same element of `planeRing k`, and the
corresponding chart morphisms are joined at morphism level. Characteristic-free, every `c`. -/
theorem f29_vertical_translation_equation (k : Type u) [Field k] (c : k) :
    coordinateTranslation (-c) (-(0 : k)) (uCoord (k := k)) =
        firstCoordinateMap (parameterPolynomialEquiv (pulledVerticalEquation c)) ∧
      planeChart ≫ (verticalTranslation (k := k) c).inv =
        (planeTranslationIso (-c) (-(0 : k))).hom ≫ planeChart :=
  ⟨coordinateTranslation_uCoord_eq_pulledVertical c, verticalTranslation_planeChart c⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_translation_equation_universe_check (k : Type u) [Field k] (c : k) : True := by
  have _ := f29_vertical_translation_equation.{u} k c
  trivial

end KltDP.Examples
