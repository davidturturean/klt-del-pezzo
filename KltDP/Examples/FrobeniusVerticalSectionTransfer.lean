import KltDP.Examples.FrobeniusVerticalTranslationEquation
import KltDP.Examples.FrobeniusFiberZeroInvertible
import KltDP.Geometry.GluedSubschemeStalkKernel

/-!
# The vertical chart section as a ring element, and the translated chart join (BRIEF51)

The remaining gap is the **section-level** translation transfer: Leg 2 proved the two presentations of
`x = c` agree as elements of `planeRing k`, and `verticalZeroChartEquation` is the *section* corresponding
to `uCoord`. This module supplies the two pieces that convert between the two worlds, both stated so that
no dependent cast can form.

**On the honesty of the first lemma.** `chartSectionsEquiv j` is
`(j.appIso ⊤) ≫ ΓSpecIso` and `chartSectionsEquiv_symm_apply` is `rfl`, while
`verticalZeroChartEquation j` is *defined* as `((productChart 0 j).appIso ⊤).inv.hom ((ΓSpecIso _).inv.hom uCoord)`.
So `chartSectionsEquiv_verticalZeroChartEquation` is `RingEquiv.apply_symm_apply` — **true by
construction**, the same shape this lane flagged in `crossingStalkEquiv_germ_lineParameterSection`. It is
recorded as such deliberately. The difference is what is being claimed: that lemma asserted a *germ coming
from an actual section* was the local parameter, which is a geometric claim its construction had already
assumed; this one only writes down the dictionary between a chart section and its ring element, and the
geometric content stays where it belongs — in Leg 2's ring identity and in the germ transport. A
bookkeeping identity may be true by construction; a content claim may not.

**The chart used is `productChart 0 0`, not `planeChart`.** `verticalZeroChartEquation` lives in
`Γ(_, productChart 0 j ''ᵁ ⊤)`, and `productOpen 0 0 = planeChart ''ᵁ ⊤` holds only propositionally, so
applying `chartSectionsEquiv planeChart` to it would not typecheck without a cast. Everything is therefore
phrased at `productChart 0 j`, whose image open is definitionally right.

* **`chartSectionsEquiv_verticalZeroChartEquation`** — the divisor's chart section is `uCoord`;
* **`productChart_verticalTranslation`** — the morphism-level join at the chart the section actually lives
  over. Rewriting `productChart_zero_zero` is safe **here** because the morphism sits inside a composition
  `≫`, which carries no instance argument — unlike `''ᵁ`, `app` and `opensRange`, where the same rewrite
  does not elaborate.

**Not proved here**: pushing `.app` through this join and landing the product germ on `localParameter c`.
That needs the `appIso`-level computation of the translated section and remains the last step before the
rows; no row is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusVerticalSectionTransfer

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusProductPlaneChart FrobeniusTranslatedCharts
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusFiberZeroInvertible FrobeniusVerticalFiberClass
open FrobeniusVerticalFiberTranslated FrobeniusVerticalTranslationEquation

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

/-- **The divisor's chart section corresponds to the ring element `uCoord`.**
True by construction — `verticalZeroChartEquation` is defined as the `chartSectionsEquiv`-preimage of
`uCoord` and `chartSectionsEquiv_symm_apply` is `rfl` — and recorded as such. It is the dictionary between
the section and the ring element, not a geometric claim. -/
theorem chartSectionsEquiv_verticalZeroChartEquation (j : Fin 2) :
    chartSectionsEquiv (productChart (k := k) 0 j) (verticalZeroChartEquation j) = uCoord := by
  change chartSectionsEquiv (productChart (k := k) 0 j)
    ((chartSectionsEquiv (productChart (k := k) 0 j)).symm uCoord) = uCoord
  exact RingEquiv.apply_symm_apply _ _

/-- **The translation join at the chart the section lives over.** The accepted
`verticalTranslation_planeChart` is stated for `planeChart`; `productChart_zero_zero` moves it to
`productChart 0 0`. The rewrite is legitimate because the morphism occurs inside a composition, which has
no instance argument — the same rewrite underneath `''ᵁ` or `app` would not elaborate. -/
theorem productChart_verticalTranslation (c : k) :
    productChart (k := k) 0 0 ≫ (verticalTranslation (k := k) c).inv =
      (planeTranslationIso (-c) (-(0 : k))).hom ≫ productChart (k := k) 0 0 := by
  rw [productChart_zero_zero]
  exact verticalTranslation_planeChart c

end KltDP.Examples.FrobeniusVerticalSectionTransfer

namespace KltDP.Examples

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusProductPlaneChart FrobeniusTranslatedCharts
open FrobeniusGraphPicardClassCharts FrobeniusVerticalFiberClass
open FrobeniusVerticalFiberTranslated FrobeniusVerticalSectionTransfer

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **F29: the vertical chart section is `uCoord`, and the translation join holds at that chart.** The two
conversions between the section world and the ring world in which Leg 2's identity is stated. -/
theorem f29_vertical_section_transfer (k : Type u) [Field k] (c : k) (j : Fin 2) :
    chartSectionsEquiv (productChart (k := k) 0 j) (verticalZeroChartEquation j) = uCoord ∧
      productChart (k := k) 0 0 ≫ (verticalTranslation (k := k) c).inv =
        (planeTranslationIso (-c) (-(0 : k))).hom ≫ productChart (k := k) 0 0 :=
  ⟨chartSectionsEquiv_verticalZeroChartEquation j, productChart_verticalTranslation c⟩

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_section_transfer_universe_check (k : Type u) [Field k] (c : k) (j : Fin 2) :
    True := by
  have _ := f29_vertical_section_transfer.{u} k c j
  trivial

end KltDP.Examples
