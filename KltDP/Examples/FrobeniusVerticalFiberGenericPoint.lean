import KltDP.Examples.FrobeniusVerticalFiberTranslated
import KltDP.Geometry.CartierDivisorPullbackSupport
import KltDP.Examples.FrobeniusGraphPicardClassRational
import KltDP.Examples.FrobeniusGraphPicardClassCoordinateComparison
import KltDP.Geometry.RationalFunctionSheaf

/-!
# The generic point of `P¹ × P¹` is off the vertical fibre (BRIEF40)

`NotInSupport` needs a point to be shown off the support of a divisor, and across the accepted tree
**nothing ever produces such a fact** — the condition appears only as a hypothesis binder. This module
produces the first one, for the generic point of the product and the vertical fibre `x = c`.

The content is that `u` does not vanish identically: the germ of the chart coefficient at the generic
point *is* the accepted rational function `rationalX`, which is `rulingLeft 0` and nonzero. Two
observations make that a `rfl`-level identification rather than a computation:

* `germToFunctionField U` **is** the germ at the generic point and `functionField` **is** the stalk
  there (both `abbrev` in Mathlib's `FunctionField`), so no factoring is needed;
* `diagonalOpen 0 = productChart 0 0 ''ᵁ ⊤ = productOpen 0 0`, and `verticalZeroChartEquation 0` is
  literally the inner composite of `chartFunctionFieldMap 0` applied to `uCoord` — so
  `rationalX = germToFunctionField (diagonalOpen 0) (verticalZeroChartEquation 0)`.

The translated fibre `x = c` then comes for free from this lane's own
`mem_support_pullbackDivisor_iff`, since `verticalFiberDivisorAt c` is by construction a
`pullbackDivisor` along the translation, and an isomorphism preserves the generic point.

* **`genericPoint_not_mem_support_verticalZero`** — the generic point is off `Supp(x = 0)`;
* **`genericPoint_not_mem_support_verticalFiberAt`** — and off `Supp(x = c)`, every `c`.

**Not proved here, and not to be confused with it**: the corresponding statement for the *graph's*
generic point, which is what `(graphStrictPrimeCurve …).NotInSupport` actually requires. The graph is a
curve in the surface, so its generic point is **not** the product's; `projectiveGraphMorphism` is a
closed immersion with no dominance, so Mathlib's `genericPoint_eq_of_isOpenImmersion` does not transport
between them. That step remains open and is stated in the record.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusVerticalFiberGenericPoint

open KltDP.Geometry
open KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
open FrobeniusProjectivePoints
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassFrames
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassCoordinateComparison
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassIntegral
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated

variable {k : Type u} [Field k]

local instance genericProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The generic point lies in the chart open `productOpen 0 0`, which is nonempty. -/
theorem genericPoint_mem_productOpen_zero :
    genericPoint (projectiveProduct k) ∈ productOpen (k := k) 0 0 :=
  genericPoint_mem_nonempty_open _ _

/-- The germ of the vertical chart coefficient at the generic point is the accepted `rationalX`:
`germToFunctionField` is the germ at the generic point, and the chart open `productOpen 0 0` is
`diagonalOpen 0`. -/
theorem germ_verticalZeroChartEquation_eq_rationalX :
    (projectiveProduct k).presheaf.germ (productOpen (k := k) 0 0)
        (genericPoint (projectiveProduct k)) genericPoint_mem_productOpen_zero
        (verticalZeroChartEquation 0) =
      rationalX (k := k) := rfl

/-- **The generic point of `P¹ × P¹` is off the support of the fibre `x = 0`.** -/
theorem genericPoint_not_mem_support_verticalZero :
    genericPoint (projectiveProduct k) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations).support := by
  intro h
  rw [mem_support_iff_not_isUnit_germ (verticalZeroDivisor (k := k))
    verticalZeroDivisor_hasRegularEquations (verticalZeroChartZero 0)
    (genericPoint (projectiveProduct k)) genericPoint_mem_productOpen_zero] at h
  apply h
  have hx : (projectiveProduct k).presheaf.germ (productOpen (k := k) 0 0)
      (genericPoint (projectiveProduct k)) genericPoint_mem_productOpen_zero
      (verticalZeroChartEquation 0) = rationalX (k := k) :=
    germ_verticalZeroChartEquation_eq_rationalX
  change IsUnit ((projectiveProduct k).presheaf.germ (productOpen (k := k) 0 0)
    (genericPoint (projectiveProduct k)) genericPoint_mem_productOpen_zero
    (verticalZeroChartEquation 0))
  rw [hx, rationalX_eq_rulingLeft]
  exact isUnit_iff_ne_zero.mpr (rulingLeft_ne_zero 0)

/-- **The generic point of `P¹ × P¹` is off the support of the fibre `x = c`, for every `c`.**
The translated fibre is a `pullbackDivisor` along an isomorphism, so this lane's
`mem_support_pullbackDivisor_iff` reduces it to the case `c = 0`. -/
theorem genericPoint_not_mem_support_verticalFiberAt (c : k) :
    genericPoint (projectiveProduct k) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support := by
  intro h
  -- `verticalFiberDivisorAt c` *is* `pullbackDivisor (verticalTranslation c).inv …` by definition,
  -- so the criterion applies to `h` up to defeq. `rw` cannot: it needs equation lemmas for the
  -- `def`, which is why `rw [verticalFiberDivisorAt] at h` failed. `.mp` works where `rw` does not.
  have h' := (mem_support_pullbackDivisor_iff (verticalTranslation c).inv
    (verticalZeroDivisor (k := k)) verticalZeroDivisor_hasRegularEquations
    (genericPoint (projectiveProduct k))).mp h
  rw [GenericPointPreserving.base_genericPoint (π := (verticalTranslation (k := k) c).inv)] at h'
  exact genericPoint_not_mem_support_verticalZero h'

end KltDP.Examples.FrobeniusVerticalFiberGenericPoint

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open FrobeniusVerticalFiberGenericPoint FrobeniusGraphPicardClassIntegral

-- A `local instance` dies at the `end` of its namespace block, so integrality is re-declared here
-- with explicit binders (the pattern that works in `FrobeniusStageVerticalDivisor`).
local instance genericProductIntegral' {k : Type u} [Field k] : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **F29: the generic point of `P¹ × P¹` lies off every vertical fibre `x = c`** — the first
statement in the development that *produces* a `∉ support` fact rather than assuming one. -/
theorem f29_generic_point_off_vertical_fiber (k : Type u) [Field k] (c : k) :
    genericPoint (projectiveProduct k) ∉
      (effectiveCartierIdealDataOfRegularEquations (projectiveProduct k)
        (verticalFiberDivisorAt (k := k) c)
        (verticalFiberDivisorAt_hasRegularEquations c)).support :=
  genericPoint_not_mem_support_verticalFiberAt c

/-- The statement has exactly one universe parameter. -/
theorem f29_generic_point_off_vertical_fiber_universe_check (k : Type u) [Field k] (c : k) :
    True := by
  have _ := f29_generic_point_off_vertical_fiber.{u} k c
  trivial

end KltDP.Examples
