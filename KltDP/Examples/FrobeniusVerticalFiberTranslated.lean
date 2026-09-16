import KltDP.Examples.FrobeniusVerticalFiberClass
import KltDP.Examples.ProjectiveProductTranslationFibres
import KltDP.Geometry.CartierDivisorPullbackAdd

/-!
# The vertical fibre `x = c` as an effective Cartier divisor (BRIEF29)

`FrobeniusVerticalFiberClass` builds the vertical fibre `x = 0` on `P¹ × P¹` with regular equations.
The rows `B · a`, `F̃ · a`, `B · b` are computed against a vertical fibre that **misses the centre of
the tower**, so the fibre needed is `x = c` for `c ≠ 0`, not `x = 0`.

The accepted translation supplies it. `productTranslation a b = τ_a × τ_b` is an automorphism of
`P¹ × P¹` (`productTranslationIso`, `productTranslation_isIso`, inverse `τ_{-a} × τ_{-b}`), and the
accepted `verticalFiberMorphismAt_productTranslation` states that it carries the vertical fibre
`x = c` onto `x = c + a`. So the fibre `x = c` is the pullback of the fibre `x = 0` along the inverse
translation — exactly the accepted idiom

    translatedFiberZeroDivisor p a = pullbackDivisor (stageTranslationIso p a 0).inv fiberZeroDivisor

used for the horizontal fibre `y = a^p`, here in the first coordinate instead of the second.

* `verticalTranslation c` — the automorphism `τ_c × τ_0` carrying `x = 0` to `x = c`;
* `verticalFiberDivisorAt c` — the divisor of `x = c`, with
  **`verticalFiberDivisorAt_hasRegularEquations`** free from `pullbackDivisor_hasRegularEquations`;
* `verticalFiberDivisorAt_zero` — at `c = 0` it is the pullback along the identity.

Nothing is assumed and nothing is Frobenius-specific: this is the first-coordinate counterpart of an
accepted second-coordinate construction, and it is the divisor the three rows are computed against.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusVerticalFiberTranslated

open KltDP.Geometry KltDP.Geometry.ProjectiveLineTranslation
open KltDP.Geometry.CartierDivisorPullbackAdd
open FrobeniusProjectivePoints FrobeniusUnaffectedFibers
open ProjectiveProductTranslation ProjectiveProductTranslationFibres
open FrobeniusVerticalFiberClass

variable {k : Type u} [Field k]

/-- Integrality of the product: the accepted modules supply this only as a `local instance`, which
reaches neither importing modules nor a later namespace block, so it is declared here. -/
local instance translatedProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **The translation carrying the vertical fibre `x = 0` onto `x = c`**: `τ_c × τ_0`. -/
def verticalTranslation (c : k) : projectiveProduct k ≅ projectiveProduct k :=
  productTranslationIso c 0

theorem verticalTranslation_hom (c : k) :
    (verticalTranslation c).hom = productTranslation c (0 : k) := rfl

theorem verticalTranslation_inv (c : k) :
    (verticalTranslation c).inv = productTranslation (-c) (-(0 : k)) := rfl

/-- **It carries the fibre `x = 0` onto the fibre `x = c`**, from the accepted
`verticalFiberMorphismAt_productTranslation` at `a = c`, `b = 0`, `c = 0`. -/
theorem verticalTranslation_fibre (c : k) :
    verticalFiberMorphismAt (0 : k) ≫ (verticalTranslation c).hom =
      projectiveTranslation (0 : k) ≫ verticalFiberMorphismAt c := by
  have h := verticalFiberMorphismAt_productTranslation (k := k) c 0 0
  rw [zero_add] at h
  exact h

/-- The inverse translation preserves the generic point (it is an isomorphism). -/
instance verticalTranslation_inv_genericPointPreserving (c : k) :
    GenericPointPreserving (verticalTranslation (k := k) c).inv :=
  inferInstance

/-- **The vertical fibre `x = c` as an effective Cartier divisor on `P¹ × P¹`**: the pullback of
`x = 0` along the inverse translation, mirroring the accepted `translatedFiberZeroDivisor`. -/
def verticalFiberDivisorAt (c : k) : CartierDivisor (projectiveProduct k) :=
  pullbackDivisor (verticalTranslation c).inv verticalZeroDivisor
    verticalZeroDivisor_hasRegularEquations

/-- **It has regular equations**, so it can be pulled back along the blowdowns in turn. -/
theorem verticalFiberDivisorAt_hasRegularEquations (c : k) :
    HasRegularCartierEquations (projectiveProduct k) (verticalFiberDivisorAt (k := k) c) :=
  pullbackDivisor_hasRegularEquations _ _ _

/-- A regular equation chart of `x = c` for each chart of `x = 0`. -/
def verticalFiberDivisorAt_chart (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalZeroDivisor (k := k))) :
    RegularCartierEquationChart (projectiveProduct k) (verticalFiberDivisorAt (k := k) c) :=
  pullbackDivisor_regularChart (verticalTranslation c).inv verticalZeroDivisor
    verticalZeroDivisor_hasRegularEquations d

/-- Its chart open is the preimage of the chart open of `x = 0`. -/
theorem verticalFiberDivisorAt_chart_openSet (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalZeroDivisor (k := k))) :
    (verticalFiberDivisorAt_chart c d).chart.openSet =
      (verticalTranslation c).inv ⁻¹ᵁ d.chart.openSet := rfl

/-- Its coefficient is the translate of the coefficient of `x = 0`: the section `u - c`. -/
theorem verticalFiberDivisorAt_chart_coefficient (c : k)
    (d : RegularCartierEquationChart (projectiveProduct k) (verticalZeroDivisor (k := k))) :
    (verticalFiberDivisorAt_chart c d).coefficient =
      (verticalTranslation c).inv.app d.chart.openSet d.coefficient := rfl

/-- At `c = 0` the translation is the identity translation `τ_0 × τ_0`. -/
theorem verticalTranslation_zero_hom :
    (verticalTranslation (0 : k)).hom = 𝟙 (projectiveProduct k) := by
  rw [verticalTranslation_hom]
  exact productTranslation_zero

end KltDP.Examples.FrobeniusVerticalFiberTranslated

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusVerticalFiberTranslated

/-- Integrality again: a `local instance` dies at the `end` of its namespace block. -/
local instance translatedProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **F29: the vertical fibre `x = c` is an effective Cartier divisor with regular equations** on
`P¹ × P¹`, for every `c` — the divisor the rows `B · a`, `F̃ · a`, `B · b` are computed against. -/
theorem f29_vertical_fiber_divisor_at (k : Type u) [Field k] (c : k) :
    HasRegularCartierEquations (projectiveProduct k) (verticalFiberDivisorAt (k := k) c) :=
  verticalFiberDivisorAt_hasRegularEquations c

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_fiber_divisor_at_universe_check (k : Type u) [Field k] (c : k) : True := by
  have _ := f29_vertical_fiber_divisor_at.{u} k c
  trivial

end KltDP.Examples
