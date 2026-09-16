import KltDP.Examples.FrobeniusFiberZeroClass
import KltDP.Geometry.CartierDivisorOfEquations

/-!
# The effective Cartier divisor of the vertical fibre `x = 0` (BRIEF28, step 2)

The accepted `FrobeniusFiberZeroClass` builds the Cartier divisor of the horizontal fibre `y = 0` on
`P¹ × P¹`. Its construction is the `d = 1` instance of a **factor-indexed** pattern: `rulingOpen d i`,
`rulingOpen_cover d`, `rulingCoordinateUnit d` and `reciprocal_cartier_class_zero d` are all general in
`d`, and `productOpen_le_rulingChart d i j` lands in `rulingOpen d (productIndex d i j)` with
`productIndex d i j = if d = 0 then i else j`. This module instantiates the same pattern at `d = 0`,
giving the vertical fibre `x = 0`, with the coordinate `uCoord` in place of `vCoord` and the charts
indexed by the **first** coordinate.

* `verticalZeroEquation` — the local equations: the coordinate `x` where `x` is finite, `1` elsewhere;
* `verticalZeroDivisor` — the glued effective Cartier divisor, with `verticalZeroDivisor_restrict_ruling`;
* `verticalZeroChartZero`, `verticalZeroChartOne` — regular equation charts on `productOpen 0 j` and
  `productOpen 1 j`, the first with coefficient the chart coordinate `u`, its `germ_eq` discharged by the
  accepted `productFunctionFieldMap_u` and `rulingCoordinate_zero` exactly as the accepted `y = 0` charts
  use `productFunctionFieldMap_v`;
* **`verticalZeroDivisor_hasRegularEquations`** — so the divisor may be pulled back along the blowdowns
  by the accepted `pullbackDivisor`, which is what the fibre rows need.

Nothing here is Frobenius-specific and nothing is assumed; it is the missing first-coordinate counterpart
of an accepted second-coordinate development. The fibre `x = c` for `c ≠ 0` is obtained from this one by
the accepted translation-pullback idiom (`translatedFiberZeroDivisor`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusVerticalFiberClass

open KltDP.Geometry ProjectiveLineComparison
open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusGraphPicardClassCharts FrobeniusGraphPicardClassMixedCoordinates
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassRulingDivisors
open FrobeniusGraphPicardClassCoordinateComparison
open FrobeniusFiberZeroInvertible FrobeniusFiberZeroClass

variable {k : Type u} [Field k]

/-- The product is integral (accepted `projectiveProduct_isIntegral`). The accepted modules supply
this as a `local instance`, which does not reach importing modules, so it is re-declared here. -/
local instance verticalProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- Local equations of the fibre `x = 0` on the two ruling opens of the **first** projection: the
coordinate `x` where `x` is finite, and `1` where `x ≠ 0`. -/
def verticalZeroEquation (i : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  if i = 0 then rulingCoordinateUnit 0 else 1

/-- The coordinate `x` is a regular unit on every common subopen of the two ruling opens. -/
theorem verticalCoordinate_cartier_class_zero (V : (projectiveProduct k).Opens) [Nonempty V]
    (h₀ : V ≤ rulingOpen 0 0) (h₁ : V ≤ rulingOpen 0 1) :
    cartierEquationClassHom (projectiveProduct k) V
      (Additive.ofMul (rulingCoordinateUnit (k := k) 0)) = 0 := by
  have h := reciprocal_cartier_class_zero (k := k) 0 V h₀ h₁
  rw [ofMul_inv, map_neg, neg_eq_zero] at h
  exact h

theorem verticalZeroEquation_compatible (i j : Fin 2) :
    cartierEquationClassHom (projectiveProduct k) (rulingOpen 0 i ⊓ rulingOpen 0 j)
        (Additive.ofMul (verticalZeroEquation i)) =
      cartierEquationClassHom (projectiveProduct k) (rulingOpen 0 i ⊓ rulingOpen 0 j)
        (Additive.ofMul (verticalZeroEquation j)) := by
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [verticalZeroEquation] using
      verticalCoordinate_cartier_class_zero (k := k) (rulingOpen 0 0 ⊓ rulingOpen 0 1)
        inf_le_left inf_le_right
  · simpa [verticalZeroEquation] using
      (verticalCoordinate_cartier_class_zero (k := k) (rulingOpen 0 1 ⊓ rulingOpen 0 0)
        inf_le_right inf_le_left).symm
  · rfl

/-- The two ruling opens of the first projection cover the product. -/
theorem verticalZero_cover :
    (⊤ : (projectiveProduct k).Opens) ≤ ⨆ i : ULift.{u} (Fin 2), rulingOpen 0 i.down := by
  intro x _
  have hx : x ∈ ⨆ i : Fin 2, rulingOpen (k := k) 0 i := by
    rw [rulingOpen_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

/-- **The effective Cartier divisor of the fibre `x = 0`.** -/
def verticalZeroDivisor : CartierDivisor (projectiveProduct k) :=
  cartierDivisorOfEquations (projectiveProduct k)
    (fun i : ULift.{u} (Fin 2) => rulingOpen 0 i.down) verticalZero_cover
    (fun i => verticalZeroEquation i.down)
    (fun i j => verticalZeroEquation_compatible i.down j.down)

theorem verticalZeroDivisor_restrict_ruling (i : Fin 2) :
    cartierEquationClassHom (projectiveProduct k) (rulingOpen 0 i)
        (Additive.ofMul (verticalZeroEquation i)) =
      (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show rulingOpen (k := k) 0 i ≤ ⊤ from le_top)).op verticalZeroDivisor :=
  (cartierDivisorOfEquations_restrict (projectiveProduct k)
    (fun i : ULift.{u} (Fin 2) => rulingOpen 0 i.down) verticalZero_cover
    (fun i => verticalZeroEquation i.down)
    (fun i j => verticalZeroEquation_compatible i.down j.down) ⟨i⟩).symm

/-- For the first projection the product chart `(i, j)` lies over the ruling open `i`. -/
theorem productOpen_le_rulingOpen_first (i j : Fin 2) :
    productOpen (k := k) i j ≤ rulingOpen 0 i :=
  productOpen_le_rulingChart 0 i j

/-- The local equation `u` of the fibre `x = 0` on the chart `(0, j)`, as a section of the product. -/
def verticalZeroChartEquation (j : Fin 2) :
    Γ(projectiveProduct k, (fiberChartAffineOpen (k := k) 0 j).1) :=
  ((productChart (k := k) 0 j).appIso ⊤).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom uCoord)

/-- On the chart `(0, j)` the divisor has equation `x` with regular coefficient the coordinate `u`. -/
def verticalZeroChartZero (j : Fin 2) :
    RegularCartierEquationChart (projectiveProduct k) (verticalZeroDivisor (k := k)) where
  chart :=
    { openSet := productOpen 0 j
      nonempty := productOpen_nonempty 0 j
      equation := rulingCoordinateUnit 0
      represents := cartierGlobalEquation_restrict (projectiveProduct k) verticalZeroDivisor
        (homOfLE (productOpen_le_rulingOpen_first 0 j)) (rulingCoordinateUnit 0)
        (verticalZeroDivisor_restrict_ruling 0) }
  coefficient := verticalZeroChartEquation j
  germ_eq := by
    change productFunctionFieldMap (k := k) 0 j uCoord = rulingLeft 0
    rw [productFunctionFieldMap_u, rulingCoordinate_zero]

/-- On the chart `(1, j)` the divisor has equation and coefficient `1`. -/
def verticalZeroChartOne (j : Fin 2) :
    RegularCartierEquationChart (projectiveProduct k) (verticalZeroDivisor (k := k)) where
  chart :=
    { openSet := productOpen 1 j
      nonempty := productOpen_nonempty 1 j
      equation := 1
      represents := cartierGlobalEquation_restrict (projectiveProduct k) verticalZeroDivisor
        (homOfLE (productOpen_le_rulingOpen_first 1 j)) 1
        (verticalZeroDivisor_restrict_ruling 1) }
  coefficient := 1
  germ_eq := by simp

/-- **The vertical fibre divisor has regular equations**, so it can be pulled back along the
blowdowns by the accepted `pullbackDivisor`. -/
theorem verticalZeroDivisor_hasRegularEquations :
    HasRegularCartierEquations (projectiveProduct k) (verticalZeroDivisor (k := k)) := by
  intro x
  obtain ⟨i, j, hx⟩ := productCharts_cover x
  have hx' := mem_productOpen_of_mem_range i j x hx
  fin_cases i
  · exact ⟨verticalZeroChartZero j, hx'⟩
  · exact ⟨verticalZeroChartOne j, hx'⟩

end KltDP.Examples.FrobeniusVerticalFiberClass

namespace KltDP.Examples

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusVerticalFiberClass

/-- Integrality again: a `local instance` is scoped to its enclosing namespace block, so the one
declared above ended at `end KltDP.Examples.FrobeniusVerticalFiberClass` and must be repeated here. -/
local instance verticalProductIntegralTop {k : Type u} [Field k] :
    IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- **F29: the vertical ruling fibre `x = 0` is an effective Cartier divisor with regular
equations** on `P¹ × P¹` — the first-coordinate counterpart of the accepted `fiberZeroDivisor`. -/
theorem f29_vertical_fiber_divisor (k : Type u) [Field k] :
    HasRegularCartierEquations (projectiveProduct k) (verticalZeroDivisor (k := k)) :=
  verticalZeroDivisor_hasRegularEquations

/-- The statement has exactly one universe parameter. -/
theorem f29_vertical_fiber_divisor_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_vertical_fiber_divisor.{u} k
  trivial

end KltDP.Examples
