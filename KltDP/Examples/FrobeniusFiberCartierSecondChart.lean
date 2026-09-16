import KltDP.Examples.FrobeniusFiberCartierCharts

/-!
# The fibre on the second Rees chart, as Cartier divisors of its polynomial model

The accepted `vChartPolynomialEquiv : reesVChartRing k ≃+* planeRing k` identifies the second Rees
chart ring with the polynomial plane, sending the older exceptional coordinate `u/v` to `v` and the
newest exceptional coordinate `v` to `u` (`vChartPolynomialEquiv_coordinate`,
`vChart_selected_equation`). Through this identification the pulled total fibre equation of stage `n`,
`(u/v)^n · v^{n+1}` on the second chart (task 7, `vChart_stageFiberEquation`), becomes
`v^n · u^{n+1}` (`secondChartFiber_image`), and BRIEF8 step 2 on the second chart is the identity of
Cartier divisors of the polynomial model

`secondChartFiberDivisor n = n • (older exceptional curve) + (n + 1) • (newest exceptional curve)`

(`secondChartFiberDivisor_eq`), the two curves being the principal divisors of `v` and `u` of
`FrobeniusFiberCartierCharts` (there named for the first chart's roles: `strictFiberDivisor` is the
divisor of `v`, `exceptionalDivisor` the divisor of `u`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusFiberCartierSecondChart

open KltDP.Geometry KltDP.Geometry.AffineBlowup FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusBlowupSmooth FrobeniusExceptionalCharts FrobeniusExceptionalSuccessorChart
  FrobeniusSpecialFiberCharts FrobeniusFiberCartierCharts

variable {k : Type u} [Field k]

/-- The older exceptional coordinate `u/v` of the second chart is `v` in the polynomial model. -/
theorem oldRatio_image : vChartPolynomialEquiv (k := k) oldRatio = vCoord :=
  vChartPolynomialEquiv_coordinate

/-- The newest exceptional coordinate `v` of the second chart is `u` in the polynomial model. -/
theorem vEquation_image : vChartPolynomialEquiv (k := k) vEquation = uCoord :=
  vChart_selected_equation

/-- The pulled total fibre equation of stage `n` on the second chart is `v^n · u^(n+1)` in the
polynomial model. -/
theorem secondChartFiber_image (n : ℕ) :
    vChartPolynomialEquiv (k := k) (chartBaseMap centerIdeal centerV (stageSubstitution n vCoord)) =
      vCoord ^ n * uCoord ^ (n + 1) := by
  rw [vChart_stageFiberEquation, map_mul, map_pow, map_pow, oldRatio_image, vEquation_image]

theorem secondChartFiber_ne_zero (n : ℕ) :
    vChartPolynomialEquiv (k := k) (chartBaseMap centerIdeal centerV (stageSubstitution n vCoord)) ≠
      0 := by
  rw [secondChartFiber_image]
  exact mul_ne_zero (pow_ne_zero n FrobeniusFiberCartierCharts.vCoord_ne_zero)
      (pow_ne_zero (n + 1) FrobeniusFiberCartierCharts.uCoord_ne_zero)

/-- The total fibre divisor of stage `n` on the polynomial model of the second Rees chart. -/
def secondChartFiberDivisor (n : ℕ) : CartierDivisor (plane k) :=
  chartDivisor (vChartPolynomialEquiv (chartBaseMap centerIdeal centerV (stageSubstitution n vCoord)))
    (secondChartFiber_ne_zero n)

/-- Chart-level step 2 on the second Rees chart: `n` times the older exceptional curve (`v` in the
model) plus `n + 1` times the newest one (`u` in the model). -/
theorem secondChartFiberDivisor_eq (n : ℕ) :
    secondChartFiberDivisor (k := k) n = n • strictFiberDivisor + (n + 1) • exceptionalDivisor := by
  rw [secondChartFiberDivisor, chartDivisor_congr (secondChartFiber_ne_zero n)
    (mul_ne_zero (pow_ne_zero n FrobeniusFiberCartierCharts.vCoord_ne_zero)
      (pow_ne_zero (n + 1) FrobeniusFiberCartierCharts.uCoord_ne_zero))
    (secondChartFiber_image n), chartDivisor_mul, chartDivisor_pow, chartDivisor_pow]
  rfl

theorem secondChartFiberDivisor_hasRegularEquations (n : ℕ) :
    HasRegularCartierEquations (plane k) (secondChartFiberDivisor n) :=
  chartDivisor_hasRegularEquations _ _

/-- The zero scheme of the second-chart total fibre divisor has ideal `(v^n · u^(n+1))` in the model. -/
theorem secondChartFiberDivisor_zeroScheme_ideal (n : ℕ) :
    sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) (secondChartFiberDivisor n))
        (effectiveCartierSection (plane k) (secondChartFiberDivisor n)
          (secondChartFiberDivisor_hasRegularEquations n)) ⊤ =
      Ideal.span {planeSectionHom (vCoord (k := k) ^ n * uCoord ^ (n + 1))} := by
  rw [← secondChartFiber_image]
  exact chartDivisor_zeroScheme_ideal _ _

/-- The chart-level Picard relation on the second chart (formal). -/
theorem secondChartFiberDivisor_picard (n : ℕ) :
    cartierPicardHom (plane k) (secondChartFiberDivisor n) =
      n • cartierPicardHom (plane k) strictFiberDivisor +
        (n + 1) • cartierPicardHom (plane k) exceptionalDivisor := by
  rw [secondChartFiberDivisor_eq, map_add, map_nsmul, map_nsmul]

end KltDP.Examples.FrobeniusFiberCartierSecondChart

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.AffineBlowup FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusBlowupSmooth FrobeniusExceptionalSuccessorChart FrobeniusFiberCartierCharts
  FrobeniusFiberCartierSecondChart

/-- Bundle: the fibre on the second Rees chart as Cartier divisors of its polynomial model. -/
theorem f29_cartier_fiber_secondChart (k : Type u) [Field k] :
    (∀ n : ℕ, vChartPolynomialEquiv (k := k)
        (chartBaseMap centerIdeal centerV (stageSubstitution n vCoord)) =
      vCoord ^ n * uCoord ^ (n + 1)) ∧
    (∀ n : ℕ, HasRegularCartierEquations (plane k) (secondChartFiberDivisor n)) ∧
    (∀ n : ℕ, secondChartFiberDivisor (k := k) n =
      n • strictFiberDivisor + (n + 1) • exceptionalDivisor) ∧
    (∀ n : ℕ, cartierPicardHom (plane k) (secondChartFiberDivisor n) =
      n • cartierPicardHom (plane k) strictFiberDivisor +
        (n + 1) • cartierPicardHom (plane k) exceptionalDivisor) :=
  ⟨fun n => secondChartFiber_image n, fun n => secondChartFiberDivisor_hasRegularEquations n,
    fun n => secondChartFiberDivisor_eq n, fun n => secondChartFiberDivisor_picard n⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_cartier_fiber_secondChart_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_cartier_fiber_secondChart.{u} k
  trivial

end KltDP.Examples
