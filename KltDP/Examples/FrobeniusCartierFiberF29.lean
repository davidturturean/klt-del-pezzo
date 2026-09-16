import KltDP.Examples.FrobeniusFiberCartierCharts

/-!
# Bundle: effective Cartier structure of the fibre on the selected chart (F29 routes ii–iii, chart level)

`f29_cartier_fiber` collects, for a field `k` and every stage `n`, what is proved of BRIEF8 on the
selected polynomial chart `plane k` of the tower:

1. the total fibre divisor `stageFiberDivisor n` (equation `u^n·v`), the exceptional divisor
   (equation `u`) and the strict-fibre divisor (equation `v`) are effective Cartier divisors with
   regular equations (accepted `HasRegularCartierEquations`);
2. the identity of Cartier divisors `stageFiberDivisor n = n • exceptionalDivisor + strictFiberDivisor`;
3. their zero schemes (evaluation ideals of the canonical sections, accepted
   `effectiveCartierSection_evaluationIdeal`) have the ideals `(u^n·v) = pulled-back fibre ideal`,
   `(u)`, `(v)` on the chart;
4. the Picard relation on the chart, formally from (2) through the accepted `cartierPicardHom`.

Not included (see `F29_CARTIER_FIBER.md`): the gluing of these chart divisors over an atlas of the
whole tower, hence the whole-stage identity and the Picard relation on the tower.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusFiberCartierCharts

/-- The chart-level effective Cartier structure of the fibre: the clauses proved. -/
theorem f29_cartier_fiber (k : Type u) [Field k] :
    -- (1) effective Cartier divisors with regular equations
    (∀ n : ℕ, HasRegularCartierEquations (plane k) (stageFiberDivisor n)) ∧
    HasRegularCartierEquations (plane k) (exceptionalDivisor (k := k)) ∧
    HasRegularCartierEquations (plane k) (strictFiberDivisor (k := k)) ∧
    -- (2) the chart-level divisor identity
    (∀ n : ℕ, stageFiberDivisor (k := k) n = n • exceptionalDivisor + strictFiberDivisor) ∧
    -- (3) zero schemes
    (∀ n : ℕ, sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) (stageFiberDivisor n))
        (effectiveCartierSection (plane k) (stageFiberDivisor n)
          (stageFiberDivisor_hasRegularEquations n)) ⊤ =
      Ideal.map planeSectionHom (Ideal.map (stageSubstitution n) (Ideal.span {vCoord (k := k)}))) ∧
    (sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) exceptionalDivisor)
        (effectiveCartierSection (plane k) exceptionalDivisor
          exceptionalDivisor_hasRegularEquations) ⊤ =
      Ideal.span {planeSectionHom (uCoord (k := k))}) ∧
    (sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) strictFiberDivisor)
        (effectiveCartierSection (plane k) strictFiberDivisor
          strictFiberDivisor_hasRegularEquations) ⊤ =
      Ideal.span {planeSectionHom (vCoord (k := k))}) ∧
    -- (4) the chart-level Picard relation
    (∀ n : ℕ, cartierPicardHom (plane k) (stageFiberDivisor n) =
      n • cartierPicardHom (plane k) exceptionalDivisor +
        cartierPicardHom (plane k) strictFiberDivisor) :=
  ⟨fun n => stageFiberDivisor_hasRegularEquations n,
    exceptionalDivisor_hasRegularEquations,
    strictFiberDivisor_hasRegularEquations,
    fun n => stageFiberDivisor_eq n,
    fun n => stageFiberDivisor_zeroScheme_ideal n,
    exceptionalDivisor_zeroScheme_ideal,
    strictFiberDivisor_zeroScheme_ideal,
    fun n => stageFiberDivisor_picard n⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_cartier_fiber_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_cartier_fiber.{u} k
  trivial

end KltDP.Examples
