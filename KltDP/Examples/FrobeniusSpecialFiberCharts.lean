import KltDP.Examples.FrobeniusFiberClosure
import KltDP.Examples.FrobeniusExceptionalSuccessorChart

/-!
# The total transform of the tangent fibre in the accepted plane charts

Clause 5 of F29, route (i): in the selected polynomial chart of stage `n` the pullback of the fibre
equation `v = 0` through the accepted composite blowdown `stageProjection n` (coordinate formula
`stageSubstitution n : v ↦ u^n·v`) is the product of the `n`-th power of the exceptional coordinate
`u` and the strict-fibre coordinate `v`:

* `stageFiberEquation : stageSubstitution n v = u^n · v`;
* `stageFiberIdeal : (v)·stageSubstitution n = (u)^n · (v)` — the total fibre ideal of the chart is the
  `n`-th power of the exceptional ideal times the strict-fibre ideal;
* `stageFiberEquation_saturation` — saturating the total fibre equation by `u` recovers the strict
  fibre `v = 0`;
* on the second Rees chart of the following blowup (accepted coordinates `vEquation = v`,
  `oldRatio = u/v`), the pulled total fibre equation is `(u/v)^n · v^(n+1)`
  (`vChart_stageFiberEquation`): the older exceptional curve `u/v = 0` (the manuscript's `C_n`)
  appears with multiplicity `n` and the newest one `v = 0` with multiplicity `n + 1`.

These are the multiplicities `F + Σ_j j·C_j + p·P` of the complete scheme-theoretic fibre on the
charts; the whole-stage divisor identity and its Picard relation are recorded as open in
`F29_SPECIAL_FIBER.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusSpecialFiberCharts

open KltDP.Geometry KltDP.Geometry.AffineBlowup FrobeniusBlowupContact FrobeniusBlowupChartIteration
  FrobeniusBlowupSmooth FrobeniusExceptionalCharts FrobeniusExceptionalSuccessorChart
  FrobeniusFiberClosure

variable {k : Type u} [Field k]

/-- The pullback of the fibre equation to the selected chart of stage `n` is `u^n · v`. -/
theorem stageFiberEquation (n : ℕ) :
    stageSubstitution (k := k) n vCoord = uCoord ^ n * vCoord :=
  stageSubstitution_v n

/-- The total fibre ideal of the chart is the `n`-th power of the exceptional ideal times the
strict-fibre ideal. -/
theorem stageFiberIdeal (n : ℕ) :
    Ideal.map (stageSubstitution (k := k) n) (Ideal.span {vCoord}) =
      Ideal.span {uCoord (k := k)} ^ n * Ideal.span {vCoord} := by
  rw [Ideal.map_span, Set.image_singleton, stageSubstitution_v, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]

/-- The strict fibre is the exceptional saturation of the total fibre. -/
theorem stageFiberEquation_saturation (n : ℕ) (f : planeRing k) :
    (∃ j : ℕ, uCoord ^ j * f ∈ Ideal.span {stageSubstitution n vCoord}) ↔
      f ∈ Ideal.span {vCoord (k := k)} := by
  have hker : RingHom.ker (Polynomial.evalRingHom (0 : Polynomial k)) =
      Ideal.span {vCoord (k := k)} := by
    rw [Polynomial.ker_evalRingHom]
    simp only [vCoord, Polynomial.C_0, sub_zero]
  have heval : Polynomial.evalRingHom (0 : Polynomial k) (stageSubstitution n (vCoord (k := k))) = 0 := by
    rw [stageSubstitution_v]
    simp [uCoord, vCoord]
  have hu : Polynomial.evalRingHom (0 : Polynomial k) (uCoord (k := k)) = Polynomial.X := by
    simp [uCoord]
  constructor
  · rintro ⟨j, hj⟩
    rw [← hker, RingHom.mem_ker]
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hj
    have h : Polynomial.X ^ j * Polynomial.evalRingHom (0 : Polynomial k) f = 0 := by
      simpa only [map_mul, map_pow, hu, heval, zero_mul] using
        congrArg (Polynomial.evalRingHom (0 : Polynomial k)) hg
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero j Polynomial.X_ne_zero)
  · intro hf
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
    refine ⟨n, Ideal.mem_span_singleton.mpr ⟨g, ?_⟩⟩
    rw [hg, stageSubstitution_v, mul_assoc]

/-- The strict fibre coordinate is invariant under every stage substitution (the strict fibre is
its own transform in the selected chart). -/
theorem stageSubstitution_fiber_strict (n : ℕ) :
    fiberCurve (k := k) ≫ stageProjection n = fiberCurve :=
  fiberCurve_stageProjection n

/-- On the second Rees chart of the next blowup the total fibre equation of stage `n` becomes
`(u/v)^n · v^(n+1)`: the older exceptional curve `u/v = 0` has multiplicity `n`, the newest `v = 0`
has multiplicity `n + 1`. -/
theorem vChart_stageFiberEquation (n : ℕ) :
    chartBaseMap centerIdeal centerV (stageSubstitution (k := k) n vCoord) =
      oldRatio (k := k) ^ n * vEquation (k := k) ^ (n + 1) := by
  rw [stageSubstitution_v, map_mul, map_pow, ← vEquation_mul_oldRatio]
  change (vEquation (k := k) * oldRatio (k := k)) ^ n * vEquation (k := k) = _
  ring

/-- The same statement for the ideals of the second Rees chart. -/
theorem vChart_stageFiberIdeal (n : ℕ) :
    Ideal.span {chartBaseMap centerIdeal centerV (stageSubstitution (k := k) n vCoord)} =
      Ideal.span {oldRatio (k := k)} ^ n * Ideal.span {vEquation (k := k)} ^ (n + 1) := by
  rw [vChart_stageFiberEquation, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]

end KltDP.Examples.FrobeniusSpecialFiberCharts
