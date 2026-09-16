import KltDP.Geometry.CartierDivisorOfEquations
import KltDP.Examples.FrobeniusSpecialFiberCharts

/-!
# Effective Cartier divisors of the fibre, the exceptional curve and the strict fibre on the chart

On the selected polynomial chart `plane k` (an integral affine scheme) every nonzero polynomial `f`
gives the principal effective Cartier divisor `chartDivisor f` (accepted `principalCartierDivisorHom`),
with the single regular equation chart `⊤` and coefficient `f` (`chartDivisor_regularChart`,
`chartDivisor_hasRegularEquations`); by the accepted `effectiveCartierSection_evaluationIdeal` the
evaluation ideal of its canonical section — the ideal of its zero scheme — is `(f)` on the chart
(`chartDivisor_zeroScheme_ideal`).

For the fibre: the total fibre divisor of stage `n` (equation `stageSubstitution n v = u^n·v`), the
exceptional divisor (equation `u`) and the strict-fibre divisor (equation `v`) are effective Cartier
divisors on the chart, and the chart-level identity of BRIEF8 step 2 holds as an identity of Cartier
divisors: `stageFiberDivisor n = n • exceptionalDivisor + strictFiberDivisor`
(`stageFiberDivisor_eq`). The zero scheme of the total fibre divisor is the pulled-back fibre ideal
(`stageFiberDivisor_zeroScheme_ideal`, via task 7's `stageFiberIdeal`). The chart-level Picard relation
holds formally (`stageFiberDivisor_picard`; all classes vanish on the affine chart).

The gluing of these chart divisors to the whole tower needs equations on an atlas of the tower; see
`F29_CARTIER_FIBER.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusFiberCartierCharts

open KltDP.Geometry FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusSpecialFiberCharts

variable {k : Type u} [Field k]

/-! ## Polynomials as sections and rational functions of the chart -/

/-- Global sections of the plane chart from polynomials. -/
def planeSectionHom : planeRing k →+* Γ(plane k, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv.hom

theorem planeSectionHom_injective : Function.Injective (planeSectionHom (k := k)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).symm.commRingCatIsoToRingEquiv.injective

/-- The rational function of a nonzero polynomial. -/
def planeRational (f : planeRing k) (hf : f ≠ 0) : (plane k).functionFieldˣ :=
  Units.mk0 ((plane k).germToFunctionField ⊤ (planeSectionHom f)) (by
    intro h
    apply hf
    apply planeSectionHom_injective
    rw [map_zero]
    apply (plane k).germToFunctionField_injective ⊤
    rw [map_zero]
    exact h)

theorem planeRational_val (f : planeRing k) (hf : f ≠ 0) :
    (planeRational f hf : (plane k).functionField) =
      (plane k).germToFunctionField ⊤ (planeSectionHom f) := rfl

theorem planeRational_mul (f g : planeRing k) (hf : f ≠ 0) (hg : g ≠ 0) :
    planeRational (f * g) (mul_ne_zero hf hg) = planeRational f hf * planeRational g hg := by
  apply Units.ext
  rw [Units.val_mul, planeRational_val, planeRational_val, planeRational_val, map_mul, map_mul]

theorem planeRational_pow (f : planeRing k) (hf : f ≠ 0) (n : ℕ) :
    planeRational (f ^ n) (pow_ne_zero n hf) = planeRational f hf ^ n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, planeRational_val, planeRational_val, map_pow, map_pow]

/-! ## Principal effective Cartier divisors of the chart -/

/-- The principal Cartier divisor of a nonzero polynomial on the chart. -/
def chartDivisor (f : planeRing k) (hf : f ≠ 0) : CartierDivisor (plane k) :=
  principalCartierDivisorHom (plane k) (Additive.ofMul (planeRational f hf))

theorem chartDivisor_congr {f g : planeRing k} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f = g) :
    chartDivisor f hf = chartDivisor g hg := by
  subst hfg
  rfl

theorem chartDivisor_mul (f g : planeRing k) (hf : f ≠ 0) (hg : g ≠ 0) :
    chartDivisor (f * g) (mul_ne_zero hf hg) = chartDivisor f hf + chartDivisor g hg := by
  rw [chartDivisor, chartDivisor, chartDivisor, planeRational_mul f g hf hg, ofMul_mul, map_add]

theorem chartDivisor_pow (f : planeRing k) (hf : f ≠ 0) (n : ℕ) :
    chartDivisor (f ^ n) (pow_ne_zero n hf) = n • chartDivisor f hf := by
  rw [chartDivisor, chartDivisor, planeRational_pow f hf n, ofMul_pow, map_nsmul]

/-- The whole chart is an equation chart of the principal divisor. -/
def chartDivisor_chart (f : planeRing k) (hf : f ≠ 0) :
    CartierEquationChart (plane k) (chartDivisor f hf) where
  openSet := ⊤
  nonempty := inferInstance
  equation := planeRational f hf
  represents := by
    simpa only [chartDivisor, principalCartierDivisorHom] using
      (cartierEquationClassHom_restrict (plane k) (show (⊤ : (plane k).Opens) ≤ ⊤ from le_rfl)
        (planeRational f hf)).symm

/-- The polynomial itself is a regular coefficient on the whole chart. -/
def chartDivisor_regularChart (f : planeRing k) (hf : f ≠ 0) :
    RegularCartierEquationChart (plane k) (chartDivisor f hf) where
  chart := chartDivisor_chart f hf
  coefficient := planeSectionHom f
  germ_eq := rfl

/-- The principal divisor of a nonzero polynomial is effective with regular equations. -/
theorem chartDivisor_hasRegularEquations (f : planeRing k) (hf : f ≠ 0) :
    HasRegularCartierEquations (plane k) (chartDivisor f hf) :=
  fun _ => ⟨chartDivisor_regularChart f hf, trivial⟩

/-- The zero scheme of the principal divisor (the evaluation ideal of its canonical section) has
ideal `(f)` on the chart. -/
theorem chartDivisor_zeroScheme_ideal (f : planeRing k) (hf : f ≠ 0) :
    sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) (chartDivisor f hf))
        (effectiveCartierSection (plane k) (chartDivisor f hf)
          (chartDivisor_hasRegularEquations f hf)) ⊤ =
      Ideal.span {planeSectionHom f} :=
  effectiveCartierSection_evaluationIdeal (plane k) (chartDivisor f hf)
    (chartDivisor_hasRegularEquations f hf) (chartDivisor_regularChart f hf)

/-- Principal divisors have trivial Picard class. -/
theorem chartDivisor_picard (f : planeRing k) (hf : f ≠ 0) :
    cartierPicardHom (plane k) (chartDivisor f hf) = 0 :=
  cartierPicardHom_principal (plane k) _

/-! ## The fibre, the exceptional curve and the strict fibre -/

theorem uCoord_ne_zero : (uCoord (k := k)) ≠ 0 := Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero

theorem vCoord_ne_zero : (vCoord (k := k)) ≠ 0 := Polynomial.X_ne_zero

theorem stageFiber_ne_zero (n : ℕ) : stageSubstitution (k := k) n vCoord ≠ 0 := by
  rw [stageSubstitution_v]
  exact mul_ne_zero (pow_ne_zero n uCoord_ne_zero) vCoord_ne_zero

/-- The exceptional divisor `u = 0` of the selected chart. -/
def exceptionalDivisor : CartierDivisor (plane k) := chartDivisor uCoord uCoord_ne_zero

/-- The strict-fibre divisor `v = 0` of the selected chart. -/
def strictFiberDivisor : CartierDivisor (plane k) := chartDivisor vCoord vCoord_ne_zero

/-- The total fibre divisor of stage `n`: the pullback of `v = 0` through the `n`-step blowdown. -/
def stageFiberDivisor (n : ℕ) : CartierDivisor (plane k) :=
  chartDivisor (stageSubstitution n vCoord) (stageFiber_ne_zero n)

/-- Chart-level step 2: the total fibre divisor is `n` times the exceptional divisor plus the strict
fibre, as Cartier divisors of the chart. -/
theorem stageFiberDivisor_eq (n : ℕ) :
    stageFiberDivisor (k := k) n = n • exceptionalDivisor + strictFiberDivisor := by
  rw [stageFiberDivisor, chartDivisor_congr (stageFiber_ne_zero n)
    (mul_ne_zero (pow_ne_zero n uCoord_ne_zero) vCoord_ne_zero) (stageSubstitution_v n),
    chartDivisor_mul, chartDivisor_pow]
  rfl

theorem stageFiberDivisor_hasRegularEquations (n : ℕ) :
    HasRegularCartierEquations (plane k) (stageFiberDivisor n) :=
  chartDivisor_hasRegularEquations _ _

theorem exceptionalDivisor_hasRegularEquations :
    HasRegularCartierEquations (plane k) (exceptionalDivisor (k := k)) :=
  chartDivisor_hasRegularEquations _ _

theorem strictFiberDivisor_hasRegularEquations :
    HasRegularCartierEquations (plane k) (strictFiberDivisor (k := k)) :=
  chartDivisor_hasRegularEquations _ _

/-- The zero scheme of the total fibre divisor is the pulled-back fibre ideal of the chart. -/
theorem stageFiberDivisor_zeroScheme_ideal (n : ℕ) :
    sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) (stageFiberDivisor n))
        (effectiveCartierSection (plane k) (stageFiberDivisor n)
          (stageFiberDivisor_hasRegularEquations n)) ⊤ =
      Ideal.map planeSectionHom (Ideal.map (stageSubstitution n) (Ideal.span {vCoord (k := k)})) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  exact chartDivisor_zeroScheme_ideal _ _

theorem exceptionalDivisor_zeroScheme_ideal :
    sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) exceptionalDivisor)
        (effectiveCartierSection (plane k) exceptionalDivisor
          exceptionalDivisor_hasRegularEquations) ⊤ =
      Ideal.span {planeSectionHom (uCoord (k := k))} :=
  chartDivisor_zeroScheme_ideal _ _

theorem strictFiberDivisor_zeroScheme_ideal :
    sectionEvaluationIdeal (plane k) (cartierDivisorModule (plane k) strictFiberDivisor)
        (effectiveCartierSection (plane k) strictFiberDivisor
          strictFiberDivisor_hasRegularEquations) ⊤ =
      Ideal.span {planeSectionHom (vCoord (k := k))} :=
  chartDivisor_zeroScheme_ideal _ _

/-- The chart-level Picard relation (formal consequence of `stageFiberDivisor_eq`). -/
theorem stageFiberDivisor_picard (n : ℕ) :
    cartierPicardHom (plane k) (stageFiberDivisor n) =
      n • cartierPicardHom (plane k) exceptionalDivisor +
        cartierPicardHom (plane k) strictFiberDivisor := by
  rw [stageFiberDivisor_eq, map_add, map_nsmul]

end KltDP.Examples.FrobeniusFiberCartierCharts
