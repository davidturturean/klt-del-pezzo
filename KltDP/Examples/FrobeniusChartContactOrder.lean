import KltDP.Examples.FrobeniusChartOrderExact
import KltDP.Examples.FrobeniusGraphPicardClassAffine
import KltDP.Examples.FrobeniusStrictTransformFirstChartTensorFrame
import Mathlib.Algebra.Polynomial.Div

/-!
# The contact equation has contact order exactly one at the blowup centre

The general order formula `σ^*f = u^(ord f) · g` with `u ∤ g` (`FrobeniusChartOrderExact`) carries an
exponent that nothing so far evaluated on any actual curve: only `1 ≤ centerOrder` was available for the
Frobenius contact family (`FrobeniusChartPullbackOrder.one_le_centerOrder_firstEquationPoly`). This
module computes that exponent exactly,

`centerOrder (vCoord - uCoord ^ (m + 1)) = 1`,

for every `m`, and identifies the cofactor of the general factorisation with the accepted residual
equation `vCoord - uCoord ^ m`.

## The route, and why the planned one is not needed

The exact value needs a **non**-membership, `vCoord - uCoord ^ (m+1) ∉ centerIdeal ^ 2`, and the plan of
record was to witness it by the `k`-algebra map to `k[s]/(s²)` sending `u ↦ 0`, `v ↦ s`. That dual-number
witness is unnecessary. The queued equivalence

`f ∈ centerIdeal ^ n ↔ uCoord ^ n ∣ chartSubstitution f`  (`mem_centerIdeal_pow_iff_uCoord_pow_dvd`)

turns the non-membership into a divisibility statement, and `coeff_chartSubstitution` evaluates it on the
first `v`-coefficient: `(σ^*f).coeff 1 = X · f.coeff 1 = X`, so membership in `centerIdeal ^ 2` would force
`X² ∣ X` in `k[u]`, which `Polynomial.X_pow_dvd_iff` refutes at `d = 1`. No quotient ring is constructed
and no new algebra map is defined.

The same coefficient computation, at the **outer** level via `uCoord_pow_dvd_iff`, gives
`¬ uCoord ∣ (vCoord - uCoord ^ p)` for every `p` — stated for an arbitrary exponent because it is used
twice, once for the equation and once for its cofactor.

## What this closes

`FrobeniusChartSectionFactorization` recorded that no corollary specialising the general factorisation
back to the accepted order-one line could be given, for want of exactly this value. With the order in
hand:

* `chartOrderExact_firstEquationPoly` exhibits the general `ChartOrderExact` data at this family: the
  exponent is `1` and the cofactor is the accepted `vCoord - uCoord ^ m`, which is **prime to** `uCoord`.
  The non-divisibility is new: the accepted `firstStepEquation_factorization` gives the factorisation but
  not that it removes *all* exceptional factors.
* `cofactor_eq_residual` shows the cofactor is forced — any `g` witnessing the general factorisation at
  this family equals the accepted residual equation.
* `firstEquation_section_factorization_order` is the section-level restatement with the order displayed.
  Its content beyond the accepted `firstStepEquation_section_factorization` is the exponent alone; it is
  recorded because the order-indexed shape is what the general theorem produces, and the two now visibly
  agree.

## What remains open

The globalisation is untouched: passing from this chart identity to a divisor identity still needs the
second chart, the agreement of the two chart orders on the overlap, and the comparison of the local
factorisation with the Weil coefficient at the exceptional curve. No Weil-side pullback exists in the
tree, and carrying `σ^*C` across `cartierWeilEquiv` would need the point blowup presented as a
`NormalProjectiveSurface` with factorial stalks, whose `normal` and `dimension_two` fields are unbuilt.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusChartContactOrder

open KltDP.RingTheory.LocalAdicOrder
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupChartIteration
open KltDP.Examples.FrobeniusChartPullbackOrder
open KltDP.Examples.FrobeniusChartOrderExact

variable {k : Type u} [Field k]

/-! ## The first `v`-coefficient of the contact family -/

/-- The linear term of `v - u ^ p` is `1`, for **every** exponent including `p = 0`: `uCoord ^ p` is a
constant of the outer ring, so it contributes nothing to the first `v`-coefficient. -/
theorem coeff_one_vCoord_sub_uCoord_pow (p : ℕ) :
    (vCoord - uCoord ^ p : planeRing k).coeff 1 = 1 := by
  have hue : (uCoord (k := k)) ^ p = Polynomial.C (Polynomial.X ^ p) := by
    show (Polynomial.C Polynomial.X : planeRing k) ^ p = _
    rw [← Polynomial.C_pow]
  have hv : (vCoord (k := k)).coeff 1 = 1 := by
    show (Polynomial.X : planeRing k).coeff 1 = 1
    exact Polynomial.coeff_X_one
  rw [Polynomial.coeff_sub, hv, hue, Polynomial.coeff_C]
  simp

/-- **The contact equation and its cofactor are prime to the exceptional coordinate.** Stated for an
arbitrary exponent: it is applied both to `v - u ^ (m+1)` and to the residual `v - u ^ m`. -/
theorem not_uCoord_dvd_vCoord_sub_uCoord_pow (p : ℕ) :
    ¬ (uCoord ∣ (vCoord - uCoord ^ p : planeRing k)) := by
  intro hdvd
  have hpow : (uCoord (k := k)) ^ 1 ∣ (vCoord - uCoord ^ p : planeRing k) := by
    rwa [pow_one]
  have hcoeff := (uCoord_pow_dvd_iff 1 _).mp hpow 1
  rw [coeff_one_vCoord_sub_uCoord_pow, pow_one] at hcoeff
  exact Polynomial.not_isUnit_X (isUnit_of_dvd_one hcoeff)

/-! ## The non-membership, without a dual-number witness -/

/-- **The contact equation is not in the square of the centre.** -/
theorem not_mem_centerIdeal_sq_firstEquationPoly (m : ℕ) :
    (vCoord - uCoord ^ (m + 1) : planeRing k) ∉ centerIdeal ^ 2 := by
  intro hmem
  have hdvd : (uCoord (k := k)) ^ 2 ∣ chartSubstitution (vCoord - uCoord ^ (m + 1)) :=
    (mem_centerIdeal_pow_iff_uCoord_pow_dvd 2 _).mp hmem
  have hcoeff := (uCoord_pow_dvd_iff 2 _).mp hdvd 1
  rw [coeff_chartSubstitution, coeff_one_vCoord_sub_uCoord_pow, mul_one, pow_one] at hcoeff
  have h1 := Polynomial.X_pow_dvd_iff.mp hcoeff 1 (by norm_num)
  rw [Polynomial.coeff_X_one] at h1
  exact one_ne_zero h1

/-! ## The order -/

/-- **The contact order of the Frobenius contact equation at the centre is exactly one.** -/
theorem centerOrder_firstEquationPoly (m : ℕ) :
    centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k) = 1 := by
  have hbdd := bddAbove_center (vCoord - uCoord ^ (m + 1) : planeRing k)
    (firstEquationPoly_ne_zero m)
  refine le_antisymm ?_ (one_le_centerOrder_firstEquationPoly m)
  by_contra hlt
  push_neg at hlt
  have h2 : (2 : ℕ) ≤ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k) := by omega
  exact not_mem_centerIdeal_sq_firstEquationPoly m ((le_adicOrder_iff_mem hbdd 2).mp h2)

/-! ## The cofactor is the accepted residual equation -/

/-- The chart substitution of the contact equation, computed directly from the substitution rules. -/
theorem chartSubstitution_firstEquationPoly (m : ℕ) :
    chartSubstitution (vCoord - uCoord ^ (m + 1) : planeRing k)
      = uCoord * (vCoord - uCoord ^ m) := by
  rw [map_sub, map_pow, chartSubstitution_u, chartSubstitution_v, pow_succ']
  ring

/-- **The cofactor is forced**: any witness of the general factorisation at this family is the accepted
residual equation. -/
theorem cofactor_eq_residual (m : ℕ) {g : planeRing k}
    (hg : chartSubstitution (vCoord - uCoord ^ (m + 1) : planeRing k)
        = uCoord ^ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k) * g) :
    g = vCoord - uCoord ^ m := by
  rw [centerOrder_firstEquationPoly] at hg
  rw [pow_one] at hg
  rw [chartSubstitution_firstEquationPoly] at hg
  exact (mul_left_cancel₀ uCoord_ne_zero hg).symm

/-- **The general exactness statement, evaluated on the contact family.** The exponent is one and the
cofactor is the accepted residual equation, which is prime to the exceptional coordinate — so the
accepted factorisation removes *all* exceptional factors, not merely one. -/
theorem chartOrderExact_firstEquationPoly (m : ℕ) :
    chartSubstitution (vCoord - uCoord ^ (m + 1) : planeRing k)
        = uCoord ^ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k)
          * (vCoord - uCoord ^ m)
      ∧ ¬ (uCoord ∣ (vCoord - uCoord ^ m : planeRing k)) := by
  refine ⟨?_, not_uCoord_dvd_vCoord_sub_uCoord_pow m⟩
  rw [centerOrder_firstEquationPoly, pow_one]
  exact chartSubstitution_firstEquationPoly m

/-! ## The section-level specialisation -/

/-- The accepted section factorisation with the order displayed. Beyond
`FrobeniusStrictTransformFirstChartTensorFrame.firstStepEquation_section_factorization` its content is the
exponent alone; it is recorded because the order-indexed shape is the one the general theorem
(`FrobeniusChartSectionFactorization.chartBlowdown_section_factorization`) produces. -/
theorem firstEquation_section_factorization_order (m : ℕ) :
    (coordinateBlowdown (k := k)).appTop
        (KltDP.Examples.FrobeniusGraphPicardClassAffine.firstEquation (k := k) (m + 1)) =
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord)
          ^ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k)
        * KltDP.Examples.FrobeniusGraphPicardClassAffine.firstEquation (k := k) m := by
  rw [centerOrder_firstEquationPoly, pow_one]
  exact KltDP.Examples.FrobeniusStrictTransformFirstChartTensorFrame.firstStepEquation_section_factorization m

end KltDP.Examples.FrobeniusChartContactOrder
