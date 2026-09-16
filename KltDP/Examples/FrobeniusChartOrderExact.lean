import KltDP.Examples.FrobeniusChartPullbackOrder
import Mathlib.Algebra.Polynomial.Div

/-!
# The chart pullback is exactly divisible: `σ^*f = u^(ord f) · g` with `u ∤ g`

BRIEF41. This closes `ChartOrderExact`, the last input to the local form of the strict transform.

## The reduction

The statement looks like it needs the dehomogenised leading form: `g mod u = f_d(1, v)`, hence the
machinery of homogeneous decompositions a second time. It does not. Writing `f = Σⱼ fⱼ vʲ` with
`fⱼ ∈ k[u]`, the chart substitution `u ↦ u`, `v ↦ u·v` acts coefficientwise as

  `(σ^*f).coeff j = Xʲ · f.coeff j`      (`coeff_chartSubstitution`)

so divisibility of `σ^*f` by `uⁿ` says exactly that every monomial `u^a v^j` of `f` has `a + j ≥ n` —
which is membership in `centerIdealⁿ`. The whole task is therefore one equivalence:

  **`f ∈ centerIdeal ^ n ↔ uCoord ^ n ∣ chartSubstitution f`**

whose forward direction is the divisibility half already proved in `FrobeniusChartPullbackOrder`, and
whose reverse direction gives exactness immediately: `f ∉ centerIdeal ^ (d+1)` forces
`u^(d+1) ∤ σ^*f`, i.e. `u ∤ g`. No leading form, no dehomogenisation, no second decomposition.

## The two levels of divisibility

`planeRing k = (k[u])[v]`, so `uCoord = C X` is a *constant* of the outer ring and `vCoord = X` is the
outer variable. The two divisibility lemmas therefore act at different levels and neither substitutes
for the other:

* `Polynomial.C_dvd_iff_dvd_coeff` at the **outer** level turns `uCoord ^ n ∣ h` into
  `∀ j, Xⁿ ∣ h.coeff j` (`uCoord_pow_dvd_iff`);
* the resulting divisibility is then inside **`k[u]`**, where `Xⁿ ∣ Xʲ · fⱼ` is cancelled to
  `X^(n-j) ∣ fⱼ`.

`Polynomial.X_pow_dvd_iff` is about the *outer* variable, so in this ring it governs `vCoord`, not
`uCoord`; using it at the outer level here would be a statement about the wrong coordinate.

## The corrected form

The factorisation is `σ^*f = u^(ord f) · g` with `u ∤ g` — **not** `u^(ord f) × unit`. The cofactor is
the strict transform's equation on this chart, so it vanishes exactly where the strict transform meets
the exceptional curve, and is a unit only away from it.
-/

noncomputable section

universe u

namespace KltDP.Examples.FrobeniusChartOrderExact

open KltDP.RingTheory.LocalAdicOrder
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusChartPullbackOrder

variable {k : Type u} [Field k]

/-! ## The coefficient formula -/

/-- **The chart substitution multiplies the `j`-th `v`-coefficient by `u^j`.** -/
theorem coeff_chartSubstitution (f : planeRing k) (j : ℕ) :
    (chartSubstitution f).coeff j = Polynomial.X ^ j * f.coeff j := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq, mul_add]
  | monomial e a =>
      have hmono : (Polynomial.monomial e a : planeRing k)
          = Polynomial.C a * vCoord ^ e := by
        show _ = Polynomial.C a * (Polynomial.X : planeRing k) ^ e
        exact Polynomial.C_mul_X_pow_eq_monomial.symm
      have hue : (uCoord (k := k)) ^ e = Polynomial.C (Polynomial.X ^ e) := by
        show (Polynomial.C Polynomial.X : planeRing k) ^ e = _
        rw [← Polynomial.C_pow]
      have hv : ((vCoord (k := k)) ^ e).coeff j = if j = e then 1 else 0 := by
        show ((Polynomial.X : planeRing k) ^ e).coeff j = _
        exact Polynomial.coeff_X_pow e j
      rw [hmono, map_mul, map_pow, chartSubstitution_C, chartSubstitution_v, mul_pow, hue,
        ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, hv]
      split_ifs with h
      · subst h; ring
      · ring

/-! ## Divisibility by a power of the exceptional coordinate -/

/-- Divisibility by `uⁿ` is coefficientwise divisibility by `Xⁿ` in `k[u]` — the **outer** level. -/
theorem uCoord_pow_dvd_iff (n : ℕ) (h : planeRing k) :
    uCoord ^ n ∣ h ↔ ∀ j, (Polynomial.X : Polynomial k) ^ n ∣ h.coeff j := by
  have hue : (uCoord (k := k)) ^ n = Polynomial.C (Polynomial.X ^ n) := by
    show (Polynomial.C Polynomial.X : planeRing k) ^ n = _
    rw [← Polynomial.C_pow]
  rw [hue]
  exact Polynomial.C_dvd_iff_dvd_coeff _ _

/-! ## The equivalence -/

/-- **Membership in a power of the centre is exactly divisibility of the chart pullback.** -/
theorem mem_centerIdeal_pow_iff_uCoord_pow_dvd (n : ℕ) (f : planeRing k) :
    f ∈ centerIdeal ^ n ↔ uCoord ^ n ∣ chartSubstitution f := by
  constructor
  · intro hf
    exact pow_dvd_of_mem_pow chartSubstitution centerIdeal uCoord
      chartSubstitution_center_uCoord hf
  · intro hdvd
    rw [uCoord_pow_dvd_iff] at hdvd
    have hsum : (∑ j ∈ f.support, (Polynomial.monomial j (f.coeff j) : planeRing k)) = f := by
      have hsm := f.sum_monomial_eq
      rwa [Polynomial.sum_def] at hsm
    rw [← hsum]
    refine Ideal.sum_mem _ fun j _ => ?_
    have hmono0 : (Polynomial.monomial j (f.coeff j) : planeRing k)
        = Polynomial.C (f.coeff j) * vCoord ^ j := by
      show _ = Polynomial.C (f.coeff j) * (Polynomial.X : planeRing k) ^ j
      exact Polynomial.C_mul_X_pow_eq_monomial.symm
    have hvmem : (vCoord (k := k)) ∈ centerIdeal :=
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have humem : (uCoord (k := k)) ∈ centerIdeal := Ideal.subset_span (Set.mem_insert _ _)
    by_cases hjn : n ≤ j
    · have hvj : (vCoord (k := k)) ^ j ∈ centerIdeal ^ n :=
        Ideal.pow_le_pow_right hjn (Ideal.pow_mem_pow hvmem j)
      rw [hmono0]
      exact Ideal.mul_mem_left _ _ hvj
    · push_neg at hjn
      have hj := hdvd j
      rw [coeff_chartSubstitution] at hj
      have hXj : (Polynomial.X : Polynomial k) ^ j ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
      have hsplit : (Polynomial.X : Polynomial k) ^ n
          = Polynomial.X ^ j * Polynomial.X ^ (n - j) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit] at hj
      obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_left hXj).mp hj
      have huc : (uCoord (k := k)) ^ (n - j) = Polynomial.C (Polynomial.X ^ (n - j)) := by
        show (Polynomial.C Polynomial.X : planeRing k) ^ (n - j) = _
        rw [← Polynomial.C_pow]
      have hprod : (uCoord (k := k)) ^ (n - j) * (Polynomial.C c * vCoord ^ j)
          ∈ centerIdeal ^ n := by
        have hu : (uCoord (k := k)) ^ (n - j) ∈ centerIdeal ^ (n - j) :=
          Ideal.pow_mem_pow humem (n - j)
        have hv : (Polynomial.C c * vCoord ^ j : planeRing k) ∈ centerIdeal ^ j :=
          Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hvmem j)
        -- `rw [← pow_add]` fails here twice over: scanning the whole membership it unifies `?a`
        -- against the ELEMENT side and then hunts for `uCoord ^ ?m * uCoord ^ ?n`; and even on the
        -- isolated equation, where the LHS *is* the pattern, it still does not match. So the
        -- identity is supplied as a TERM -- no pattern, no metavariable, no instance guessing.
        have hexp : n - j + j = n := by omega
        have hidx : (centerIdeal (k := k)) ^ (n - j) * centerIdeal ^ j = centerIdeal ^ n :=
          calc (centerIdeal (k := k)) ^ (n - j) * centerIdeal ^ j
              = centerIdeal ^ (n - j + j) := (pow_add centerIdeal (n - j) j).symm
            _ = centerIdeal ^ n := by rw [hexp]
        have hmul := Ideal.mul_mem_mul hu hv
        rw [hidx] at hmul
        exact hmul
      have hrewrite : (Polynomial.monomial j (f.coeff j) : planeRing k)
          = uCoord ^ (n - j) * (Polynomial.C c * vCoord ^ j) := by
        rw [hmono0, hc, Polynomial.C_mul, ← huc]
        ring
      rw [hrewrite]
      exact hprod

/-! ## Exactness -/

/-- **`ChartOrderExact`: the chart pullback factors as `u^(ord f)` times something prime to `u`.** -/
theorem chartOrderExact : ChartOrderExact k := by
  intro f hf
  obtain ⟨g, hg⟩ := exists_chartSubstitution_factor f hf
  refine ⟨g, hg, ?_⟩
  rintro ⟨c, rfl⟩
  have hdvd : uCoord ^ (centerOrder f + 1) ∣ chartSubstitution f := by
    refine ⟨c, ?_⟩
    rw [hg, pow_succ]
    ring
  exact not_mem_pow_succ (bddAbove_center f hf)
    ((mem_centerIdeal_pow_iff_uCoord_pow_dvd (centerOrder f + 1) f).mpr hdvd)

end KltDP.Examples.FrobeniusChartOrderExact
