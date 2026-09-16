import KltDP.Examples.FrobeniusBlowupChartIteration
import KltDP.RingTheory.LocalAdicOrder

/-!
# The exceptional coordinate divides a chart pullback to the order of the curve

BRIEF36 task 2: the first module of the Rees computation, scoped deliberately to the half that is
provable at this pin.

## What this proves

For a ring map `φ` carrying an ideal `I` into a principal ideal `(t)`, the image `φ f` of an element
of `I ^ d` is divisible by `t ^ d` (`pow_dvd_of_mem_pow`). Taking `d` to be the adic order supplies
the sharp exponent (`pow_adicOrder_dvd`). Instantiated at the accepted blowup chart — `φ =
chartSubstitution`, `I = centerIdeal`, `t = uCoord` — this gives

`uCoord ^ (order of f at the centre) ∣ chartSubstitution f`

for every nonzero `f` in the polynomial plane (`uCoord_pow_centerOrder_dvd_chartSubstitution`).

The base case is **not** rebuilt: `FrobeniusBlowupContact.chartSubstitution_center` already states that
`chartSubstitution` carries `centerIdeal` into `span {chartSubstitution centerU}`, and
`chartSubstitution_u` identifies that generator as `uCoord`. Only the passage to the `d`-th power and
the identification of `d` with the order are new here.

## A correction to the statement of the task

The brief asked for `σ^*f = u^{ord f} × unit`. That is **false** as stated: the cofactor is a unit only
away from the strict transform. The correct local statement is

`σ^*f = u^{ord f} · g` with `u ∤ g`,

where `g` reduces mod `u` to the dehomogenised leading form `f_d(1, v)`. The cofactor is the strict
transform's equation on this chart, which vanishes exactly where the strict transform meets `E`, so it
is not a unit there. This module proves the factorisation and leaves the non-divisibility of `g`
explicitly open; see below.

## What the global step still needs

1. **Exactness of the exponent**, recorded as `ChartOrderExact`. The existential factorisation is
   proved unconditionally (`exists_chartSubstitution_factor`); what is missing is `¬ uCoord ∣ g`.
   Mathematically `g ≡ f_d(1, v) mod uCoord` where `f_d` is the leading form, so this needs the
   decomposition of `f` into forms homogeneous in `(u, v)` and the fact that the leading form is
   nonzero — i.e. exactly the **associated graded ring** of the `centerIdeal`-filtration, which the
   pinned Mathlib cannot construct (it has `Ideal.Filtration` and no `gr`). This is the same missing
   object that blocks `HasAdditiveAdicOrder`; the two gaps are one gap.
2. **The order of a specific equation.** Only `1 ≤ order` is proved here, for the Frobenius contact
   equations. The exact value needs a lower bound *and* a non-membership; for
   `vCoord - uCoord ^ (m+1)` the order is `1`, and non-membership in `centerIdeal ^ 2` is witnessed by
   the `k`-algebra map to `k[s]/(s²)` sending `uCoord ↦ 0`, `vCoord ↦ s`, under which the equation goes
   to `s ≠ 0` while `centerIdeal ^ 2` goes to `0`. Not built this round.
3. **Globalisation.** Passing from this chart identity to the divisor identity `σ^*C = C̃ + m·E` needs
   the second chart, the agreement of the two chart orders on the overlap, and the comparison of the
   local factorisation with the Weil coefficient at `E` — that last step being a genuine theorem, not a
   composition, since it identifies a coefficient with an order.

## Consistency with the accepted order-one line

`FrobeniusStrictTransformFirstChartProduct.firstStepEquation_factorization` states
`firstStepSectionMap (vCoord - uCoord^(m+1)) = uCoord * (vCoord - uCoord^m)` — one exceptional factor,
because `vCoord - uCoord^(m+1)` is smooth at the centre. That is precisely the order-one instance of
the general statement, and `uCoord_dvd_chartSubstitution_firstEquationPoly` below rederives its
divisibility content from the order, independently of the explicit factorisation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace KltDP.Examples.FrobeniusChartPullbackOrder

open KltDP.RingTheory.LocalAdicOrder
open KltDP.Examples.FrobeniusBlowupContact

/-! ## The generic divisibility statement -/

section Generic

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- If a ring map carries `I` into the principal ideal `(t)`, it carries `I ^ d` into `(t ^ d)`. -/
theorem map_pow_le_span_pow (φ : A →+* B) (I : Ideal A) (t : B)
    (hφ : Ideal.map φ I ≤ Ideal.span {t}) (d : ℕ) :
    Ideal.map φ (I ^ d) ≤ Ideal.span {t ^ d} := by
  rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
  exact Ideal.pow_right_mono hφ d

/-- Hence `t ^ d` divides the image of every element of `I ^ d`. -/
theorem pow_dvd_of_mem_pow (φ : A →+* B) (I : Ideal A) (t : B)
    (hφ : Ideal.map φ I ≤ Ideal.span {t}) {d : ℕ} {f : A} (hf : f ∈ I ^ d) :
    t ^ d ∣ φ f :=
  Ideal.mem_span_singleton.mp
    (map_pow_le_span_pow φ I t hφ d (Ideal.mem_map_of_mem φ hf))

/-- **The divisibility half of the order computation**, with the sharp exponent. -/
theorem pow_adicOrder_dvd (φ : A →+* B) (I : Ideal A) (t : B)
    (hφ : Ideal.map φ I ≤ Ideal.span {t}) {f : A} (hbdd : BddAbove (powMemSet I f)) :
    t ^ adicOrder I f ∣ φ f :=
  pow_dvd_of_mem_pow φ I t hφ (mem_pow_adicOrder hbdd)

end Generic

/-! ## The blowup chart of the polynomial plane -/

variable {k : Type u} [Field k]

/-- The centre is proper, from the accepted maximality instance. -/
theorem centerIdeal_ne_top : (centerIdeal (k := k)) ≠ ⊤ :=
  Ideal.IsMaximal.ne_top inferInstance

/-- Boundedness at the centre, by Krull for Noetherian domains. The plane is not local, so the
closed-point supplier does not apply; the domain supplier does. -/
theorem bddAbove_center (f : planeRing k) (hf : f ≠ 0) :
    BddAbove (powMemSet (centerIdeal (k := k)) f) :=
  bddAbove_powMemSet_of_isDomain centerIdeal_ne_top hf

/-- **The contact order of a plane curve at the blowup centre.** -/
abbrev centerOrder (f : planeRing k) : ℕ := adicOrder (centerIdeal (k := k)) f

/-- The accepted chart statement, with the generator named as the coordinate. -/
theorem chartSubstitution_center_uCoord :
    Ideal.map (chartSubstitution (k := k)) centerIdeal ≤ Ideal.span {uCoord (k := k)} := by
  have h : Ideal.map (chartSubstitution (k := k)) centerIdeal ≤
      Ideal.span {chartSubstitution (uCoord (k := k))} := chartSubstitution_center
  rwa [chartSubstitution_u] at h

/-- **The exceptional coordinate divides the chart pullback to the order of the curve.** -/
theorem uCoord_pow_centerOrder_dvd_chartSubstitution (f : planeRing k) (hf : f ≠ 0) :
    uCoord ^ centerOrder f ∣ chartSubstitution f :=
  pow_adicOrder_dvd chartSubstitution centerIdeal uCoord chartSubstitution_center_uCoord
    (bddAbove_center f hf)

/-- **The factorisation.** The cofactor exists unconditionally; that it is not divisible by `uCoord`
is the open half, recorded as `ChartOrderExact`. -/
theorem exists_chartSubstitution_factor (f : planeRing k) (hf : f ≠ 0) :
    ∃ g : planeRing k, chartSubstitution f = uCoord ^ centerOrder f * g :=
  uCoord_pow_centerOrder_dvd_chartSubstitution f hf

/-- **The exactness half, as a named `Prop`.** The pinned Mathlib has no associated graded ring of an
ideal filtration, so the leading form — which is what makes the cofactor prime to `uCoord` — cannot be
constructed. Consumers carry this explicitly until that object exists. -/
def ChartOrderExact (k : Type u) [Field k] : Prop :=
  ∀ f : planeRing k, f ≠ 0 →
    ∃ g : planeRing k, chartSubstitution f = uCoord ^ centerOrder f * g ∧ ¬ (uCoord ∣ g)

/-! ## Nonvacuity: the Frobenius contact equations -/

/-- The contact equation is nonzero: it is monic of degree one in the outer variable. -/
theorem firstEquationPoly_ne_zero (m : ℕ) :
    (vCoord - uCoord ^ (m + 1) : planeRing k) ≠ 0 := by
  have h : (vCoord - uCoord ^ (m + 1) : planeRing k)
      = Polynomial.X - Polynomial.C (Polynomial.X ^ (m + 1)) := by
    show (Polynomial.X - (Polynomial.C Polynomial.X) ^ (m + 1) : planeRing k) = _
    rw [← Polynomial.C_pow]
  rw [h]
  exact Polynomial.X_sub_C_ne_zero _

/-- The contact equation passes through the centre. -/
theorem firstEquationPoly_mem_center (m : ℕ) :
    (vCoord - uCoord ^ (m + 1) : planeRing k) ∈ centerIdeal := by
  refine Ideal.sub_mem _ ?_ ?_
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_insert _ _)) _ (Nat.succ_pos m)

/-- Hence its order at the centre is at least one. -/
theorem one_le_centerOrder_firstEquationPoly (m : ℕ) :
    1 ≤ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k) :=
  (one_le_adicOrder_iff_mem (bddAbove_center _ (firstEquationPoly_ne_zero m))).mpr
    (firstEquationPoly_mem_center m)

/-- **Consistency with the accepted order-one factorisation**, derived from the order rather than from
the explicit computation. -/
theorem uCoord_dvd_chartSubstitution_firstEquationPoly (m : ℕ) :
    uCoord ∣ chartSubstitution (vCoord - uCoord ^ (m + 1) : planeRing k) := by
  have h := uCoord_pow_centerOrder_dvd_chartSubstitution
    (vCoord - uCoord ^ (m + 1) : planeRing k) (firstEquationPoly_ne_zero m)
  have h1 : (uCoord (k := k)) ^ 1 ∣
      (uCoord (k := k)) ^ centerOrder (vCoord - uCoord ^ (m + 1) : planeRing k) :=
    pow_dvd_pow _ (one_le_centerOrder_firstEquationPoly m)
  rw [pow_one] at h1
  exact h1.trans h

end KltDP.Examples.FrobeniusChartPullbackOrder
