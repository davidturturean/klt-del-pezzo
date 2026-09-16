import KltDP.Examples.FrobeniusChartOrderExact
import KltDP.Examples.FrobeniusStrictTransformFirstChartProduct
import KltDP.Examples.FrobeniusBlowupChartIteration

/-!
# The chart blowdown pulls back an arbitrary equation with exactly `ord f` exceptional factors

BRIEF42 (rescoped). This is the section-level form of `ChartOrderExact`: for **any** nonzero `f` in the
polynomial plane,

  `σ^*f = u^(ord f) · g`   with `u ∤ g`,

as an identity of global sections on the coordinate chart, obtained from the ring-level statement by the
`ΓSpecIso` transport.

## What is new, stated precisely

The accepted `FrobeniusStrictTransformFirstChartTensorFrame.firstStepEquation_section_factorization` reads

  `coordinateBlowdown.appTop (firstEquation (m+1)) = (ΓSpecIso).inv uCoord * firstEquation m`

— **one** exceptional factor, and no order appears anywhere. That is not a special case of a formula in
`m`: it is the statement for a *single family*, `firstEquation p = (ΓSpecIso).inv (vCoord - uCoord ^ p)`,
every member of which has multiplicity exactly `1` at the origin because the `v` term is linear. So the
accepted statement needs no notion of order precisely because the order is constantly one.

The generalisation here is therefore **not** "`1 → m` within that family" but

  *that family at order one*  ⟶  *any `f ≠ 0` at its own order `ord f`*,

with the exponent supplied by `adicOrder centerIdeal` and the non-divisibility of the cofactor supplied by
`ChartOrderExact`. Removing the family-specificity is the additive content; the transport itself is the
same `congrArg (ΓSpecIso).inv` argument the accepted proof uses, needing `map_pow` in addition to
`map_mul` because the exceptional factor now carries an exponent.

## The corrected form

`σ^*f = u^(ord f) · g` with `u ∤ g` — **not** `u^(ord f) × unit`. The cofactor `g` is the strict
transform's equation on this chart, so it vanishes exactly where the strict transform meets the
exceptional curve and is a unit only away from it.

## What is deliberately not proved

No corollary specialising back to `firstStepEquation_section_factorization` is given. That needs
`centerOrder (vCoord - uCoord ^ (m+1)) = 1` **exactly**, whereas only `1 ≤ centerOrder` is available
(`FrobeniusChartPullbackOrder.one_le_centerOrder_firstEquationPoly`); the exact value requires the
non-membership witness in `centerIdeal ^ 2`, via the `k`-algebra map to `k[s]/(s²)` sending `u ↦ 0`,
`v ↦ s`, which is not built. Recording that rather than asserting the specialisation.

Weil-divisor forms of this identity are blocked elsewhere: there is no Weil-side pullback in the tree, and
carrying `σ^*C` across `cartierWeilEquiv` would need the point blowup presented as a
`NormalProjectiveSurface` with factorial stalks, whose `normal` and `dimension_two` fields are unbuilt.
That is recorded as a planning gap, not attempted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusChartSectionFactorization

open KltDP.RingTheory.LocalAdicOrder
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupChartIteration
open KltDP.Examples.FrobeniusChartPullbackOrder
open KltDP.Examples.FrobeniusChartOrderExact

variable {k : Type u} [Field k]

/-- **The chart blowdown pulls an arbitrary plane equation back with exactly `ord f` exceptional
factors, and the cofactor is prime to the exceptional coordinate.** -/
theorem chartBlowdown_section_factorization (f : planeRing k) (hf : f ≠ 0) :
    ∃ g : planeRing k,
      (coordinateBlowdown (k := k)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv f)
        = ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv uCoord) ^ centerOrder f
          * (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv g
      ∧ ¬ (uCoord ∣ g) := by
  obtain ⟨g, hg, hndvd⟩ := chartOrderExact f hf
  refine ⟨g, ?_, hndvd⟩
  have hss : KltDP.Examples.FrobeniusStrictTransformFirstChartProduct.firstStepSectionMap (k := k) f
      = uCoord ^ centerOrder f * g := by
    rw [KltDP.Examples.FrobeniusStrictTransformFirstChartProduct.firstStepSectionMap_eq]
    exact hg
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv hss
  change (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).hom
        ((coordinateBlowdown (k := k)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv f)))
    = (Scheme.ΓSpecIso (CommRingCat.of (planeRing k))).inv
        (uCoord ^ centerOrder f * g) at h
  rw [Iso.hom_inv_id_apply, map_mul, map_pow] at h
  exact h

end KltDP.Examples.FrobeniusChartSectionFactorization
