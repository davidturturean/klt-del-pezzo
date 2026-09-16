import KltDP.RingTheory.LocalAdicOrder
import KltDP.Geometry.UFDDivisorCoordinates
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Defs

/-!
# The multiplicity of a curve germ at a closed point

BRIEF50 task 2. The multiplicity `m` of a curve at a point — the coefficient that must appear in
`σ^*C = C̃ + m·E` — is the adic order, at the maximal ideal, of a **local equation** of the curve.
The accepted `cartierOrderAt` cannot serve: it requires the stalk to be a `IsDiscreteValuationRing`,
which is the codimension-one situation, whereas the centre of a point blowup is a closed point whose
stalk on a surface has dimension two.

## Why this is a multiplicity and not bookkeeping

A local equation is only determined **up to a unit**, so a number extracted from one is a multiplicity
only if it does not depend on which equation was chosen. That is the content here:

* `adicOrder_mul_isUnit` / `adicOrder_eq_of_associated` — the adic order is invariant under
  multiplication by a unit, hence under associates;
* `primeMultiplicity_eq_of_span` — **every** generator of the prime computes the same number, not just
  the chosen one.

Apply the vacuity test: if `primeMultiplicity` were defined as, say, the coefficient of `E` in some
pullback, then "the coefficient equals the multiplicity" would be true by construction and would
constrain nothing. Here the definition is made on the *base*, from the curve's own germ, with no
reference to a blowup at all — and `primeMultiplicity_eq_of_span` would be **false** for any variant
of the order that were not unit-invariant. That is what makes it content.

## The unit-invariance is hypothesis-free, which is worth noting

`u * f ∈ Iⁿ ↔ f ∈ Iⁿ` for a unit `u`, so the two exponent sets `powMemSet` are *literally equal* and
the orders agree as suprema. No Noetherian hypothesis, no boundedness, no `f ≠ 0`: the junk value of
an unbounded set is carried along identically on both sides. Only the positivity statement needs the
standing finiteness assumptions.

## Scope, and the gap that stops this short of the geometric statement

This module is ring-theoretic: it fixes the multiplicity of a **height-one prime** of a Noetherian
local UFD, which is exactly the germ at `x` of a curve through `x`. Packaging it as a function of a
`PrimeCurve` and a point of a surface requires `PrimeCurve.stalkHeightOnePrime`, and that accepted
construction takes an **affine chart `U` as an argument**: `PrimeCurveStalkCoordinates` proves
`stalkHeightOnePrime_comap` and `stalkHeightOnePrime_injective`, but **not** that the resulting stalk
prime is independent of `U`. Until that independence is proved, a geometric `curveMultiplicityAt`
defined through it would depend on a chart, so it is deliberately **not** defined here; the gap is
reported rather than hidden behind a chosen chart.
-/

noncomputable section

universe u

namespace KltDP.RingTheory.LocalMultiplicity

open KltDP.RingTheory.LocalAdicOrder
open IsLocalRing

/-! ## Unit invariance of the adic order -/

variable {R : Type u} [CommRing R]

/-- Multiplying by a unit does not change membership in a power of an ideal. -/
theorem mem_pow_mul_isUnit_iff (I : Ideal R) {u : R} (hu : IsUnit u) (f : R) (n : ℕ) :
    u * f ∈ I ^ n ↔ f ∈ I ^ n := by
  obtain ⟨v, rfl⟩ := hu
  constructor
  · intro h
    have hv := Ideal.mul_mem_left (I ^ n) (↑v⁻¹ : R) h
    rwa [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at hv
  · intro h
    exact Ideal.mul_mem_left _ _ h

/-- Hence the exponent sets of `f` and `u * f` are **equal**, not merely cofinal. -/
theorem powMemSet_mul_isUnit (I : Ideal R) {u : R} (hu : IsUnit u) (f : R) :
    powMemSet I (u * f) = powMemSet I f :=
  Set.ext fun n => mem_pow_mul_isUnit_iff I hu f n

/-- **The adic order is unit-invariant.** No finiteness hypothesis is needed: the two suprema are
taken over the same set. -/
theorem adicOrder_mul_isUnit (I : Ideal R) {u : R} (hu : IsUnit u) (f : R) :
    adicOrder I (u * f) = adicOrder I f :=
  congrArg sSup (powMemSet_mul_isUnit I hu f)

/-- **Associated elements have the same adic order** — the statement that makes an order computed
from a local equation independent of the equation. -/
theorem adicOrder_eq_of_associated (I : Ideal R) {f g : R} (h : Associated f g) :
    adicOrder I f = adicOrder I g := by
  obtain ⟨v, rfl⟩ := h
  have hv := adicOrder_mul_isUnit I v.isUnit f
  rw [mul_comm f (↑v : R)]
  exact hv.symm

/-! ## The multiplicity of a height-one prime at the closed point -/

section Local

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] [IsLocalRing R]

/-- **The multiplicity of a curve germ at the closed point**: the `m`-adic order of a local equation
of the height-one prime `p`. Defined through the accepted chosen generator; `primeMultiplicity_eq_of_span`
shows the choice does not matter. -/
def primeMultiplicity (p : AffineHeightOnePrime R) : ℕ :=
  localAdicOrder (heightOnePrimeGenerator R p)

/-- **Well-definedness, and the content of the definition**: *any* generator of the prime computes the
multiplicity. Without unit-invariance of the adic order this would be false. -/
theorem primeMultiplicity_eq_of_span (p : AffineHeightOnePrime R) {g : R}
    (hg : Ideal.span {g} = p.1.asIdeal) :
    localAdicOrder g = primeMultiplicity R p := by
  have hspan : Ideal.span {g} = Ideal.span {heightOnePrimeGenerator R p} :=
    hg.trans (heightOnePrimeGenerator_span R p).symm
  exact adicOrder_eq_of_associated _ (Ideal.span_singleton_eq_span_singleton.mp hspan)

/-- **Positivity**: a curve through the closed point has multiplicity at least one there, because a
generator of a height-one prime is a nonunit. -/
theorem one_le_primeMultiplicity (p : AffineHeightOnePrime R) :
    1 ≤ primeMultiplicity R p :=
  (one_le_localAdicOrder_iff_nonunit (heightOnePrimeGenerator_prime R p).ne_zero).mpr
    (heightOnePrimeGenerator_prime R p).not_unit

end Local

end KltDP.RingTheory.LocalMultiplicity
