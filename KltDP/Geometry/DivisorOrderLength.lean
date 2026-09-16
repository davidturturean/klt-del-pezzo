/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

The ideal-order-isomorphism proof is adapted from Mathlib commit
006d1d9d2dfee3e9e4162bee332313cf26b2c191, RingTheory/DiscreteValuationRing/Basic.
The quotient-length and project-order adapters below are local additions.
-/
import KltDP.Geometry.DivisorOrder
import Mathlib.RingTheory.Length

/-!
# DVR quotient lengths and the actual divisor order

A bounded port of the proved Mathlib ideal-order isomorphism identifies the
ideals of a DVR with the opposite order on `ℕ∞`. Consequently the length of
`R ⧸ (r)` is the existing additive DVR valuation of `r`, including infinite
length at zero. For a nonzero element this finite length agrees with the
project's integer `divisorOrder` after the actual fraction-field embedding.
The comparison proves the normalization from units and uniformizer powers.

No scheme intersection multiplicity, degree formula, or literature axiom is
assumed. The last adapter uses the actual structure-sheaf stalk and actual
function field, under an explicit DVR-stalk hypothesis.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory

open Ideal IsLocalRing Submodule.IsPrincipal IsDiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Equality of the pinned additive valuations is association of elements. -/
theorem dvrAddVal_eq_iff_associated (x y : R) :
    addVal R x = addVal R y ↔ Associated x y := by
  rw [le_antisymm_iff, addVal_le_iff_dvd, addVal_le_iff_dvd,
    dvd_dvd_iff_associated]

/-- The actual ideal lattice of a DVR is the opposite of `ℕ∞`.
This is a bounded port of the proved upstream Mathlib construction. -/
def dvrIdealOrderIsoENat : Ideal R ≃o ℕ∞ᵒᵈ where
  toFun I := .toDual (addVal R (generator I))
  invFun n := n.ofDual.recTopCoe ⊥ (fun n ↦ maximalIdeal R ^ n)
  left_inv I := by
    let x := generator I
    suffices (addVal R x).recTopCoe ⊥ (fun n ↦ maximalIdeal R ^ n) = span {x} by
      rwa [Ideal.span_singleton_generator] at this
    by_cases hx0 : x = 0
    · simp only [hx0, addVal_zero, ENat.recTopCoe_top]
      exact (Ideal.span_singleton_eq_bot.mpr rfl).symm
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
      obtain ⟨n, a, ha⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
      rw [ha, addVal_def' a hϖ, span_singleton_mul_left_unit a.isUnit,
        ENat.recTopCoe_coe, hϖ.maximalIdeal_eq, span_singleton_pow]
  right_inv n := by
    obtain ⟨k, rfl⟩ := OrderDual.toDual.surjective n
    dsimp
    induction k with
    | top =>
      have hbot : generator (⊥ : Ideal R) = 0 :=
        (eq_bot_iff_generator_eq_zero (⊥ : Ideal R)).mp rfl
      simp [hbot, addVal_zero]
    | coe k =>
      obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
      rw [OrderDual.toDual_inj, ENat.recTopCoe_coe, hϖ.maximalIdeal_eq,
        span_singleton_pow, ← hϖ.addVal_pow k, dvrAddVal_eq_iff_associated]
      exact associated_generator_span_self (ϖ ^ k)
  map_rel_iff' {I J} := by
    simp [addVal_le_iff_dvd, ← span_singleton_le_span_singleton]

/-- Quotient length agrees with the existing additive DVR valuation.
At zero both sides are infinite; no nonzero input is hidden here. -/
theorem dvr_length_quotient_span_eq_addVal (r : R) :
    Module.length R (R ⧸ Ideal.span {r}) = addVal R r := by
  rw [Module.length_quotient]
  have h := Order.coheight_orderIso (dvrIdealOrderIsoENat R) (Ideal.span {r})
  change Order.coheight (OrderDual.toDual (addVal R (generator (Ideal.span {r})))) =
    Order.coheight (Ideal.span {r}) at h
  rw [Order.coheight_toDual, Order.height_enat] at h
  exact h.symm.trans ((dvrAddVal_eq_iff_associated R _ _).mpr
    (associated_generator_span_self r))

/-- An actual uniformizer power has quotient length equal to its exponent. -/
theorem dvr_length_quotient_uniformizer_pow (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length R (R ⧸ Ideal.span {ϖ ^ n}) = n := by
  rw [dvr_length_quotient_span_eq_addVal, hϖ.addVal_pow]

/-- Multiplying a uniformizer power by a local unit preserves that length. -/
theorem dvr_length_quotient_unit_mul_uniformizer_pow
    (a : Rˣ) (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length R (R ⧸ Ideal.span {(a : R) * ϖ ^ n}) = n := by
  rw [dvr_length_quotient_span_eq_addVal, addVal_def' a hϖ]

/-- Every nonzero principal quotient of a DVR has finite length. -/
theorem dvr_length_quotient_span_ne_top (r : R) (hr : r ≠ 0) :
    Module.length R (R ⧸ Ideal.span {r}) ≠ ⊤ := by
  rw [dvr_length_quotient_span_eq_addVal]
  intro h
  exact hr (addVal_eq_top_iff.mp h)

variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The existing integer divisor order respects natural powers. -/
theorem divisorOrder_pow (f : Kˣ) (n : ℕ) :
    divisorOrder R K (f ^ n) = (n : ℤ) * divisorOrder R K f := by
  induction n with
  | zero => simp only [pow_zero, divisorOrder_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, divisorOrder_mul, ih, Nat.cast_succ, add_mul, one_mul]

/-- Actual fraction-field units respect the unit-times-power factorization. -/
theorem fractionFieldUnit_unit_mul_pow (a : Rˣ) (ϖ : R) (hϖ : ϖ ≠ 0)
    (n : ℕ) (hr : (a : R) * ϖ ^ n ≠ 0) :
    fractionFieldUnit R K ((a : R) * ϖ ^ n) hr =
      Units.map (algebraMap R K) a * (fractionFieldUnit R K ϖ hϖ) ^ n := by
  apply Units.ext
  change algebraMap R K ((a : R) * ϖ ^ n) =
    algebraMap R K (a : R) * (algebraMap R K ϖ) ^ n
  rw [map_mul, map_pow]

/-- A local unit times the `n`th power of an actual uniformizer has integer
order `n` in the actual fraction field. -/
theorem divisorOrder_unit_mul_uniformizer_pow (a : Rˣ) (ϖ : R)
    (hϖ : Irreducible ϖ) (n : ℕ) (hr : (a : R) * ϖ ^ n ≠ 0) :
    divisorOrder R K (fractionFieldUnit R K ((a : R) * ϖ ^ n) hr) = (n : ℤ) := by
  rw [fractionFieldUnit_unit_mul_pow R K a ϖ hϖ.ne_zero n hr,
    divisorOrder_mul, divisorOrder_map_unit, divisorOrder_pow,
    divisorOrder_uniformizer R K ϖ hϖ, mul_one, zero_add]

/-- The project's actual divisor order of a nonzero ring element equals
the finite quotient-module length, viewed as an integer. -/
theorem divisorOrder_eq_quotient_length (r : R) (hr : r ≠ 0) :
    divisorOrder R K (fractionFieldUnit R K r hr) =
      ((Module.length R (R ⧸ Ideal.span {r})).toNat : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, a, rfl⟩ := eq_unit_mul_pow_irreducible hr hϖ
  rw [divisorOrder_unit_mul_uniformizer_pow R K a ϖ hϖ n,
    dvr_length_quotient_unit_mul_uniformizer_pow R a ϖ hϖ n, ENat.toNat_coe]

/-- Nonzero ring elements have nonnegative integer divisor order. -/
theorem divisorOrder_algebraMap_nonneg (r : R) (hr : r ≠ 0) :
    0 ≤ divisorOrder R K (fractionFieldUnit R K r hr) := by
  rw [divisorOrder_eq_quotient_length]
  exact Int.natCast_nonneg _

end KltDP.RingTheory

namespace KltDP.Geometry

open AlgebraicGeometry

local instance (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsDomain (X.presheaf.stalk x) := integralSchemeStalk_isDomain X x

variable (X : Scheme.{u}) [IsIntegral X] (x : X)
variable [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- The actual DVR stalk quotient has finite length for a nonzero stalk
section. The DVR hypothesis is explicit and remains a geometric adapter. -/
theorem stalk_length_quotient_span_ne_top (r : X.presheaf.stalk x) (hr : r ≠ 0) :
    Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.span {r}) ≠ ⊤ :=
  RingTheory.dvr_length_quotient_span_ne_top (X.presheaf.stalk x) r hr

/-- The actual rational-function order of a nonzero stalk section equals
its quotient length over that same stalk ring. -/
theorem stalkDivisorOrder_eq_quotient_length (r : X.presheaf.stalk x) (hr : r ≠ 0) :
    stalkDivisorOrder X x
        (RingTheory.fractionFieldUnit (X.presheaf.stalk x) X.functionField r hr) =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span {r})).toNat : ℤ) :=
  RingTheory.divisorOrder_eq_quotient_length (X.presheaf.stalk x) X.functionField r hr

end KltDP.Geometry
