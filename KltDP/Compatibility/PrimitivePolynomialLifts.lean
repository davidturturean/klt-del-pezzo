/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

Compatibility adapter for Mathlib/RingTheory/Polynomial/GaussLemma.lean,
commit 59e84018b299993f5d4ca6d8cb4012b08bc55241, lines 238-252.
The pinned library uses NormalizedGCDMonoid in place of the newer
IsGCDMonoid plus a chosen normalization. The proof below uses the pinned
integerNormalization_map_to_map and exact content identities.
-/
import Mathlib.RingTheory.Polynomial.GaussLemma

open Polynomial IsLocalization
open scoped nonZeroDivisors Polynomial

namespace KltDP.Compatibility.PrimitivePolynomialLifts

variable {R K : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Multiplication by a primitive polynomial detects whether a polynomial
over the fraction field has coefficients in the original domain. -/
theorem mul_map_mem_lifts_iff {f : R[X]} (hf : f.IsPrimitive) {g : K[X]} :
    g * f.map (algebraMap R K) ∈ lifts (algebraMap R K) ↔
      g ∈ lifts (algebraMap R K) := by
  classical
  constructor
  · intro hg
    obtain ⟨k, hk⟩ := (mem_lifts _).mp hg
    let g' : R[X] := integerNormalization R⁰ g
    obtain ⟨⟨b, hb⟩, hnorm⟩ := integerNormalization_map_to_map R⁰ g
    rw [Algebra.smul_def, algebraMap_apply, Subtype.coe_mk] at hnorm
    change g'.map (algebraMap R K) = C (algebraMap R K b) * g at hnorm
    have hmul : g' * f = C b * k := by
      apply map_injective (algebraMap R K) (IsFractionRing.injective R K)
      rw [Polynomial.map_mul, Polynomial.map_mul, map_C, hnorm, hk, mul_assoc]
    have hcontent : g'.content = normalize b * k.content := by
      simpa only [content_mul, content_C, hf.content_eq_one, mul_one] using
        congrArg Polynomial.content hmul
    have hbcontent : b ∣ g'.content := by
      rw [hcontent]
      exact (show b ∣ normalize b from dvd_normalize_iff.mpr (dvd_refl b)).trans
        (dvd_mul_right (normalize b) k.content)
    obtain ⟨g'', hfactor⟩ := dvd_content_iff_C_dvd.mp hbcontent
    refine (mem_lifts _).mpr ⟨g'', ?_⟩
    have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hC : C (algebraMap R K b) ≠ (0 : K[X]) := by
      refine C_ne_zero.mpr (fun hb0 => ?_)
      apply hb'
      apply IsFractionRing.injective R K
      simpa only [map_zero] using hb0
    apply mul_left_cancel₀ hC
    calc
      C (algebraMap R K b) * g''.map (algebraMap R K) =
          g'.map (algebraMap R K) := by
        rw [hfactor, Polynomial.map_mul, map_C]
      _ = C (algebraMap R K b) * g := hnorm
  · intro hg
    exact (lifts (algebraMap R K)).mul_mem hg ((mem_lifts _).mpr ⟨f, rfl⟩)

end KltDP.Compatibility.PrimitivePolynomialLifts
