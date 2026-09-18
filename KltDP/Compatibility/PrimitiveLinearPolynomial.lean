/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin

Bounded compatibility port of the full statement
`Polynomial.irreducible_C_mul_X_add_C`, lines 280–284 of
Mathlib/Algebra/Polynomial/RingDivision.lean at official commit
59e84018b299993f5d4ca6d8cb4012b08bc55241.
Source SHA256: df4efea17d794d79fe46161ccf7b3434189a86e1b24eef6ceab3a8885e3abe0e.
The proof below uses the pinned primitive-polynomial descent and
degree-one APIs; no newer degree-computation tactic is required.
-/
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Coprime.Basic

/-!
# Irreducibility of a primitive linear polynomial over a domain

Relative primality of the two coefficients makes the original polynomial
primitive. Its image in the fraction field has degree one, hence is
irreducible. The pinned proved Gauss-lemma descent returns irreducibility
over the original ring. The full upstream domain/relative-primality
signature is retained, without factoriality or Bézout hypotheses.
-/

noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nonconstant linear polynomial is irreducible when its two original
coefficients are relatively prime. -/
theorem irreducible_C_mul_X_add_C {a b : R} (ha : a ≠ 0) (hab : IsRelPrime a b) :
    Irreducible (C a * X + C b) := by
  have hp : (C a * X + C b).IsPrimitive := by
    intro r hr
    have hc := (C_dvd_iff_dvd_coeff r (C a * X + C b)).mp hr
    apply hab
    · simpa [coeff_C_mul_X] using hc 1
    · simpa [coeff_C_mul_X] using hc 0
  refine hp.irreducible_of_irreducible_map_of_injective
    (φ := algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) ?_
  apply irreducible_of_degree_eq_one
  rw [degree_map_eq_of_injective (IsFractionRing.injective R (FractionRing R))]
  exact (degree_add_eq_left_of_degree_lt (degree_C_lt_degree_C_mul_X ha)).trans
    (degree_C_mul_X ha)

end Polynomial

#print Polynomial.irreducible_C_mul_X_add_C
#print axioms Polynomial.irreducible_C_mul_X_add_C
