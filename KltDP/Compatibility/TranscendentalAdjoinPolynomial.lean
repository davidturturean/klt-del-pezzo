/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Compatible adaptation of the polynomial simple-adjoin helpers in Mathlib
commit 59e84018b299993f5d4ca6d8cb4012b08bc55241,
Mathlib/RingTheory/Algebraic/Basic.lean, lines 590-605 and 629-631.
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Transcendental polynomial evaluation onto its original simple adjoin

The polynomial equivalence and its coercion normalization preserve the
upstream full commutative-base-ring/ring-algebra statements. Their proofs
use the pinned injectivity and aeval-range APIs. The separately named UFD
adapter uses the pinned domain-based unique-factorization classes; it
therefore applies to every field in the field-general Lüroth port without
claiming that the two versions' UFD class telescopes are identical.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Polynomial

variable (R : Type u) {S : Type v} [CommRing R] [Ring S] [Algebra R S]

/-- A transcendental element identifies the polynomial algebra with the
actual subalgebra it generates, by evaluation at that original element. -/
def algEquivOfTranscendental (s : S) (h : Transcendental R s) :
    R[X] ≃ₐ[R] Algebra.adjoin R {s} :=
  AlgEquiv.ofBijective
    (aeval (⟨s, Algebra.self_mem_adjoin_singleton R s⟩ : Algebra.adjoin R {s})) <| by
    constructor
    · intro p q hpq
      apply transcendental_iff_injective.mp h
      simpa only [coe_aeval_mk_apply] using congrArg Subtype.val hpq
    · rintro ⟨t, ht⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at ht
      obtain ⟨p, hp⟩ := ht
      refine ⟨p, Subtype.ext ?_⟩
      simpa only [coe_aeval_mk_apply] using hp

@[simp]
theorem algEquivOfTranscendental_coe (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] →+* Algebra.adjoin R {s}) =
      aeval (R := R) (A := Algebra.adjoin R {s})
        ⟨s, Algebra.self_mem_adjoin_singleton R s⟩ := rfl

end Polynomial

namespace KltDP.Compatibility.TranscendentalAdjoinPolynomial

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [UniqueFactorizationMonoid R] [Ring S] [IsDomain S] [Algebra R S]

/-- The pinned UFD transfer for a transcendental simple adjoin of domains.
In particular this covers every pair of fields, in every characteristic. -/
theorem uniqueFactorizationMonoid_adjoin {s : S} (h : Transcendental R s) :
    UniqueFactorizationMonoid (Algebra.adjoin R {s}) :=
  (Polynomial.algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

end KltDP.Compatibility.TranscendentalAdjoinPolynomial

#print axioms Polynomial.algEquivOfTranscendental
#print axioms Polynomial.algEquivOfTranscendental_coe
#print axioms KltDP.Compatibility.TranscendentalAdjoinPolynomial.uniqueFactorizationMonoid_adjoin
