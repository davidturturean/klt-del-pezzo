import KltDP.Geometry.RegularLocalTwoParameters
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Radical ideals of original regular surface parameters

The accepted regular-pair proof already derives primality of the original
first parameter from its nonzero cotangent class. We expose that conclusion.
The original second parameter is prime by symmetry and is not divisible by
the first. The pinned squarefree-product and radical-span theorems then
prove that the original two-branch equation generates a radical ideal.
-/

noncomputable section

universe u

namespace KltDP.Geometry.RegularLocalTwoParameters

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The first original member of a regular surface parameter pair is prime. -/
theorem first_prime (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (a b : R) (hspan : Ideal.span {a, b} = maximalIdeal R) : Prime a := by
  obtain ⟨hDomain, hUFM⟩ := regularLocal_isDomain_and_uniqueFactorizationMonoid R hR
  letI : IsDomain R := hDomain
  letI : UniqueFactorizationMonoid R := hUFM
  have ha : a ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (RegularLocalFactorialSupport.irreducible_of_mem_maximal_not_mem_sq ha
      (PrincipalQuotientParameters.first_not_mem_square hR hdim a b hspan))

/-- The principal ideal of the original first parameter is prime. -/
theorem first_span_isPrime (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (a b : R) (hspan : Ideal.span {a, b} = maximalIdeal R) :
    (Ideal.span {a}).IsPrime := by
  have ha := first_prime hR hdim a b hspan
  exact (Ideal.span_singleton_prime ha.ne_zero).mpr ha

/-- The original product of the two distinct parameters has radical principal ideal. -/
theorem product_span_isRadical (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (a b : R) (hspan : Ideal.span {a, b} = maximalIdeal R) :
    (Ideal.span {a * b}).IsRadical := by
  obtain ⟨hDomain, hUFM⟩ := regularLocal_isDomain_and_uniqueFactorizationMonoid R hR
  letI : IsDomain R := hDomain
  letI : UniqueFactorizationMonoid R := hUFM
  have ha : Prime a := first_prime hR hdim a b hspan
  have hb : Prime b := first_prime hR hdim b a (Ideal.span_pair_comm.trans hspan)
  have hab : ¬ a ∣ b := by
    intro h
    exact second_not_mem_first hR hdim a b hspan (Ideal.mem_span_singleton.mpr h)
  have hsq : Squarefree (a * b) := squarefree_mul_iff.mpr
    ⟨ha.irreducible.isRelPrime_iff_not_dvd.mpr hab, ha.squarefree, hb.squarefree⟩
  exact isRadical_iff_span_singleton.mp hsq.isRadical

end KltDP.Geometry.RegularLocalTwoParameters

#check @KltDP.Geometry.RegularLocalTwoParameters.first_span_isPrime
#check @KltDP.Geometry.RegularLocalTwoParameters.product_span_isRadical
#print axioms KltDP.Geometry.RegularLocalTwoParameters.first_span_isPrime
#print axioms KltDP.Geometry.RegularLocalTwoParameters.product_span_isRadical
