import KltDP.Geometry.RegularLocalTwoParameters

/-!
# The actual prime ideals of surface parameters

The existing regular-local factoriality and cotangent arguments identify
each principal ideal of the given parameter pair as prime in the
original ring. This supplies the original residual branch quotient with
its domain instance, without a prime-parameter premise.
-/

noncomputable section

namespace KltDP.Geometry.RegularLocalTwoParameters

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem span_first_isPrime (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (f g : R) (hspan : Ideal.span {f, g} = maximalIdeal R) :
    (Ideal.span {f}).IsPrime := by
  obtain ⟨hDomain, hUFM⟩ := regularLocal_isDomain_and_uniqueFactorizationMonoid R hR
  letI : IsDomain R := hDomain
  letI : UniqueFactorizationMonoid R := hUFM
  have hf : f ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  have hfsq := PrincipalQuotientParameters.first_not_mem_square hR hdim f g hspan
  have hprime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (RegularLocalFactorialSupport.irreducible_of_mem_maximal_not_mem_sq hf hfsq)
  exact (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime

theorem span_second_isPrime (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
    (f g : R) (hspan : Ideal.span {f, g} = maximalIdeal R) :
    (Ideal.span {g}).IsPrime :=
  span_first_isPrime hR hdim g f (Ideal.span_pair_comm.trans hspan)

end KltDP.Geometry.RegularLocalTwoParameters
