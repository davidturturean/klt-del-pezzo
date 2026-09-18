import KltDP.RingTheory.FactorialHartogs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
A prime denominator ideal has height one whenever an actual denominator
s sends the fraction to a numerator r outside that prime. In the original
localization at the prime, r is a unit and the maximal ideal is generated
by s. The pinned local PID equivalences and the existing height transport
then give height one. Normality is not needed for this algebraic leaf.
-/

noncomputable section

universe u v

namespace KltDP.RingTheory.NormalHartogs

open FactorialHartogs

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An actual denominator with numerator outside the prime makes the
original denominator prime have height one. -/
theorem prime_denominator_height_eq_one_of_witness (f : K)
    [(denominatorIdeal R K f).IsPrime] (s r : R)
    (hs : s ∈ denominatorIdeal R K f) (hr : r ∉ denominatorIdeal R K f)
    (he : algebraMap R K s * f = algebraMap R K r) :
    (denominatorIdeal R K f).height = 1 := by
  let P : Ideal R := denominatorIdeal R K f
  let S := Localization.AtPrime P
  letI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have hr0 : r ≠ 0 := by
    intro h
    exact hr (h.symm ▸ P.zero_mem)
  have hs0 : s ≠ 0 := by
    intro h
    have hz := he
    rw [h, map_zero, zero_mul] at hz
    apply hr0
    apply IsFractionRing.injective R K
    simpa only [map_zero] using hz.symm
  have hrunit : IsUnit (algebraMap R S r) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S P r).mpr hr
  have hmax : IsLocalRing.maximalIdeal S = Ideal.span {algebraMap R S s} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P)]
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro t ht
      change algebraMap R S t ∈ Ideal.span {algebraMap R S s}
      apply Ideal.mem_span_singleton.mpr
      obtain ⟨a, ha⟩ := ht
      have htr : t * r = s * a := by
        apply IsFractionRing.injective R K
        simp only [map_mul]
        rw [← he, ← ha]
        ring
      apply hrunit.dvd_mul_right.mp
      refine ⟨algebraMap R S a, ?_⟩
      simpa only [map_mul] using congrArg (algebraMap R S) htr
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hs
  have hprincipal : (IsLocalRing.maximalIdeal S).IsPrincipal := by
    rw [hmax]
    exact ⟨⟨algebraMap R S s, rfl⟩⟩
  letI : IsPrincipalIdealRing S :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain S).out 4 0).mp hprincipal
  have hsS0 : algebraMap R S s ≠ 0 := by
    intro h
    apply hs0
    apply IsLocalization.injective S P.primeCompl_le_nonZeroDivisors
    simpa only [map_zero] using h
  have hprime : Prime (algebraMap R S s) :=
    (Ideal.span_singleton_prime hsS0).mp (by rw [← hmax]; infer_instance)
  have hheight : (IsLocalRing.maximalIdeal S).height = 1 := by
    rw [hmax]
    exact KltDP.RingTheory.primeElement_span_height_eq_one S _ hprime
  have hc := IsLocalization.height_comap P.primeCompl (IsLocalRing.maximalIdeal S)
  rw [IsLocalization.AtPrime.comap_maximalIdeal S P] at hc
  exact hc.trans hheight

end KltDP.RingTheory.NormalHartogs
