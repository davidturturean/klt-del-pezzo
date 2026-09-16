/-
Adapted from the UW Math AI auslander-buchsbaum repository,
`Reference/Nagata theorem.lean`, revision
ff45bce9228646c73f0dc0f40c1459f37d5c6307.
Released under Apache 2.0, as specified by that repository's LICENSE.
The original source and full license are preserved under
audit/library_reuse/regular_local_factorial/uw_source/.
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Nagata's factoriality criterion for localization away from a prime

This port uses the denominator cancellation and reduced-prime lifting argument
of the cited UW source. The final argument uses pinned Mathlib's existence of
irreducible factors instead of porting the source's multiset reconstruction.

The rings, algebra map and localization are actual Mathlib objects. Factoriality
of the localized ring remains a hypothesis. No assertion about regular local
rings is made here. See `docs/NAGATA_FACTORIALITY_PORT.md` for the source review.
-/

namespace KltDP.Compatibility.NagataFactoriality

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Cancel a power of a prime denominator when that prime does not divide the
prospective divisor. This does not require the prospective divisor to be prime. -/
theorem dvd_of_mul_prime_pow_eq {f a x r : R} (hf : Prime f)
    (hfa : ¬ f ∣ a) (n : ℕ) (h : x * f ^ n = a * r) : a ∣ x := by
  induction n generalizing r with
  | zero => exact ⟨r, by simpa using h⟩
  | succ n ih =>
    have hf_ar : f ∣ a * r := by
      refine ⟨x * f ^ n, ?_⟩
      calc
        a * r = x * f ^ (n + 1) := h.symm
        _ = f * (x * f ^ n) := by rw [pow_succ]; ac_rfl
    obtain ⟨r', hr⟩ := (hf.dvd_or_dvd hf_ar).resolve_left hfa
    have heq : (x * f ^ n) * f = (a * r') * f := by
      calc
        (x * f ^ n) * f = x * f ^ (n + 1) := by rw [pow_succ, mul_assoc]
        _ = a * r := h
        _ = (a * r') * f := by rw [hr]; ac_rfl
    exact ih (r := r') (mul_right_cancel₀ hf.ne_zero heq)

section Localization

variable {T : Type*} [CommRing T] [Algebra R T]
variable {f : R} [IsLocalization.Away f T]

/-- The algebra map to a localization away from a nonzero element of a domain
is injective. -/
theorem algebraMap_injective (hf : f ≠ 0) :
    Function.Injective (algebraMap R T) :=
  IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

include f

omit [IsDomain R] in
/-- Every element of the actual localization is associated to the image of an
element of the original ring. -/
theorem exists_associated_algebraMap (z : T) :
    ∃ a : R, Associated z (algebraMap R T a) := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f z
  exact ⟨a, (associated_mul_unit_right z (algebraMap R T f ^ n)
    (IsLocalization.Away.algebraMap_pow_isUnit f n)).trans ⟨1, by simpa using ha⟩⟩

/-- Divisibility descends through localization away from a prime whenever the
prime denominator does not divide the prospective divisor. -/
theorem dvd_of_algebraMap_dvd (hf : Prime f) {a x : R} (hfa : ¬ f ∣ a)
    (hdiv : algebraMap R T a ∣ algebraMap R T x) : a ∣ x := by
  obtain ⟨z, hz⟩ := hdiv
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj f z
  have heq : x * f ^ n = a * r := by
    apply algebraMap_injective (T := T) hf.ne_zero
    calc
      algebraMap R T (x * f ^ n) =
          algebraMap R T x * algebraMap R T f ^ n := by rw [map_mul, map_pow]
      _ = (algebraMap R T a * z) * algebraMap R T f ^ n := by rw [hz]
      _ = algebraMap R T a * (z * algebraMap R T f ^ n) := mul_assoc _ _ _
      _ = algebraMap R T a * algebraMap R T r := by rw [hr]
      _ = algebraMap R T (a * r) := (map_mul (algebraMap R T) a r).symm
  exact dvd_of_mul_prime_pow_eq hf hfa n heq

/-- A prime in the localization descends to a prime representative once the
representative is not divisible by the prime denominator. -/
theorem prime_of_algebraMap_prime (hf : Prime f) {a : R} (hfa : ¬ f ∣ a)
    (ha : Prime (algebraMap R T a)) : Prime a := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    exact ha.ne_zero (by rw [hzero, map_zero])
  · intro hunit
    exact ha.not_unit (hunit.map (algebraMap R T))
  · intro x y hxy
    have hmap : algebraMap R T a ∣ algebraMap R T x * algebraMap R T y := by
      simpa only [map_mul] using map_dvd (algebraMap R T) hxy
    rcases ha.dvd_or_dvd hmap with hx | hy
    · exact Or.inl (dvd_of_algebraMap_dvd hf hfa hx)
    · exact Or.inr (dvd_of_algebraMap_dvd hf hfa hy)

variable [IsNoetherianRing R]

/-- A prime of the localization has an associated image of an actual prime of
the original Noetherian domain, not divisible by the prime denominator. -/
theorem prime_lifts (hf : Prime f) {q : T} (hq : Prime q) :
    ∃ a : R, Prime a ∧ Associated q (algebraMap R T a) ∧ ¬ f ∣ a := by
  obtain ⟨a₀, h₀⟩ := exists_associated_algebraMap (f := f) q
  have ha₀ : a₀ ≠ 0 := by
    intro hzero
    exact (h₀.ne_zero_iff.mp hq.ne_zero) (by rw [hzero, map_zero])
  obtain ⟨n, a, hfa, heq⟩ := WfDvdMonoid.max_power_factor ha₀ hf.irreducible
  have hmap : algebraMap R T a₀ = algebraMap R T f ^ n * algebraMap R T a := by
    rw [heq, map_mul, map_pow]
  have hmap_assoc : Associated (algebraMap R T a₀)
      (algebraMap R T f ^ n * algebraMap R T a) := ⟨1, by simpa using hmap⟩
  have hassoc : Associated q (algebraMap R T a) :=
    h₀.trans (hmap_assoc.trans
      (associated_unit_mul_left (algebraMap R T a) (algebraMap R T f ^ n)
        (IsLocalization.Away.algebraMap_pow_isUnit f n)))
  exact ⟨a, prime_of_algebraMap_prime hf hfa (hassoc.prime hq), hassoc, hfa⟩

variable [IsDomain T] [UniqueFactorizationMonoid T]

include T

/-- Every irreducible of the original ring is prime if localization away from
the specified prime denominator is factorial. -/
theorem irreducible_prime_of_away (hf : Prime f) {p : R}
    (hp : Irreducible p) : Prime p := by
  classical
  by_cases hfp : f ∣ p
  · exact (hf.irreducible.associated_of_dvd hp hfp).prime hf
  · have hpmap₀ : algebraMap R T p ≠ 0 := by
      intro hzero
      apply hp.ne_zero
      apply algebraMap_injective (T := T) hf.ne_zero
      simpa only [map_zero] using hzero
    have hpmap_unit : ¬ IsUnit (algebraMap R T p) := by
      intro hunit
      have hdiv : algebraMap R T p ∣ algebraMap R T (1 : R) := by
        simpa only [map_one] using (isUnit_iff_dvd_one.mp hunit)
      exact hp.not_isUnit (isUnit_of_dvd_one (dvd_of_algebraMap_dvd hf hfp hdiv))
    obtain ⟨q, hq, hqp⟩ := WfDvdMonoid.exists_irreducible_factor hpmap_unit hpmap₀
    have hqprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
    obtain ⟨a, ha, hassoc, hfa⟩ := prime_lifts hf hqprime
    have hadiv : a ∣ p :=
      dvd_of_algebraMap_dvd hf hfa (hassoc.dvd_iff_dvd_left.mp hqp)
    exact (ha.irreducible.associated_of_dvd hp hadiv).prime ha

/-- Nagata's criterion for a Noetherian domain and an actual localization away
from a prime element. Factoriality of the localized ring is retained as an
explicit typeclass hypothesis; no regularity implication is assumed. -/
theorem uniqueFactorizationMonoid_of_away (hf : Prime f) :
    UniqueFactorizationMonoid R := by
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro x hx
  obtain ⟨s, hs, hassoc⟩ := WfDvdMonoid.exists_factors x hx
  exact ⟨s, fun p hp => irreducible_prime_of_away (T := T) hf (hs p hp), hassoc⟩

end Localization

end KltDP.Compatibility.NagataFactoriality
