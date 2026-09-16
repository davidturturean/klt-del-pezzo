/-
Parts adapted from the AlgebraicJacobian contributors' WeilDivisor.lean
(copyright 2026), released under Apache 2.0. The selected source is frozen at
frenzymath/Algebraic-Geometry commit 9223d85c786394721963a9d642b08d066b72a594.
The adaptation reuses the pinned Mathlib valuation in place of Ring.ordFrac.
-/
import KltDP.Geometry.DivisorOrder
import KltDP.Geometry.NormalStalkDVR
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite principal support on an actual normal affine chart

The base ring is a Noetherian integrally closed domain of arbitrary Krull
dimension. Its actual height-one prime localizations are proved to be DVRs.
Their fraction-field valuations define integer orders on actual nonzero
fractions, using `DivisorOrder` and its positive uniformizer convention.

For a fraction `a/b`, a nonzero order can occur only at a height-one prime
containing `a` or `b`. Such a prime is minimal over the corresponding
principal ideal. The existing finiteness of minimal primes in a Noetherian
ring therefore proves finite support. The base ring is not assumed to be
a Dedekind domain, and finite support is a conclusion, not a hypothesis.

The minimal-prime and numerator/denominator proof pattern was reviewed in
`docs/WEIL_DIVISOR_BACKPORT_ASSESSMENT.md`. The actual orders here use only
the current pinned Mathlib valuation APIs. Gluing these affine bounds over
an actual surface remains a separate scheme-level step.
-/

noncomputable section

open IsDedekindDomain
open scoped Multiplicative

universe u v

namespace KltDP.RingTheory

variable (R : Type u) [CommRing R]

/-- Actual height-one primes of an arbitrary commutative ring. This is
distinct from the nonzero-prime spectrum specialized to Dedekind domains. -/
abbrev AffineHeightOnePrime := {p : PrimeSpectrum R // p.asIdeal.height = 1}

section MinimalPrimes

variable {R} [IsDomain R]

/-- In a domain, a height-one prime containing a nonzero element is
minimal over that element's principal ideal. -/
theorem mem_minimalPrimes_span_singleton_of_height_one
    {p : Ideal R} [p.IsPrime] (hp : p.height = 1)
    {a : R} (ha : a ≠ 0) (hap : a ∈ p) :
    p ∈ (Ideal.span {a}).minimalPrimes := by
  have hle : Ideal.span {a} ≤ p :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hap)
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hle
  letI : q.IsPrime := hq.1.1
  have haq : a ∈ q := hq.1.2 (Ideal.subset_span (Set.mem_singleton a))
  have hqbot : q ≠ ⊥ := by
    intro h
    rw [h] at haq
    exact ha (by simpa using haq)
  have hqeq : q = p := by
    rcases eq_or_lt_of_le hqp with h | h
    · exact h
    · exfalso
      letI : (⊥ : Ideal R).IsPrime := Ideal.bot_prime
      have h01 := Ideal.primeHeight_add_one_le_of_lt (bot_lt_iff_ne_bot.mpr hqbot)
      have h1 : (1 : ℕ∞) ≤ q.primeHeight := by
        change Order.height (⊥ : PrimeSpectrum R) + 1 ≤ q.primeHeight at h01
        simpa only [Order.height_bot, zero_add] using h01
      have h12 := Ideal.primeHeight_add_one_le_of_lt h
      have hheight : p.primeHeight = 1 := p.height_eq_primeHeight.symm.trans hp
      rw [hheight] at h12
      have hbad : (2 : ℕ∞) ≤ 1 := (add_le_add_right h1 1).trans h12
      norm_num at hbad
  rwa [← hqeq]

/-- A nonzero element belongs to only finitely many actual height-one
primes in a Noetherian domain. -/
theorem finite_heightOnePrimes_containing [IsNoetherianRing R]
    (a : R) (ha : a ≠ 0) :
    {p : AffineHeightOnePrime R | a ∈ p.1.asIdeal}.Finite := by
  have hinj : Function.Injective (fun p : AffineHeightOnePrime R => p.1.asIdeal) := by
    intro p q h
    exact Subtype.ext (PrimeSpectrum.ext h)
  have hfinite :
      {p : AffineHeightOnePrime R |
        p.1.asIdeal ∈ (Ideal.span {a}).minimalPrimes}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})).preimage
      (Set.injOn_of_injective hinj)
  exact hfinite.subset (fun p hp =>
    mem_minimalPrimes_span_singleton_of_height_one p.2 ha hp)

end MinimalPrimes

section NormalDomain

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Every actual height-one prime localization of a normal Noetherian
domain is a DVR. No global dimension-one assumption is made. -/
theorem heightOneLocalization_isDiscreteValuationRing (p : AffineHeightOnePrime R) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := by
  letI : IsNoetherianRing (Localization.AtPrime p.1.asIdeal) :=
    IsLocalization.isNoetherianRing p.1.asIdeal.primeCompl _ inferInstance
  letI : IsIntegrallyClosed (Localization.AtPrime p.1.asIdeal) :=
    isIntegrallyClosed_of_isLocalization _ p.1.asIdeal.primeCompl
      p.1.asIdeal.primeCompl_le_nonZeroDivisors
  apply KltDP.Geometry.isDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
  simpa only [p.2] using IsLocalization.AtPrime.ringKrullDim_eq_height
    p.1.asIdeal (Localization.AtPrime p.1.asIdeal)

variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical map from a height-one localization into the given
actual fraction field. -/
def heightOneFractionFieldAlgebra (p : AffineHeightOnePrime R) :
    Algebra (Localization.AtPrime p.1.asIdeal) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.AtPrime p.1.asIdeal) K p.1.asIdeal.primeCompl (nonZeroDivisors R)
    p.1.asIdeal.primeCompl_le_nonZeroDivisors

/-- Actual integer order at an affine height-one prime, with the DVR
property proved from normality and dimension. -/
def affinePrincipalOrder (p : AffineHeightOnePrime R) (f : Kˣ) : ℤ :=
  letI : IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) :=
    heightOneLocalization_isDiscreteValuationRing R p
  letI : Algebra (Localization.AtPrime p.1.asIdeal) K := heightOneFractionFieldAlgebra R K p
  letI : IsScalarTower R (Localization.AtPrime p.1.asIdeal) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime p.1.asIdeal) K p.1.asIdeal.primeCompl (nonZeroDivisors R)
      p.1.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing (Localization.AtPrime p.1.asIdeal) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      p.1.asIdeal.primeCompl (Localization.AtPrime p.1.asIdeal) K
  divisorOrder (Localization.AtPrime p.1.asIdeal) K f

/-- If a numerator and denominator are both outside the prime, their
fraction is an actual local unit and has order zero. -/
theorem affinePrincipalOrder_eq_zero_of_fraction_notMem
    (p : AffineHeightOnePrime R) (f : Kˣ) (a b : R)
    (hf : (f : K) = algebraMap R K a * (algebraMap R K b)⁻¹)
    (ha : a ∉ p.1.asIdeal) (hb : b ∉ p.1.asIdeal) :
    affinePrincipalOrder R K p f = 0 := by
  let S := Localization.AtPrime p.1.asIdeal
  letI : IsDiscreteValuationRing S := heightOneLocalization_isDiscreteValuationRing R p
  letI : Algebra S K := heightOneFractionFieldAlgebra R K p
  letI : IsScalarTower R S K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S K
      p.1.asIdeal.primeCompl (nonZeroDivisors R) p.1.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.1.asIdeal.primeCompl S K
  have hua : IsUnit (algebraMap R S a) :=
    IsLocalization.map_units S (⟨a, ha⟩ : p.1.asIdeal.primeCompl)
  have hub : IsUnit (algebraMap R S b) :=
    IsLocalization.map_units S (⟨b, hb⟩ : p.1.asIdeal.primeCompl)
  obtain ⟨ua, hua⟩ := hua
  obtain ⟨ub, hub⟩ := hub
  have hmap : Units.map (algebraMap S K) (ua * ub⁻¹) = f := by
    apply Units.ext
    calc
      ((Units.map (algebraMap S K) (ua * ub⁻¹) : Kˣ) : K) =
          algebraMap S K (ua : S) * (algebraMap S K (ub : S))⁻¹ := by
        change algebraMap S K ((ua : S) * ((ub⁻¹ : Sˣ) : S)) = _
        rw [map_mul, map_units_inv]
      _ = algebraMap R K a * (algebraMap R K b)⁻¹ := by
        rw [hua, hub, ← IsScalarTower.algebraMap_apply R S K,
          ← IsScalarTower.algebraMap_apply R S K]
      _ = (f : K) := hf.symm
  change divisorOrder S K f = 0
  rw [← hmap]
  exact divisorOrder_map_unit S K (ua * ub⁻¹)

/-- Explicit numerator/denominator bound on the support of the actual
affine principal orders. -/
theorem affinePrincipalOrder_support_subset
    (f : Kˣ) (a b : R)
    (hf : (f : K) = algebraMap R K a * (algebraMap R K b)⁻¹) :
    Function.support (fun p : AffineHeightOnePrime R => affinePrincipalOrder R K p f) ⊆
      {p | a ∈ p.1.asIdeal} ∪ {p | b ∈ p.1.asIdeal} := by
  intro p hp
  by_contra h
  have hnot : a ∉ p.1.asIdeal ∧ b ∉ p.1.asIdeal := by
    simpa only [Set.mem_union, Set.mem_setOf_eq, not_or] using h
  exact hp (affinePrincipalOrder_eq_zero_of_fraction_notMem R K p f a b hf hnot.1 hnot.2)

/-- The actual height-one-prime order function of a nonzero fraction has
finite support over a Noetherian normal domain of any dimension. -/
theorem affinePrincipalOrder_finite_support (f : Kˣ) :
    (Function.support (fun p : AffineHeightOnePrime R => affinePrincipalOrder R K p f)).Finite := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (f : K)
  have hinj := IsFractionRing.injective R K
  have hbne : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hbmap : algebraMap R K (b : R) ≠ 0 := by
    intro h
    exact hbne (hinj (by simpa only [map_zero] using h))
  have hane : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hab
    exact (mul_ne_zero f.ne_zero hbmap) hab
  have hfrac : (f : K) = algebraMap R K a * (algebraMap R K (b : R))⁻¹ := by
    rw [← hab, mul_inv_cancel_right₀ hbmap]
  exact ((finite_heightOnePrimes_containing a hane).union
    (finite_heightOnePrimes_containing (b : R) hbne)).subset
      (affinePrincipalOrder_support_subset R K f a (b : R) hfrac)

/-- The actual principal divisor on the affine height-one-prime carrier.
Its finite-support witness is the preceding theorem. -/
def affinePrincipalDivisor (f : Kˣ) : AffineHeightOnePrime R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => affinePrincipalOrder R K p f)
    (affinePrincipalOrder_finite_support R K f)

@[simp]
theorem affinePrincipalDivisor_apply (f : Kˣ) (p : AffineHeightOnePrime R) :
    affinePrincipalDivisor R K f p = affinePrincipalOrder R K p f := rfl

end NormalDomain

end KltDP.RingTheory
