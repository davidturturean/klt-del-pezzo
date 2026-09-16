import KltDP.Geometry.DivisorOrderTransport
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Height-one coordinates under an actual prime localization

A height-one prime contained in `P` extends to a height-one prime of an
actual localization at `P`. Extension is injective on these primes, and
the normalized orders in a common fraction field agree. The base ring
may have arbitrary dimension and need not be factorial.

The proof uses the pinned Mathlib prime-ideal localization correspondence,
`IsLocalization.height_comap`, and localization of a localization
(Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, Apache-2.0).
The final order equality uses the already proved normalization transport
for actual DVRs; no equality of valuations is an input.
-/

noncomputable section

universe u v w

namespace KltDP.RingTheory

variable (A : Type u) [CommRing A] (P : Ideal A) [P.IsPrime]
variable (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S P]

/-- Extend a prime below `P` along the actual localization map. -/
def primeAtPrime (p : PrimeSpectrum A) (hp : p.asIdeal ≤ P) : PrimeSpectrum S :=
  ⟨p.asIdeal.map (algebraMap A S),
    IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl S p.asIdeal p.isPrime
      (Set.disjoint_left.mpr (fun _ ha hb => ha (hp hb)))⟩

/-- Contracting the extended prime recovers the original prime. -/
theorem primeAtPrime_comap (p : PrimeSpectrum A) (hp : p.asIdeal ≤ P) :
    (primeAtPrime A P S p hp).asIdeal.comap (algebraMap A S) = p.asIdeal :=
  IsLocalization.comap_map_of_isPrime_disjoint P.primeCompl S p.asIdeal p.isPrime
    (Set.disjoint_left.mpr (fun _ ha hb => ha (hp hb)))

/-- Localization preserves the actual height of each prime below `P`. -/
theorem primeAtPrime_height (p : PrimeSpectrum A) (hp : p.asIdeal ≤ P) :
    (primeAtPrime A P S p hp).asIdeal.height = p.asIdeal.height := by
  rw [← IsLocalization.height_comap P.primeCompl,
    primeAtPrime_comap A P S p hp]

/-- A height-one prime below `P`, viewed in the actual localized ring. -/
def affineHeightOnePrimeAtPrime (p : AffineHeightOnePrime A) (hp : p.1.asIdeal ≤ P) :
    AffineHeightOnePrime S :=
  ⟨primeAtPrime A P S p.1 hp, (primeAtPrime_height A P S p.1 hp).trans p.2⟩

theorem affineHeightOnePrimeAtPrime_comap
    (p : AffineHeightOnePrime A) (hp : p.1.asIdeal ≤ P) :
    (affineHeightOnePrimeAtPrime A P S p hp).1.asIdeal.comap (algebraMap A S) =
      p.1.asIdeal :=
  primeAtPrime_comap A P S p.1 hp

/-- Distinct height-one primes below `P` remain distinct after localization. -/
theorem affineHeightOnePrimeAtPrime_injective :
    Function.Injective (fun p : {p : AffineHeightOnePrime A // p.1.asIdeal ≤ P} =>
      affineHeightOnePrimeAtPrime A P S p.1 p.2) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  apply PrimeSpectrum.ext
  have hc := congrArg
    (fun r : AffineHeightOnePrime S => r.1.asIdeal.comap (algebraMap A S)) h
  simpa only [affineHeightOnePrimeAtPrime_comap] using hc

section Orders

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S]
variable (K : Type w) [Field K]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra S K] [IsFractionRing S K] [IsScalarTower A S K]

/-- Extending a height-one prime through an actual prime localization
preserves its integer order in the original common fraction field. -/
theorem affinePrincipalOrder_atPrime
    (p : AffineHeightOnePrime A) (hp : p.1.asIdeal ≤ P) (f : Kˣ) :
    affinePrincipalOrder S K (affineHeightOnePrimeAtPrime A P S p hp) f =
      affinePrincipalOrder A K p f := by
  let q : AffineHeightOnePrime S := affineHeightOnePrimeAtPrime A P S p hp
  let T := Localization.AtPrime q.1.asIdeal
  let B := Localization.AtPrime p.1.asIdeal
  letI : IsDiscreteValuationRing T := heightOneLocalization_isDiscreteValuationRing S q
  letI : IsDiscreteValuationRing B := heightOneLocalization_isDiscreteValuationRing A p
  letI : Algebra T K := heightOneFractionFieldAlgebra S K q
  letI : IsScalarTower S T K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T K
      q.1.asIdeal.primeCompl (nonZeroDivisors S) q.1.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing T K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.1.asIdeal.primeCompl T K
  letI : IsScalarTower A S T := inferInstance
  letI : IsScalarTower A T K := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A K a = algebraMap T K (algebraMap S T (algebraMap A S a))
    rw [← IsScalarTower.algebraMap_apply S T K,
      ← IsScalarTower.algebraMap_apply A S K])
  letI : IsLocalization.AtPrime T p.1.asIdeal := by
    have hlocal := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      P.primeCompl T q.1.asIdeal
    have hcomap : q.1.asIdeal.comap (algebraMap A S) = p.1.asIdeal :=
      affineHeightOnePrimeAtPrime_comap A P S p hp
    have hcompl : (q.1.asIdeal.comap (algebraMap A S)).primeCompl = p.1.asIdeal.primeCompl := by
      ext a
      change a ∉ q.1.asIdeal.comap (algebraMap A S) ↔ a ∉ p.1.asIdeal
      rw [hcomap]
    change IsLocalization (q.1.asIdeal.comap (algebraMap A S)).primeCompl T at hlocal
    change IsLocalization p.1.asIdeal.primeCompl T
    rw [← hcompl]
    exact hlocal
  letI : Algebra B K := heightOneFractionFieldAlgebra A K p
  letI : IsScalarTower A B K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B K
      p.1.asIdeal.primeCompl (nonZeroDivisors A) p.1.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.1.asIdeal.primeCompl B K
  change divisorOrder T K f = divisorOrder B K f
  exact divisorOrder_eq_of_isLocalization A p.1.asIdeal.primeCompl T B K f

end Orders

end KltDP.RingTheory
