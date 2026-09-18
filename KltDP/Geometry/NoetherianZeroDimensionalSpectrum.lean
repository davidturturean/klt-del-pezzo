import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Topology.Separation.Connected

/-!
# Connected reduced rings with Noetherian zero-dimensional spectra

The existing finite irreducible-component theorem applies to the topology
of the original spectrum. In dimension zero those components are exactly
the original prime ideals. The spectrum is therefore finite and discrete;
connectedness leaves one maximal ideal, and reducedness makes the ring a field.
-/

noncomputable section

open TopologicalSpace

universe u

namespace KltDP.Geometry.NoetherianZeroDimensionalSpectrum

variable (R : Type u) [CommRing R] [NoetherianSpace (PrimeSpectrum R)]
  [Ring.KrullDimLE 0 R]

/-- Noetherianity of the spectrum, rather than of the ring, suffices in dimension zero. -/
theorem finite_primeSpectrum : Finite (PrimeSpectrum R) := by
  have hmin : (minimalPrimes R).Finite :=
    (minimalPrimes.equivIrreducibleComponents R).set_finite_iff.mpr
      NoetherianSpace.finite_irreducibleComponents
  have hprime : {I : Ideal R | I.IsPrime}.Finite := by
    rwa [Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime] at hmin
  letI : Finite {I : Ideal R // I.IsPrime} := hprime.to_subtype
  exact Finite.of_equiv _ (PrimeSpectrum.equivSubtype R).symm

/-- The original spectrum is discrete by the pinned finite-spectrum criterion. -/
theorem discrete_primeSpectrum : DiscreteTopology (PrimeSpectrum R) :=
  PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr
    ⟨finite_primeSpectrum R, inferInstance⟩

/-- A reduced nonzero ring with connected Noetherian zero-dimensional spectrum is a field. -/
theorem isField_of_reduced_connected [Nontrivial R] [_root_.IsReduced R]
    [PreconnectedSpace (PrimeSpectrum R)] : IsField R := by
  letI := discrete_primeSpectrum R
  letI : Subsingleton (PrimeSpectrum R) := PreconnectedSpace.trivial_of_discrete
  let p : PrimeSpectrum R := Classical.choice inferInstance
  letI : IsLocalRing R := IsLocalRing.of_unique_max_ideal
    ⟨p.asIdeal, p.isPrime.isMaximal', fun I hI =>
      congrArg PrimeSpectrum.asIdeal
        (Subsingleton.elim (⟨I, hI.isPrime⟩ : PrimeSpectrum R) p)⟩
  exact Ring.KrullDimLE.isField_of_isReduced

end KltDP.Geometry.NoetherianZeroDimensionalSpectrum
