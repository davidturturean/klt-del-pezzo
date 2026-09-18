import KltDP.Geometry.QuadraticRamificationCharts
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Original quadratic chart points on and off the root-zero locus

The actual quotient inclusion contains precisely the primes containing
the original root. Every other prime maps to the basic open of the
original branch coefficient, by the original identity t²=s.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.QuadraticCover

variable {R : Type u} [CommRing R]

/-- Vanishing of the original root is equivalent to lying in the actual root-zero image. -/
theorem root_mem_iff_mem_range_rootZeroι (s : R) (z : affineScheme s) :
    root s ∈ z.asIdeal ↔ z ∈ Set.range (rootZeroι s).base := by
  change root s ∈ z.asIdeal ↔ z ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (rootIdeal s)))
  rw [PrimeSpectrum.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  change root s ∈ z.asIdeal ↔ rootIdeal s ≤ z.asIdeal
  rw [rootIdeal, Ideal.span_le, Set.singleton_subset_iff]
  rfl

/-- Off the original root-zero locus, the same base point lies off the original branch equation. -/
theorem base_mem_basicOpen_of_root_not_mem (s : R) (z : affineScheme s)
    (hz : root s ∉ z.asIdeal) : (toBase s).base z ∈ PrimeSpectrum.basicOpen s := by
  change algebraMap R (CoverAlgebra s) s ∉ z.asIdeal
  intro h
  rw [← root_sq s, pow_two] at h
  exact hz ((z.isPrime.mem_or_mem h).elim id id)

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.root_mem_iff_mem_range_rootZeroι
#print axioms KltDP.Geometry.QuadraticCover.base_mem_basicOpen_of_root_not_mem
