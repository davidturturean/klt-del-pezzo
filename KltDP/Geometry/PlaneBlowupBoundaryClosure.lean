import KltDP.Examples.FrobeniusBlowupIncidence

/-!
# The residual coordinate branch in the original plane blowup chart

The already constructed residual affine line has the original kernel
`span {chartW}`. Its generic point is outside the exceptional equation,
because the original line map sends `chartU` to the polynomial variable.
Consequently the punctured residual branch is dense in that whole branch.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.PlaneBlowupBoundaryClosure

open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupIncidence

universe u

variable (k : Type u) [Field k]

/-- The strict residual coordinate branch is the closure of its complement
of the original exceptional equation, in the original Rees chart itself. -/
theorem residual_closure :
    closure (PrimeSpectrum.zeroLocus {chartW (k := k)} \
      PrimeSpectrum.zeroLocus {chartU (k := k)}) =
      PrimeSpectrum.zeroLocus {chartW (k := k)} := by
  let η : PrimeSpectrum (reesChartRing k) :=
    ⟨RingHom.ker (fiberChartMap (k := k)), RingHom.ker_isPrime _⟩
  have hη : η ∈ PrimeSpectrum.zeroLocus {chartW (k := k)} \
      PrimeSpectrum.zeroLocus {chartU (k := k)} := by
    constructor
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      change fiberChartMap (chartW (k := k)) = 0
      exact fiberChartMap_w
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      change ¬ fiberChartMap (chartU (k := k)) = 0
      rw [fiberChartMap_u]
      exact Polynomial.X_ne_zero
  have hclosure : closure ({η} : Set (PrimeSpectrum (reesChartRing k))) =
      PrimeSpectrum.zeroLocus {chartW (k := k)} := by
    rw [PrimeSpectrum.closure_singleton]
    change PrimeSpectrum.zeroLocus
      (RingHom.ker (fiberChartMap (k := k)) : Set (reesChartRing k)) = _
    rw [fiberChartMap_ker, PrimeSpectrum.zeroLocus_span]
  apply Set.Subset.antisymm
  · exact closure_minimal Set.diff_subset (PrimeSpectrum.isClosed_zeroLocus _)
  · exact hclosure.symm.le.trans
      (closure_mono (Set.singleton_subset_iff.mpr hη))

end KltDP.Geometry.PlaneBlowupBoundaryClosure
