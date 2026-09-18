import KltDP.Geometry.AffineBlowupRegularPairResidual
import KltDP.Geometry.RegularLocalParameterIdeal
import KltDP.Geometry.AffineBlowupBoundaryChartSupports

/-!
# The actual strict residual branch for given regular surface parameters

The given original maximal-ideal generators supply both regular-pair
conditions and the original residual prime ideal. Its generic point is
outside the exceptional equation. Thus the residual fraction cuts out
the actual strict-support closure in the original Rees chart. No etale
coordinate choice, density, prime-branch or strict-transform premise is
supplied to these theorems.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace KltDP.Geometry.AffineBlowupRegularPairChart

open AffineBlowup

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable (I : Ideal R) (a b : I)
variable (hR : RegularLocal R) (hdim : ringKrullDim R = 2)
variable (hI : I = Ideal.span {(a : R), (b : R)}) (hmax : I = maximalIdeal R)

include hR hdim hI hmax in
/-- The actual residual fraction ideal is prime for the given original
surface parameters. Its reducedness is consequently derived. -/
theorem fraction_ideal_isPrime_of_surface_parameters :
    (Ideal.span {chartFraction I a b}).IsPrime := by
  have hspan := hI.symm.trans hmax
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim (a : R) (b : R) hspan
  letI : (Ideal.span {(b : R)}).IsPrime :=
    RegularLocalTwoParameters.span_second_isPrime hR hdim (a : R) (b : R) hspan
  exact residualIdeal_isPrime I a b hpair.1 hpair.2 hI

include hR hdim hI hmax in
theorem fraction_closure_of_surface_parameters :
    closure (PrimeSpectrum.zeroLocus {chartFraction I a b} \
      PrimeSpectrum.zeroLocus {chartBaseMap I a (a : R)}) =
      PrimeSpectrum.zeroLocus {chartFraction I a b} := by
  have hspan := hI.symm.trans hmax
  have hpair := RegularLocalTwoParameters.regular_pair hR hdim (a : R) (b : R) hspan
  have hab : (a : R) ∉ Ideal.span {(b : R)} :=
    RegularLocalTwoParameters.second_not_mem_first hR hdim (b : R) (a : R)
      (Ideal.span_pair_comm.trans hspan)
  let η : PrimeSpectrum (chartRing I a) :=
    ⟨Ideal.span {chartFraction I a b},
      fraction_ideal_isPrime_of_surface_parameters I a b hR hdim hI hmax⟩
  have hη : η ∈ PrimeSpectrum.zeroLocus {chartFraction I a b} \
      PrimeSpectrum.zeroLocus {chartBaseMap I a (a : R)} := by
    constructor
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact Ideal.mem_span_singleton_self _
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact parameter_not_mem_residual I a b hpair.1 hpair.2 hI hab
  have hclosure : closure ({η} : Set (PrimeSpectrum (chartRing I a))) =
      PrimeSpectrum.zeroLocus {chartFraction I a b} := by
    rw [PrimeSpectrum.closure_singleton]
    change PrimeSpectrum.zeroLocus (Ideal.span {chartFraction I a b} : Set (chartRing I a)) = _
    exact PrimeSpectrum.zeroLocus_span _
  apply Set.Subset.antisymm
  · exact closure_minimal Set.diff_subset (PrimeSpectrum.isClosed_zeroLocus _)
  · exact hclosure.symm.le.trans (closure_mono (Set.singleton_subset_iff.mpr hη))

include hR hdim hI hmax in
/-- The actual strict-support closure of the original second parameter
branch is the original residual fraction's prime zero locus. -/
theorem original_parameter_branch_closure :
    closure ((chartι I a ≫ toSpec I).base ⁻¹'
      (PrimeSpectrum.zeroLocus {(b : R)} \ PrimeSpectrum.zeroLocus (I : Set R))) =
      PrimeSpectrum.zeroLocus {chartFraction I a b} := by
  rw [chart_second_branch_off_center]
  exact fraction_closure_of_surface_parameters I a b hR hdim hI hmax

end KltDP.Geometry.AffineBlowupRegularPairChart
