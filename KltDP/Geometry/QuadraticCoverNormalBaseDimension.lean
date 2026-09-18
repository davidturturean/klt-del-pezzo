import KltDP.Geometry.OriginalQuadraticSurjective
import KltDP.Compatibility.FiniteTypeMaximalHeight

/-!
# Dimension of an actual integral quadratic algebra over a normal base

The accepted integral incomparability theorem gives the upper bound.
An actual maximal base prime has full height by the accepted finite-type
dimension theorem. Lying over supplies a prime of the original quadratic
algebra above it, and the accepted normal-base going-down theorem gives
the lower bound at that same prime. No dimension or valuation of the
quadratic algebra is supplied.

This is an algebraic adapter. Integrality of the original geometric cover
is established from its actual nonempty reduced Cartier branch in the
separate geometric producer.
-/

noncomputable section
universe u

namespace KltDP.Geometry.QuadraticCover

open KltDP.Compatibility

variable (k R : Type u) [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    [IsIntegrallyClosed R]

include k

/-- The actual integral quadratic algebra has the same finite dimension as its normal base. -/
theorem ringKrullDim_eq_of_normal (s : R) [IsDomain (CoverAlgebra s)]
    (n : ℕ) (hdim : ringKrullDim R = (n : WithBot ℕ∞)) :
    ringKrullDim (CoverAlgebra s) = (n : WithBot ℕ∞) := by
  letI : Module.Finite R (CoverAlgebra s) := finite s
  letI : FaithfulSMul R (CoverAlgebra s) :=
    (faithfulSMul_iff_algebraMap_injective R (CoverAlgebra s)).mpr (algebraMap_injective s)
  letI : Algebra.HasGoingDown R (CoverAlgebra s) := normal_hasGoingDown
  have hint : (algebraMap R (CoverAlgebra s)).IsIntegral := Algebra.IsIntegral.isIntegral
  apply le_antisymm ((ringKrullDim_le_of_integral _ hint).trans hdim.le)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  letI : M.IsMaximal := hM
  have hn : (n : ℕ∞) ≤ M.primeHeight := by
    apply WithBot.coe_le_coe.mp
    simpa only [Ideal.height_eq_primeHeight] using
      ((maximal_height_eq_ringKrullDim k R M).trans hdim).ge
  obtain ⟨Q, hQ⟩ := hint.specComap_surjective (algebraMap_injective s)
    (⟨M, inferInstance⟩ : PrimeSpectrum R)
  letI : Q.asIdeal.IsPrime := Q.isPrime
  have hunder : Q.asIdeal.under R = M := congrArg PrimeSpectrum.asIdeal hQ
  have hQheight : (n : ℕ∞) ≤ Q.asIdeal.primeHeight :=
    nat_le_primeHeight_of_hasGoingDown R (CoverAlgebra s) n Q.asIdeal (by
      simpa only [hunder] using hn)
  exact (WithBot.coe_le_coe.mpr hQheight).trans Ideal.primeHeight_le_ringKrullDim

end KltDP.Geometry.QuadraticCover

#print axioms KltDP.Geometry.QuadraticCover.ringKrullDim_eq_of_normal
