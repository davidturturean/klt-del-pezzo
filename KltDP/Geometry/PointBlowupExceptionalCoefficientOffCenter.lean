import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.DominantCartierPullbackOffSupport
import KltDP.Geometry.DominantCartierPullbackFunctorial

/-!
# The original exceptional Cartier coefficient away from the centre

The divisor's actual ideal data is the original centre-fibre kernel.
The original closed fibre has exactly the inverse image of the closed
centre as its range. Therefore any prime whose generic point does not
map to the centre lies off that original support and has coefficient zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open PointBlowupGluing PointBlowupExceptionalCartier

/-- The actual exceptional Cartier divisor has zero coefficient at each
original source prime whose generic point does not map to the centre. -/
theorem exceptionalCartierDivisor_coefficient_eq_zero
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint ≠ j.base q) :
    letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
    (sourceSurface X j q hclosed).cartierToWeilHom
      (exceptionalCartierDivisor j q hclosed) C = 0 := by
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  have hoff : C.genericPoint ∉
      (effectiveCartierIdealDataOfRegularEquations (scheme j q hclosed)
        (exceptionalCartierDivisor j q hclosed)
        (exceptionalCartierDivisor_hasRegularEquations j q hclosed)).support := by
    rw [exceptionalCartierDivisor_idealData]
    change C.genericPoint ∉
      (((globalCenterFiberι j q hclosed).ker).support : Set (scheme j q hclosed))
    rw [Scheme.Hom.support_ker,
      (globalCenterFiberι j q hclosed).isClosedEmbedding.isClosed_range.closure_eq,
      range_globalCenterFiberι]
    exact hcenter
  have hz := DominantCartierPullback.coefficient_eq_zero_of_not_mem_support
    (S := sourceSurface X j q hclosed) (𝟙 (sourceSurface X j q hclosed).toScheme)
    (exceptionalCartierDivisor j q hclosed)
    (exceptionalCartierDivisor_hasRegularEquations j q hclosed) C hoff
  simpa only [DominantCartierPullback.pullbackHom_id, AddMonoidHom.id_apply] using hz

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk

#check @KltDP.Geometry.PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_zero
#print axioms KltDP.Geometry.PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_zero
