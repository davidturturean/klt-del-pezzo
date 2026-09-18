import KltDP.Examples.FrobeniusDiscrepancyBounds
import KltDP.Examples.FrobeniusStrictTransformSmoothCurves

/-!
# Smooth, disjoint support of the actual candidate discrepancy

The original graph and strict special fibres are smooth over the original
field. The actual prime-curve schemes inherit this through their proved
inclusion lifts. The candidate's proved support inclusion therefore gives
smooth components, and the original incidence equations give disjointness.
No SNC property or replacement component is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open PrimeCurveInclusionLift FrobeniusStrictTransformSmoothCurves
open FrobeniusMultiCentreSurface FrobeniusMultiCentreGraphFiber
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreGraphProjectiveLine FrobeniusMultiCentreFiberProjectiveLine
open FrobeniusMultiCentreCanonicalWeilRepresentatives FrobeniusGraphFiberDisjointSPn

private theorem smooth_prime_of_native {k : Type u} [Field k]
    {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
    {T : Scheme.{u}} (ι : T ⟶ X.toScheme) [IsClosedImmersion ι] [IsReduced T]
    (hC : (C : Set X.toScheme) = Set.range ι.base)
    (hι : IsSmooth (ι ≫ X.structureMorphism)) : IsSmooth C.toSpec :=
  isSmooth_toSpec_of_iso C (inv (lift C ι hC)) (ι ≫ X.structureMorphism) hι (by
    rw [← Category.assoc, ← inclusion_eq_inv_lift C ι hC]
    rfl)

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Smoothness of the original graph prime, with its original structure map. -/
theorem graphPrimeCurve_isSmooth :
    IsSmooth (graphPrimeCurve q n a ha hproj).toSpec := by
  letI := graphStrict_isReduced (q + 1) n a
  exact smooth_prime_of_native (graphPrimeCurve q n a ha hproj)
    (graphStrictι (q + 1) n a) rfl (globalGraph_isSmooth (q + 1) n a)

/-- Smoothness of each original strict special-fibre prime. -/
theorem fiberPrimeCurve_isSmooth (i : Fin n) :
    IsSmooth (fiberPrimeCurve q n a ha hproj i).toSpec := by
  letI := fiberStrict_isReduced (q + 1) n a i
  exact smooth_prime_of_native (fiberPrimeCurve q n a ha hproj i)
    (fiberStrictι (q + 1) n a i) rfl (globalFiber_isSmooth q n a ha i)

/-- Every prime with a nonzero coefficient in the actual candidate is smooth. -/
theorem candidate_support_isSmooth (C : (sourceSurface q n a ha hproj).PrimeCurve)
    (hC : C ∈ (candidate q n a ha hproj).support) : IsSmooth C.toSpec := by
  rcases candidate_support_subset q n a ha hproj hC with rfl | ⟨i, rfl⟩
  · exact graphPrimeCurve_isSmooth q n a ha hproj
  · exact fiberPrimeCurve_isSmooth q n a ha hproj i

/-- Distinct actual candidate-support primes are disjoint on the original surface. -/
theorem candidate_support_pairwise_disjoint :
    ((candidate q n a ha hproj).support :
      Set (sourceSurface q n a ha hproj).PrimeCurve).Pairwise
      (fun C E => Disjoint (C : Set (sourceSurface q n a ha hproj).toScheme)
        (E : Set (sourceSurface q n a ha hproj).toScheme)) := by
  intro C hC E hE hCE
  rcases candidate_support_subset q n a ha hproj hC with rfl | ⟨i, rfl⟩
  · rcases candidate_support_subset q n a ha hproj hE with rfl | ⟨j, rfl⟩
    · exact (hCE rfl).elim
    · simpa only [coe_graphPrimeCurve, coe_fiberPrimeCurve] using
        graphStrict_fiberStrict_disjoint' q n a j
  · rcases candidate_support_subset q n a ha hproj hE with rfl | ⟨j, rfl⟩
    · simpa only [coe_graphPrimeCurve, coe_fiberPrimeCurve] using
        (graphStrict_fiberStrict_disjoint' q n a i).symm
    · simpa only [coe_fiberPrimeCurve] using
        fiberStrict_disjoint (q + 1) n a ha (fun h => hCE (congrArg _ h))

/-- At every original point at most one candidate-support prime passes through it. -/
theorem candidate_support_unique_at_point
    (C E : (sourceSurface q n a ha hproj).PrimeCurve)
    (hC : C ∈ (candidate q n a ha hproj).support)
    (hE : E ∈ (candidate q n a ha hproj).support)
    (x : (sourceSurface q n a ha hproj).toScheme) (hxC : x ∈ C) (hxE : x ∈ E) :
    C = E := by
  by_contra hCE
  exact Set.disjoint_left.mp
    (candidate_support_pairwise_disjoint q n a ha hproj hC hE hCE) hxC hxE

end KltDP.Examples.FrobeniusDiscrepancyBounds
