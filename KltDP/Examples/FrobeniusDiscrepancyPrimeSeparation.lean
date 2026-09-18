import KltDP.Examples.FrobeniusDiscrepancyCandidate
import KltDP.Examples.FrobeniusContractingBlockSupports

/-!
The actual graph, special-fibre and old-exceptional primes are distinct
because their original embedded supports satisfy the established incidence
theorems. No distinctness or coefficient hypothesis is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves FrobeniusMultiCentreExceptionalPrime
open FrobeniusMultiCentreExceptional FrobeniusMultiCentreGraphFiber
open FrobeniusMultiCentreGraphContacts FrobeniusMultiCentreFiberContacts
open FrobeniusGraphFiberDisjointSPn FrobeniusMultiCentreCanonicalWeilRepresentatives

private theorem prime_ne_of_disjoint {k : Type u} [Field k]
    {S : NormalProjectiveSurface k} (C D : S.PrimeCurve)
    (h : Disjoint (C : Set S.toScheme) (D : Set S.toScheme)) : C ≠ D := by
  intro hCD
  subst D
  exact Set.disjoint_left.mp h C.genericPoint_mem C.genericPoint_mem

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original graph prime is distinct from every original strict special fibre. -/
theorem graph_ne_fiber (i : Fin n) :
    graphPrimeCurve q n a ha hproj ≠ fiberPrimeCurve q n a ha hproj i := by
  apply prime_ne_of_disjoint
  simpa only [coe_graphPrimeCurve, coe_fiberPrimeCurve] using
    graphStrict_fiberStrict_disjoint' q n a i

/-- Distinct selected heights give distinct original strict-fibre primes. -/
theorem fiber_injective : Function.Injective (fiberPrimeCurve q n a ha hproj) := by
  intro i j hij
  by_contra hne
  have hd : Disjoint
      (fiberPrimeCurve q n a ha hproj i : Set (sourceSurface q n a ha hproj).toScheme)
      (fiberPrimeCurve q n a ha hproj j : Set (sourceSurface q n a ha hproj).toScheme) := by
    simpa only [coe_fiberPrimeCurve] using
      fiberStrict_disjoint (q + 1) n a ha hne
  exact prime_ne_of_disjoint _ _ hd hij

/-- No original old exceptional prime is the original graph prime. -/
theorem graph_ne_old (i : Fin n) (j : Fin q) :
    graphPrimeCurve q n a ha hproj ≠
      exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj := by
  apply prime_ne_of_disjoint
  simpa only [coe_graphPrimeCurve, coe_exceptionalPrimeCurveSPn, exceptionalSupport] using
    graphStrict_disjoint_exceptional_same q n a i j

/-- No original old exceptional prime is any original strict special fibre. -/
theorem fiber_ne_old (i : Fin n) (j : Fin q) (l : Fin n) :
    fiberPrimeCurve q n a ha hproj l ≠
      exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj := by
  apply prime_ne_of_disjoint
  have hd : Disjoint (Set.range (fiberStrictι (q + 1) n a l).base)
      (exceptionalSupport q n a i (.inl j)) := by
    by_cases hli : l = i
    · subst l
      exact fiberStrict_disjoint_exceptional_same q n a i j
    · exact fiberStrict_disjoint_exceptional q n a ha hli (.inl j)
  simpa only [coe_fiberPrimeCurve, coe_exceptionalPrimeCurveSPn, exceptionalSupport] using hd

end KltDP.Examples.FrobeniusDiscrepancyBounds
