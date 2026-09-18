import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives
import KltDP.Examples.FrobeniusProjectivityProved

/-!
# The actual integral canonical Weil relation on the original source

Map the already proved source Picard identity through the original
Picard-to-Weil class homomorphism, using the actual representative formulas.
The result is an explicit divisor supported in the original canonical
representative, embedded graph and special fibres, and the original Cartier
representative of M. Its class is zero, with an actual function-field unit
as a principal-divisor witness. Projectivity is discharged by the existing
original projectivity theorem in the final endpoint.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRelation

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The explicit integer combination of actual original Weil divisors. -/
def canonicalRelationDivisor : (sourceSurface q n a ha hproj).WeilDivisor :=
  let p : ℤ := (q + 1 : ℕ)
  let r : ℤ := (n : ℤ) - 2
  let s : ℤ := p * r
  let d : ℤ := 2 - (p - 2) * r
  s • canonicalWeil q n a ha hproj +
    (s - 2) • Finsupp.single (graphPrimeCurve q n a ha hproj) 1 +
    (r * (p - 2)) •
      (∑ i : Fin n, Finsupp.single (fiberPrimeCurve q n a ha hproj i) 1) +
    d • contractingWeil q n a ha hproj

/-- The actual divisor combination has zero class; every term is identified
with its existing geometric representative before applying the source identity. -/
theorem canonicalRelationDivisor_class_eq_zero :
    (sourceSurface q n a ha hproj).weilClassMap
      (canonicalRelationDivisor q n a ha hproj) = 0 := by
  have h := congrArg (sourceSurface q n a ha hproj).picardToWeilClassHom
    (FrobeniusMultiCentreCanonicalIntegralRelation.canonical_integral_relation q n a ha)
  simp only [map_add, map_zsmul, map_sum, map_zero,
    canonical_picardToWeil q n a ha hproj,
    graph_picardToWeil q n a ha hproj,
    fiber_picardToWeil q n a ha hproj,
    contracting_picardToWeil q n a ha hproj] at h
  simpa only [canonicalRelationDivisor, map_add, map_zsmul, map_sum] using h

/-- An actual nonzero rational function witnesses the explicit source Weil relation. -/
theorem canonicalRelationDivisor_principal :
    ∃ f : (sourceSurface q n a ha hproj).toScheme.functionFieldˣ,
      canonicalRelationDivisor q n a ha hproj =
        (sourceSurface q n a ha hproj).principalDivisor f :=
  ((sourceSurface q n a ha hproj).weilClassMap_eq_zero_iff _).mp
    (canonicalRelationDivisor_class_eq_zero q n a ha hproj)

/-- The same actual divisor, with the original projectivity theorem supplied. -/
def originalCanonicalRelationDivisor :
    (sourceSurface q n a ha
      (FrobeniusProjectivityProved.originalMultiStructureProjective k (q + 1) n a)).WeilDivisor :=
  canonicalRelationDivisor q n a ha
    (FrobeniusProjectivityProved.originalMultiStructureProjective k (q + 1) n a)

/-- The explicit original Weil relation needs no projectivity or canonical-descent premise. -/
theorem originalCanonicalRelationDivisor_principal :
    ∃ f : (sourceSurface q n a ha
      (FrobeniusProjectivityProved.originalMultiStructureProjective k (q + 1) n a)).toScheme.functionFieldˣ,
      originalCanonicalRelationDivisor q n a ha =
        (sourceSurface q n a ha
          (FrobeniusProjectivityProved.originalMultiStructureProjective k (q + 1) n a)).principalDivisor
          f :=
  canonicalRelationDivisor_principal q n a ha
    (FrobeniusProjectivityProved.originalMultiStructureProjective k (q + 1) n a)

end KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRelation
