import KltDP.Examples.FrobeniusMultiCentreCanonicalWeilRepresentatives

/-!
The explicit rational divisor uses the original strict graph and original
strict special-fibre prime divisors on the original Frobenius surface.
Its identification with the canonical discrepancy is a separate theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The candidate discrepancy, as an actual finite rational sum of original
prime curves, with no old-exceptional or replacement-curve term. -/
def candidate : (sourceSurface q n a ha hproj).RationalWeilDivisor :=
  let p : ℚ := ((q + 1 : ℕ) : ℚ)
  let r : ℚ := (n : ℚ) - 2
  let s : ℚ := p * r
  (-((s - 2) / s)) •
      rationalizeWeilDivisor (sourceSurface q n a ha hproj)
        (Finsupp.single (graphPrimeCurve q n a ha hproj) 1) -
    ((p - 2) / p) •
      rationalizeWeilDivisor (sourceSurface q n a ha hproj)
        (∑ i : Fin n, Finsupp.single (fiberPrimeCurve q n a ha hproj i) 1)

end KltDP.Examples.FrobeniusDiscrepancyBounds
