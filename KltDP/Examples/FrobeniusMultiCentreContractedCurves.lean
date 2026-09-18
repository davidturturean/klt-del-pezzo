import KltDP.Geometry.PrimeCurvePowerSystem
import KltDP.Examples.FrobeniusMultiCentreNullCurveClassification

/-!
# Curves contracted by an actual Frobenius M power-system map

For any actual generated positive power of the original M, the original
projective map is constant on exactly the graph, selected strict fibers,
and old exceptional prime curves. The positive power system is input data;
this theorem does not assert that M is semiample.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractedCurves

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open SemiampleProjectiveMap ProjectiveSpaceDegreeOneSheaf
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreNullCurveClassification

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
  (S : PowerSystem (contractingLine q n a ha hproj))

/-- The degree comparison is for the actual projective map and the
independently defined restriction degree on every original prime curve. -/
theorem pullback_degreeOne_degree
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve) :
    C.restrictionDegree
        (pullbackInvertibleSheaf
          (PowerSystem.toProjective (contractingLine q n a ha hproj)
            (multiStructure (q + 1) n a) S)
          (degreeOne k S.dimension)) =
      (S.exponent : ℤ) * C.restrictionDegree (contractingLine q n a ha hproj) :=
  PrimeCurvePowerSystem.pullback_degreeOne_degree
    (multiSurfaceSurface (q + 1) n a ha hproj) (contractingLine q n a ha hproj) S C

/-- Exactly the original M-null primes have constant restriction under
the actual map of this generated positive power of M. -/
theorem restriction_factors_iff (hn : 2 < n)
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve) :
    (∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k S.dimension,
      C.inclusion ≫
          PowerSystem.toProjective (contractingLine q n a ha hproj)
            (multiStructure (q + 1) n a) S = C.toSpec ≫ p ∧
        p ≫ projectiveSpaceToSpec k S.dimension = 𝟙 _) ↔
      C = graphPrimeCurve q n a ha hproj ∨
      (∃ i : Fin n, C = fiberPrimeCurve q n a ha hproj i) ∨
      ∃ (i : Fin n) (j : Fin q),
        C = exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj :=
  (PrimeCurvePowerSystem.factors_iff_restrictionDegree_zero
    (multiSurfaceSurface (q + 1) n a ha hproj)
    (contractingLine q n a ha hproj) S C).trans
      (restrictionDegree_eq_zero_iff q n a ha hproj hn C)

end KltDP.Examples.FrobeniusMultiCentreContractedCurves
