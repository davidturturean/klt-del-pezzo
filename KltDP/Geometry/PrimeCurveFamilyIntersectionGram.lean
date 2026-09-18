import KltDP.Geometry.DisjointNegativeCurvesRank
import KltDP.LinearAlgebra.NegativeGramDimension

/-!
# Actual prime intersections determine the numerical negative Gram matrix

Equality of the original Cartier intersection numbers for two actual
prime families gives equality of the actual numerical-class Gram matrices,
using the existing numerical pairing comparison. This transports the
proved original Gram through the unchanged contraction map's image family.
-/

noncomputable section
open AlgebraicGeometry
universe u v

namespace KltDP.Geometry.PrimeCurveFamilyIntersectionGram

open NormalProjectiveSurface DisjointNegativeCurvesRank
open KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S T : NormalProjectiveSurface k)
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (hT : ∀ x : T.Point, RegularPoint T.toScheme x)
    {I : Type v} (C : I → S.PrimeCurve) (D : I → T.PrimeCurve)

/-- Equal actual prime intersections give equal actual numerical negative Gram matrices. -/
theorem negativeGram_eq_of_intersections
    (h : ∀ i j, (D i).intersectionNumber (T.primeCurveCartier hT (D j)) =
      (C i).intersectionNumber (S.primeCurveCartier hS (C j))) :
    negativeGram (T.numericalIntersectionBilinForm hT) (fun i => curveClass T hT (D i)) =
      negativeGram (S.numericalIntersectionBilinForm hS) (fun i => curveClass S hS (C i)) := by
  ext i j
  change -T.numericalIntersectionBilinForm hT (curveClass T hT (D i)) (curveClass T hT (D j)) =
    -S.numericalIntersectionBilinForm hS (curveClass S hS (C i)) (curveClass S hS (C j))
  rw [curveClass_pairing, curveClass_pairing,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber T hT (D i) (D j),
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber S hS (C i) (C j)]
  exact congrArg (fun z : ℤ => -(z : ℚ)) (h i j)

end KltDP.Geometry.PrimeCurveFamilyIntersectionGram

#print axioms KltDP.Geometry.PrimeCurveFamilyIntersectionGram.negativeGram_eq_of_intersections
