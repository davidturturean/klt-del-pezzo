import KltDP.Geometry.PrimeCurveFamilyIntersectionGram
import KltDP.Geometry.NullCurveIntersectionMatrix

/-!
# Recover the actual prime pairing from the complete rational matrix

The already defined matrix records the actual integer prime intersections.
Its equality therefore retains every integer intersection, and hence the
actual numerical negative Gram. This is the small adapter for the single
blowdown constructor's complete surviving matrix.
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
    (h : NullCurveIntersectionMatrix.intersectionMatrix T hT D =
      NullCurveIntersectionMatrix.intersectionMatrix S hS C)

include h

/-- Equality of the complete matrices gives equality of the original integer intersections. -/
theorem intersections_eq_of_matrix_eq (i j : I) :
    (D i).intersectionNumber (T.primeCurveCartier hT (D j)) =
      (C i).intersectionNumber (S.primeCurveCartier hS (C j)) := by
  have hij := congrFun (congrFun h i) j
  change (T.intersectionPairing hT (T.primeCurveCartier hT (D i))
      (T.primeCurveCartier hT (D j)) : ℚ) =
    (S.intersectionPairing hS (S.primeCurveCartier hS (C i))
      (S.primeCurveCartier hS (C j)) : ℚ) at hij
  rw [PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber T hT (D i) (D j),
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber S hS (C i) (C j)] at hij
  exact_mod_cast hij

/-- The same complete matrix also preserves the actual numerical negative Gram. -/
theorem negativeGram_eq_of_matrix_eq :
    negativeGram (T.numericalIntersectionBilinForm hT) (fun i => curveClass T hT (D i)) =
      negativeGram (S.numericalIntersectionBilinForm hS) (fun i => curveClass S hS (C i)) :=
  negativeGram_eq_of_intersections S T hS hT C D (intersections_eq_of_matrix_eq S T hS hT C D h)

end KltDP.Geometry.PrimeCurveFamilyIntersectionGram

#print axioms KltDP.Geometry.PrimeCurveFamilyIntersectionGram.negativeGram_eq_of_matrix_eq
