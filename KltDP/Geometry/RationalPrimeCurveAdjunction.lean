import KltDP.Geometry.SmoothPrimeCurveAdjunctionDegree
import KltDP.Geometry.RationalCurveSmooth
import KltDP.Geometry.SmoothSurfaceRegularity
import KltDP.Geometry.Positivity

/-!
# Actual rational prime curves and the canonical divisor of a smooth surface

The original surface's smoothness supplies its stalk regularity. The actual
projective-line isomorphism supplies the curve's smoothness and canonical
degree. The adjunction consequences thus require neither as an additional
numerical or sheaf-isomorphism premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.RationalPrimeCurveAdjunction

open SmoothCanonicalCartierRepresentative

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance smoothSurface : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

variable (C : X.PrimeCurve) (e : C.toScheme ≅ projectiveSpace k 1)
  (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)

include e he

/-- The original canonical plus curve Cartier divisor has degree minus two. -/
theorem canonical_add_curve :
    C.intersectionNumber (cartierRepresentative X.structureMorphism +
      X.primeCurveCartier X.regularPoints_of_isSmooth C) = -2 := by
  letI := smoothOne_of_projectiveLineIso C.toSpec e he
  exact SmoothPrimeCurveAdjunctionDegree.canonical_add_rational_curve_intersection
    X X.regularPoints_of_isSmooth C e he

/-- The original anticanonical degree is the self-intersection plus two. -/
theorem antiCanonical_degree :
    C.intersectionNumber (-cartierRepresentative X.structureMorphism) =
      C.selfIntersectionNumber X.regularPoints_of_isSmooth + 2 := by
  letI := smoothOne_of_projectiveLineIso C.toSpec e he
  exact SmoothPrimeCurveAdjunctionDegree.antiCanonical_rational_curve_intersection
    X X.regularPoints_of_isSmooth C e he

/-- Every actual rational minus-two prime curve is orthogonal to that anticanonical divisor. -/
theorem antiCanonical_degree_of_minus_two
    (hC : C.selfIntersectionNumber X.regularPoints_of_isSmooth = -2) :
    C.intersectionNumber (-cartierRepresentative X.structureMorphism) = 0 := by
  rw [antiCanonical_degree X C e he, hC]
  norm_num

/-- A nef actual anticanonical divisor bounds the self-intersection of every actual rational curve. -/
theorem selfIntersection_ge_neg_two
    (hnef : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme (-cartierRepresentative X.structureMorphism))) :
    -2 ≤ C.selfIntersectionNumber X.regularPoints_of_isSmooth := by
  have hc := (Positivity.isNef_iff_forall_primeCurve X _).mp hnef C
  change 0 ≤ C.intersectionNumber (-cartierRepresentative X.structureMorphism) at hc
  rw [antiCanonical_degree X C e he] at hc
  omega

/-- Under nef anticanonical degree, an actual negative rational prime curve has square -1 or -2. -/
theorem negative_selfIntersection
    (hnef : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme (-cartierRepresentative X.structureMorphism)))
    (hneg : C.selfIntersectionNumber X.regularPoints_of_isSmooth < 0) :
    C.selfIntersectionNumber X.regularPoints_of_isSmooth = -1 ∨
      C.selfIntersectionNumber X.regularPoints_of_isSmooth = -2 := by
  have hbound := selfIntersection_ge_neg_two X C e he hnef
  omega

end KltDP.Geometry.RationalPrimeCurveAdjunction
