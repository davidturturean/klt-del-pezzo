import KltDP.Geometry.PrimeCurveSmoothAdjunction
import KltDP.Geometry.SmoothCanonicalCartierPicard
import KltDP.Geometry.CurveCanonicalSchemeIso

/-!
# The numerical adjunction consequence for an original smooth prime curve

The original smooth adjunction isomorphism supplies the formerly explicit
adjunction premise. The actual canonical Cartier representative therefore has
the canonical restriction degree. The rational-curve specialization uses an
original scheme isomorphism over the field, not an assumed degree formula.
This file depends on the full smooth adjunction producer, still staged when
this consumer was written; it asserts no singular-curve dualizing result.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SmoothPrimeCurveAdjunctionDegree

open AdjunctionSeed SmoothSurfaceKaehlerAtlas
open SmoothCanonicalCartierRepresentative SmoothCanonicalCartierPicard

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C : X.PrimeCurve) [IsSmoothOfRelativeDimension 1 C.toSpec]

/-- The original smooth canonical line satisfies adjunction on the original smooth prime curve. -/
theorem adjunction_degree :
    canonicalRestrictionDegree X (canonicalSheafOfSmoothSurface X.structureMorphism) C +
        C.selfIntersectionNumber hregular = CurveCanonical.canonicalDegree C.toSpec :=
  AdjunctionSeed.adjunction_degree X hregular
    (canonicalSheafOfSmoothSurface X.structureMorphism) C
    (PrimeCurveSmoothAdjunction.adjunctionIso X hregular C)

omit hregular in
/-- The chosen canonical Cartier representative has the degree of the original canonical line. -/
theorem canonical_intersection :
    C.intersectionNumber (cartierRepresentative X.structureMorphism) =
      canonicalRestrictionDegree X (canonicalSheafOfSmoothSurface X.structureMorphism) C := by
  rw [← C.picardRestrictionDegreeHom_cartierPicardHom, cartierPicardHom_representative]
  rfl

/-- Adjunction for the actual sum of the canonical Cartier divisor and the prime-curve divisor. -/
theorem canonical_add_curve_intersection :
    C.intersectionNumber
        (cartierRepresentative X.structureMorphism + X.primeCurveCartier hregular C) =
      CurveCanonical.canonicalDegree C.toSpec := by
  rw [C.intersectionNumber_add, canonical_intersection]
  exact adjunction_degree X hregular C

/-- On an actual rational smooth prime curve, the original adjoint Cartier divisor has degree -2. -/
theorem canonical_add_rational_curve_intersection
    (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    C.intersectionNumber
        (cartierRepresentative X.structureMorphism + X.primeCurveCartier hregular C) = -2 :=
  (canonical_add_curve_intersection X hregular C).trans
    (CurveCanonical.canonicalDegree_eq_neg_two_of_projectiveLineIso C.toSpec e he)

/-- The actual anticanonical degree of that rational curve is its self-intersection plus two. -/
theorem antiCanonical_rational_curve_intersection
    (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    C.intersectionNumber (-cartierRepresentative X.structureMorphism) =
      C.selfIntersectionNumber hregular + 2 := by
  rw [C.intersectionNumber_neg, canonical_intersection]
  have h := adjunction_degree X hregular C
  rw [CurveCanonical.canonicalDegree_eq_neg_two_of_projectiveLineIso C.toSpec e he] at h
  omega

end KltDP.Geometry.SmoothPrimeCurveAdjunctionDegree
