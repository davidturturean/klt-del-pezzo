import KltDP.Geometry.SurfaceNakaiMoishezonProved
import KltDP.Geometry.NefSelfIntersectionNonnegative

/-!
# The actual sum of an ample and a nef Cartier divisor is ample

On the original smooth projective surface, H²>0, H.A≥0 and A²≥0 give
(H+A)²>0. Every original prime curve has positive intersection with H
and nonnegative intersection with A. The reviewed full surface Nakai
criterion therefore proves Serre ampleness of the original O(H+A).
No numerical positivity or criterion parameter is supplied by the user.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.AmpleNefCartierSum

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The original ample-plus-nef Cartier sum has strictly positive square,
using the independently compiled nonnegative square of the nef divisor. -/
theorem intersection_add_self_pos (H A : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A)) :
    0 < intersectionPairing X X.regularPoints_of_isSmooth (H + A) (H + A) := by
  have hHH : 0 < intersectionPairing X X.regularPoints_of_isSmooth H H := by
    have h := AmpleSelfIntersectionPositive.selfIntersection_pos_of_isAmple
      X X.regularPoints_of_isSmooth (cartierDivisorInvertibleSheaf X.toScheme H) hH
    change 0 < X.picardPairing X.regularPoints_of_isSmooth
      (cartierPicardClass X.toScheme H) (cartierPicardClass X.toScheme H) at h
    rwa [X.picardPairing_class X.regularPoints_of_isSmooth] at h
  have hAA : 0 ≤ intersectionPairing X X.regularPoints_of_isSmooth A A := by
    have h := NefSelfIntersectionNonnegative.selfIntersection_nonneg X
      (cartierDivisorInvertibleSheaf X.toScheme A) hA
    change 0 ≤ X.picardPairing X.regularPoints_of_isSmooth
      (cartierPicardClass X.toScheme A) (cartierPicardClass X.toScheme A) at h
    rwa [X.picardPairing_class X.regularPoints_of_isSmooth] at h
  have hHA := NefSelfIntersectionNonnegative.intersection_nonneg_of_isAmple_isNef
    X X.regularPoints_of_isSmooth H A hH hA
  rw [X.intersectionPairing_add_left, X.intersectionPairing_add_right,
    X.intersectionPairing_add_right,
    X.intersectionPairing_symm X.regularPoints_of_isSmooth A H]
  omega

/-- Every original prime curve has strictly positive intersection with
the actual ample-plus-nef Cartier sum. -/
theorem intersection_add_primeCurve_pos (H A : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A)) (C : X.PrimeCurve) :
    0 < intersectionPairing X X.regularPoints_of_isSmooth (H + A)
      (X.primeCurveCartier X.regularPoints_of_isSmooth C) := by
  rw [X.intersectionPairing_add_left]
  have hHC : 0 < intersectionPairing X X.regularPoints_of_isSmooth H
      (X.primeCurveCartier X.regularPoints_of_isSmooth C) := by
    rw [X.intersectionPairing_primeCurve, C.intersectionNumber_eq_restrictionDegree]
    exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme H) hH C
  have hAC := (X.isNef_iff_pairing X.regularPoints_of_isSmooth A).mp hA C
  exact add_pos_of_pos_of_nonneg hHC hAC

/-- On the original smooth projective surface, the actual sum of an
ample Cartier divisor and a nef Cartier divisor is Serre ample. -/
theorem isAmple_add (H A : CartierDivisor X.toScheme)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H))
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A)) :
    AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme (H + A)) :=
  SurfaceNakaiMoishezonProved.cartier_isAmple_of_positive X X.regularPoints_of_isSmooth (H + A)
    (intersection_add_self_pos X H A hH hA)
    (intersection_add_primeCurve_pos X H A hH hA)

end KltDP.Geometry.AmpleNefCartierSum
