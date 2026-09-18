import KltDP.Geometry.ProjectiveProductCanonicalFactors
import KltDP.Examples.FrobeniusGraphClosed

/-!
# The two actual canonical factors on the initial projective product

This computes the sum of the classes pulled along the original product
projections. The right side uses the original coordinate-point ideals,
pulled by those same maps. It does not replace the existing fiber classes
by these expressions or assert a formula for the product canonical class.

The remaining original-object comparisons are the product differential
splitting and the identification of these pulled point ideals with the
already defined fiber ideal classes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalFactors

open KltDP.Geometry ProjectiveProductCanonicalFactors
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusProjectiveCoordinatePicard

variable {k : Type u} [Field k]

/-- The two original pulled cotangent classes have coefficient minus two in the
inverse pulled coordinate-ideal classes, over any field. -/
theorem factorPicard_eq_coordinatePullbacks :
    Additive.ofMul
        (pullbackInvertibleSheaf (firstProjection (k := k))
          (ProjectiveLineCanonical.canonicalSheaf k)).toPic +
      Additive.ofMul
        (pullbackInvertibleSheaf (secondProjection (k := k))
          (ProjectiveLineCanonical.canonicalSheaf k)).toPic =
      (-2 : ℤ) • (-Additive.ofMul
        (pullbackInvertibleSheaf (firstProjection (k := k))
          (coordinateIdealLine (k := k))).toPic) +
      (-2 : ℤ) • (-Additive.ofMul
        (pullbackInvertibleSheaf (secondProjection (k := k))
          (coordinateIdealLine (k := k))).toPic) := by
  rw [pullback_canonical_toPic_eq_coordinate_square,
    pullback_canonical_toPic_eq_coordinate_square]
  simp only [pow_two, neg_smul_neg, two_smul]
  rfl

end KltDP.Examples.FrobeniusInitialCanonicalFactors
