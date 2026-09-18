import KltDP.Examples.FrobeniusInitialCanonicalFiberEquations
import KltDP.Examples.FrobeniusInitialCanonicalFactors
import KltDP.Examples.FrobeniusGraphPicardClassFiberClasses

/-!
# The pulled coordinate-point ideal classes are the original fiber classes

The general proved Cartier/Picard pullback comparison is applied to the
original coordinate point, whose effective Cartier equations were derived
from its actual kernel. The proved pulled-divisor equation and the vanishing
Picard class of a principal divisor identify its inverse ideal class with
the existing infinity ruling, hence with the already defined x=1 or y=1
fiber class. No fiber class is redefined.

This closes the fiber-class part of the initial canonical calculation.
The product canonical-sheaf comparison with its two pulled cotangent
factors remains a separate theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalFiberClasses

open KltDP.Geometry CartierPullbackComparison
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusGraphPicardClassIntegral
open FrobeniusProjectiveCoordinatePicard FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusGraphPicardClassRulingDivisors FrobeniusGraphPicardClassFiberClasses
open FrobeniusInitialCanonicalFiberPoint FrobeniusInitialCanonicalFiberMaps
open FrobeniusInitialCanonicalFiberEquations FrobeniusInitialCanonicalFactors

variable {k : Type u} [Field k]

local instance fiberClassesProductIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance fiberClassesLineIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

local instance fiberClassesGeneric (d : Fin 2) :
    GenericPointPreserving (rulingProjection (k := k) d) :=
  rulingProjection_genericPointPreserving d

/-- The actual inverse pulled point-ideal class is the already constructed ruling class. -/
theorem inverse_pullbackCoordinateIdeal_eq_ruling (d : Fin 2) :
    -Additive.ofMul
        (pullbackInvertibleSheaf (rulingProjection (k := k) d) coordinateIdealLine).toPic =
      cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor d) := by
  have h := cartierPicardHom_pullbackDivisor_eq (rulingProjection (k := k) d)
    coordinateCartier coordinateCartier_hasRegularEquations
  rw [pullback_coordinateCartier_eq_ruling_add_principal, map_add,
    cartierPicardHom_principal, add_zero, coordinateCartier_picard, map_neg] at h
  change cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor d) =
    -Additive.ofMul (schemePicardPullbackHom (rulingProjection d)
      (coordinateIdealLine (k := k)).toPic) at h
  rw [schemePicardPullbackHom_toPic] at h
  exact h.symm

/-- Pullback along the original first projection gives the original first fiber class. -/
theorem inverse_firstPullbackCoordinateIdeal_eq_firstFiberClass :
    -Additive.ofMul
        (pullbackInvertibleSheaf (firstProjection (k := k)) coordinateIdealLine).toPic =
      firstFiberClass := by
  simpa [rulingProjection] using
    (inverse_pullbackCoordinateIdeal_eq_ruling (k := k) 0).trans
      (firstFiberClass_eq_ruling (k := k)).symm

/-- Pullback along the original second projection gives the original second fiber class. -/
theorem inverse_secondPullbackCoordinateIdeal_eq_secondFiberClass :
    -Additive.ofMul
        (pullbackInvertibleSheaf (secondProjection (k := k)) coordinateIdealLine).toPic =
      secondFiberClass := by
  simpa [rulingProjection] using
    (inverse_pullbackCoordinateIdeal_eq_ruling (k := k) 1).trans
      (secondFiberClass_eq_ruling (k := k)).symm

/-- The actual pulled canonical factors have coefficients minus two in the
already defined first and second fiber classes. -/
theorem canonicalFactorPicard_eq_fiberClasses :
    Additive.ofMul
        (pullbackInvertibleSheaf (firstProjection (k := k))
          (ProjectiveLineCanonical.canonicalSheaf k)).toPic +
      Additive.ofMul
        (pullbackInvertibleSheaf (secondProjection (k := k))
          (ProjectiveLineCanonical.canonicalSheaf k)).toPic =
      (-2 : ℤ) • firstFiberClass + (-2 : ℤ) • secondFiberClass := by
  rw [factorPicard_eq_coordinatePullbacks,
    inverse_firstPullbackCoordinateIdeal_eq_firstFiberClass,
    inverse_secondPullbackCoordinateIdeal_eq_secondFiberClass]

end KltDP.Examples.FrobeniusInitialCanonicalFiberClasses
