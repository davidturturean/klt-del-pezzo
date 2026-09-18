import KltDP.Examples.FrobeniusInitialCanonicalFiberClasses
import KltDP.Examples.FrobeniusMultiCentreRulingPairing
import KltDP.Geometry.ProjectiveLineDegreeOnePullbackNef

/-!
# The actual ruling line bundles are the original degree-one pullbacks

The original coordinate-point ideal has Picard exponent minus one. The
injective original projective-line exponent therefore identifies its inverse
with the existing degree-one line bundle. The proved original coordinate-fibre
class comparisons and Picard pullback composition then identify the two actual
multicentre ruling classes with degree-one pullbacks along their original maps.
No curve degree or positivity assertion is assumed in these comparisons.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRulingNefClasses

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusProjectiveCoordinatePicard
open FrobeniusGraphPicardClassFiberClasses FrobeniusInitialCanonicalFiberClasses
open FrobeniusMultiCentreSurface FrobeniusMultiCentreRulingPairing

variable {k : Type u} [Field k]

/-- The original degree-one class is the inverse of the original coordinate-point ideal class. -/
theorem degreeOne_toPic_eq_coordinate_inverse :
    (monomialLineBundle k 1).toPic = (coordinateIdealLine (k := k)).toPic⁻¹ := by
  apply ProjectiveLinePicardExponent.hom_injective k
  rw [map_inv]
  change Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k
      (monomialLineBundle k 1).toPic) =
    (Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k
      (coordinateIdealLine (k := k)).toPic))⁻¹
  rw [ProjectiveLinePicardExponent.value_toPic, monomialLineBundle_exponent,
    coordinatePicardValue_eq_neg_one]
  rfl

private theorem pullback_degreeOne_class {X : Scheme.{u}}
    (f : X ⟶ projectiveSpace k 1) :
    Additive.ofMul (pullbackInvertibleSheaf f (monomialLineBundle k 1)).toPic =
      -Additive.ofMul (pullbackInvertibleSheaf f (coordinateIdealLine (k := k))).toPic := by
  simp only [← schemePicardPullbackHom_toPic, degreeOne_toPic_eq_coordinate_inverse,
    map_inv, ofMul_inv]

/-- The degree-one pullback along the original first projection is the original first ruling. -/
theorem degreeOne_firstProjection_class :
    Additive.ofMul
        (pullbackInvertibleSheaf (firstProjection (k := k)) (monomialLineBundle k 1)).toPic =
      firstFiberClass :=
  (pullback_degreeOne_class firstProjection).trans
    inverse_firstPullbackCoordinateIdeal_eq_firstFiberClass

/-- The degree-one pullback along the original second projection is the original second ruling. -/
theorem degreeOne_secondProjection_class :
    Additive.ofMul
        (pullbackInvertibleSheaf (secondProjection (k := k)) (monomialLineBundle k 1)).toPic =
      secondFiberClass :=
  (pullback_degreeOne_class secondProjection).trans
    inverse_secondPullbackCoordinateIdeal_eq_secondFiberClass

private theorem composite_degreeOne_class {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ projectiveSpace k 1) :
    Additive.ofMul (pullbackInvertibleSheaf (f ≫ g) (monomialLineBundle k 1)).toPic =
      (schemePicardPullbackHom f).toAdditive
        (Additive.ofMul (pullbackInvertibleSheaf g (monomialLineBundle k 1)).toPic) := by
  rw [← schemePicardPullbackHom_toPic, schemePicardPullbackHom_comp]
  change Additive.ofMul
      (schemePicardPullbackHom f (schemePicardPullbackHom g (monomialLineBundle k 1).toPic)) =
    Additive.ofMul
      (schemePicardPullbackHom f (pullbackInvertibleSheaf g (monomialLineBundle k 1)).toPic)
  rw [schemePicardPullbackHom_toPic]

/-- The actual degree-one pullback along the original first ruling map. -/
def firstRulingLine (p n : ℕ) (a : Fin n → k) : InvertibleSheaf (multiSurface p n a) :=
  pullbackInvertibleSheaf (multiProjection p n a ≫ firstProjection) (monomialLineBundle k 1)

/-- The actual degree-one pullback along the original second ruling map. -/
def secondRulingLine (p n : ℕ) (a : Fin n → k) : InvertibleSheaf (multiSurface p n a) :=
  pullbackInvertibleSheaf (multiProjection p n a ≫ secondProjection) (monomialLineBundle k 1)

variable [IsAlgClosed k]

/-- Its class is the existing original first ruling class on the multicentre surface. -/
theorem firstRulingLine_class (p n : ℕ) (a : Fin n → k) :
    Additive.ofMul (firstRulingLine p n a).toPic = multiFirstFiberClass p n a := by
  unfold firstRulingLine
  rw [composite_degreeOne_class, degreeOne_firstProjection_class, pullback_firstFiberClass]

/-- Its class is the existing original second ruling class on the multicentre surface. -/
theorem secondRulingLine_class (p n : ℕ) (a : Fin n → k) :
    Additive.ofMul (secondRulingLine p n a).toPic = multiSecondFiberClass p n a := by
  unfold secondRulingLine
  rw [composite_degreeOne_class, degreeOne_secondProjection_class, pullback_secondFiberClass]

end KltDP.Examples.FrobeniusMultiCentreRulingNefClasses
