import KltDP.Examples.FrobeniusMultiCentreRulingNefClasses

/-!
# Nefness of the original two rulings on the multicentre surface

Both original ruling morphisms pull back the original degree-one line bundle
on the projective line. The proved global-generation and nefness producer
therefore applies to those exact maps. The original ruling-class comparisons
give nonnegative restriction degree on every actual prime curve, and hence
nonnegative pairing with every original prime Cartier class. The actual
surface projectivity premise is retained. No claim about subtracting
exceptional classes from these nef ruling classes is made.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRulingNef

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusGraphClosed FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreRulingNefClasses

private theorem degree_nonneg_of_nef {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
    (hL : Positivity.IsNef X.structureMorphism L) (C : X.PrimeCurve) :
    0 ≤ X.picardRestrictionDegreeHom C (Additive.ofMul L.toPic) := by
  change 0 ≤ C.picardRestrictionDegree L.toPic
  rw [C.picardRestrictionDegree_toPic]
  exact (Positivity.isNef_iff_forall_primeCurve X L).mp hL C

variable {k : Type u} [Field k] [IsAlgClosed k]
  (p n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure p n a))

local instance rulingNefSurfaceIntegral : IsIntegral (multiSurface p n a) :=
  multiSurface_isIntegral p n a ha

include ha hproj in
/-- The actual first ruling degree-one pullback is nef on the original surface. -/
theorem firstRulingLine_isNef :
    Positivity.IsNef (multiStructure p n a) (firstRulingLine p n a) :=
  ProjectiveLineDegreeOnePullbackNef.pullback_isNef
    (multiSurfaceSurface p n a ha hproj) (multiProjection p n a ≫ firstProjection)

include ha hproj in
/-- The actual second ruling degree-one pullback is nef on the original surface. -/
theorem secondRulingLine_isNef :
    Positivity.IsNef (multiStructure p n a) (secondRulingLine p n a) :=
  ProjectiveLineDegreeOnePullbackNef.pullback_isNef
    (multiSurfaceSurface p n a ha hproj) (multiProjection p n a ≫ secondProjection)

/-- Every actual prime curve has nonnegative degree against the original first ruling class. -/
theorem firstRuling_primeDegree_nonneg (C : (multiSurfaceSurface p n a ha hproj).PrimeCurve) :
    0 ≤ (multiSurfaceSurface p n a ha hproj).picardRestrictionDegreeHom C
      (multiFirstFiberClass p n a) := by
  rw [← firstRulingLine_class]
  exact degree_nonneg_of_nef (multiSurfaceSurface p n a ha hproj) (firstRulingLine p n a)
    (firstRulingLine_isNef p n a ha hproj) C

/-- Every actual prime curve has nonnegative degree against the original second ruling class. -/
theorem secondRuling_primeDegree_nonneg (C : (multiSurfaceSurface p n a ha hproj).PrimeCurve) :
    0 ≤ (multiSurfaceSurface p n a ha hproj).picardRestrictionDegreeHom C
      (multiSecondFiberClass p n a) := by
  rw [← secondRulingLine_class]
  exact degree_nonneg_of_nef (multiSurfaceSurface p n a ha hproj) (secondRulingLine p n a)
    (secondRulingLine_isNef p n a ha hproj) C

/-- The original first ruling pairs nonnegatively with every actual prime Cartier class. -/
theorem firstRuling_primePairing_nonneg (C : (multiSurfaceSurface p n a ha hproj).PrimeCurve) :
    0 ≤ multiPairing p n a ha hproj (multiFirstFiberClass p n a)
      (cartierPicardHom (multiSurfaceSurface p n a ha hproj).toScheme
        ((multiSurfaceSurface p n a ha hproj).primeCurveCartier
          (multiSurfaceSurface_regularPoints p n a ha hproj) C)) := by
  change 0 ≤ pairing (multiSurfaceSurface p n a ha hproj)
    (multiSurfaceSurface_regularPoints p n a ha hproj) _ _
  rw [pairing_primeCurve_right]
  exact firstRuling_primeDegree_nonneg p n a ha hproj C

/-- The original second ruling pairs nonnegatively with every actual prime Cartier class. -/
theorem secondRuling_primePairing_nonneg (C : (multiSurfaceSurface p n a ha hproj).PrimeCurve) :
    0 ≤ multiPairing p n a ha hproj (multiSecondFiberClass p n a)
      (cartierPicardHom (multiSurfaceSurface p n a ha hproj).toScheme
        ((multiSurfaceSurface p n a ha hproj).primeCurveCartier
          (multiSurfaceSurface_regularPoints p n a ha hproj) C)) := by
  change 0 ≤ pairing (multiSurfaceSurface p n a ha hproj)
    (multiSurfaceSurface_regularPoints p n a ha hproj) _ _
  rw [pairing_primeCurve_right]
  exact secondRuling_primeDegree_nonneg p n a ha hproj C

end KltDP.Examples.FrobeniusMultiCentreRulingNef
