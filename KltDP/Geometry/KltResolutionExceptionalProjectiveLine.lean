import KltDP.Geometry.KltResolutionExceptionalGenusZero
import KltDP.Geometry.GenusZeroCurveProjectiveLineIso
import KltDP.Geometry.RationalCurveSmooth
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse

/-!
# Actual projective-line exceptional curves of a klt resolution

Arithmetic adjunction and the original discrepancy matrix give arithmetic
genus zero for every original exceptional prime. The proved genus-zero
curve theorem constructs an isomorphism of that same curve with P1 over
the original field. No curve rationality, smoothness, point, map or degree
is an input. Source smoothness follows from the regularity of the original resolution.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  {π : S.toScheme ⟶ X.toScheme}

/-- Every original exceptional prime is the actual projective line over k. -/
theorem IsResolution.exceptional_projectiveLine_iso_of_klt
    (hres : IsResolution S X π) (hklt : IsKlt X)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) :
    ∃ e : C.toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hres.regular
  letI : IsProper C.toSpec := C.toSpec_isProper
  exact GenusZeroCurveProjectiveLineIso.exists_iso C.toSpec C.dimension_one_toScheme
    (hres.exceptional_arithmetic_genus_zero_of_klt hklt C hC)

/-- Smoothness of the original exceptional curve is derived from the
constructed isomorphism; it is not assumed in the arithmetic adjunction. -/
theorem IsResolution.exceptional_smoothOne_of_klt
    (hres : IsResolution S X π) (hklt : IsKlt X)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) :
    IsSmoothOfRelativeDimension 1 C.toSpec := by
  obtain ⟨e, he⟩ := hres.exceptional_projectiveLine_iso_of_klt hklt C hC
  exact smoothOne_of_projectiveLineIso C.toSpec e he

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.exceptional_projectiveLine_iso_of_klt
#print axioms KltDP.Geometry.IsResolution.exceptional_projectiveLine_iso_of_klt
#print axioms KltDP.Geometry.IsResolution.exceptional_smoothOne_of_klt
