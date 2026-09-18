import KltDP.Geometry.KltResolutionExceptionalProjectiveLine
import KltDP.Geometry.RationalProjectiveLineDegreeZero

/-!
# Actual degree-zero restrictions on original klt exceptional curves

The original curve's projective-line isomorphism is constructed from klt.
The original Euler degree is the restriction degree already used in the
intersection calculation, so its vanishing supplies a frame on that same
curve, over the original field.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  {π : S.toScheme ⟶ X.toScheme}

/-- Each original exceptional restriction of degree zero is trivial; no
rationality, coordinate, or curve-isomorphism hypothesis is supplied. -/
theorem IsResolution.exceptional_restriction_trivial_of_klt
    (hres : IsResolution S X π) (hklt : IsKlt X)
    (L : InvertibleSheaf S.toScheme) (C : S.PrimeCurve)
    (hC : IsExceptionalCurve π C) (hdegree : C.restrictionDegree L = 0) :
    Nonempty ((pullbackInvertibleSheaf C.inclusion L).obj ≅
      _root_.SheafOfModules.unit C.toScheme.ringCatSheaf) := by
  obtain ⟨e, he⟩ := hres.exceptional_projectiveLine_iso_of_klt hklt C hC
  exact ⟨RationalTreePicard.unitIsoOfEulerDegreeZero e C.toSpec he
    (pullbackInvertibleSheaf C.inclusion L) hdegree⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsResolution.exceptional_restriction_trivial_of_klt
