import KltDP.Geometry.NefPositiveSpanProved

/-!
# Actual negative curves orthogonal to a nontrivial nef line bundle

The existing numerical restriction-degree and prime Cartier comparisons
instantiate the nef positive-span obstruction on the original prime curves.
No numerical intersection matrix or class independence is supplied.
-/

noncomputable section

open AlgebraicGeometry
open KltDP.Geometry.NormalProjectiveSurface

universe u

namespace KltDP.Geometry.NefOrthogonalNegativeCurves

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

private def curveClass (C : X.PrimeCurve) : X.NumericalClassGroup :=
  X.picardNumericalClass (cartierPicardClass X.toScheme
    (X.primeCurveCartier X.regularPoints_of_isSmooth C))

private theorem pairing_curves (C P : X.PrimeCurve) :
    X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      (curveClass X C) (curveClass X P) =
    (P.intersectionNumber (X.primeCurveCartier X.regularPoints_of_isSmooth C) : ℚ) := by
  unfold curveClass
  change X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
    (X.picardNumericalMap (Additive.ofMul _))
    (X.picardNumericalMap (Additive.ofMul _)) = _
  rw [X.numericalIntersectionBilinForm_picard]
  simp only [toMul_ofMul]
  rw [X.picardPairing_class, X.intersectionPairing_primeCurve]

private theorem pairing_curve_line (C : X.PrimeCurve) (L : InvertibleSheaf X.toScheme) :
    X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
      (curveClass X C) (X.picardNumericalClass L.toPic) =
    (C.picardRestrictionDegree L.toPic : ℚ) := by
  rw [(X.numericalIntersectionBilinForm_isSymm X.regularPoints_of_isSmooth).eq]
  change X.numericalIntersectionBilinForm X.regularPoints_of_isSmooth
    (X.picardNumericalClass L.toPic)
    (X.picardNumericalClass (cartierPicardClass X.toScheme
      (X.primeCurveCartier X.regularPoints_of_isSmooth C))) = _
  rw [X.numericalIntersectionBilinForm_primeCurve]
  exact X.numericalRestrictionDegree_picardNumericalMap C (Additive.ofMul L.toPic)

/-- A (-2)-curve and a (-1)-curve perpendicular to a numerically nontrivial
nef line bundle have original integral intersection number at most one. -/
theorem intersection_le_one
    (L : InvertibleSheaf X.toScheme) (hL : Positivity.IsNef X.structureMorphism L)
    (hne : ¬ X.NumericallyTrivial L.toPic) (C P : X.PrimeCurve)
    (hC : C.selfIntersectionNumber X.regularPoints_of_isSmooth = -2)
    (hP : P.selfIntersectionNumber X.regularPoints_of_isSmooth = -1)
    (hCL : C.picardRestrictionDegree L.toPic = 0)
    (hPL : P.picardRestrictionDegree L.toPic = 0) :
    P.intersectionNumber (X.primeCurveCartier X.regularPoints_of_isSmooth C) ≤ 1 := by
  apply NefPositiveSpanProved.intersection_le_one X L hL hne (curveClass X C)
    (curveClass X P)
  · rw [pairing_curves]
    change (C.selfIntersectionNumber X.regularPoints_of_isSmooth : ℚ) = -2
    exact_mod_cast hC
  · rw [pairing_curves]
    change (P.selfIntersectionNumber X.regularPoints_of_isSmooth : ℚ) = -1
    exact_mod_cast hP
  · exact pairing_curves X C P
  · rw [pairing_curve_line, hCL, Int.cast_zero]
  · rw [pairing_curve_line, hPL, Int.cast_zero]

end KltDP.Geometry.NefOrthogonalNegativeCurves
