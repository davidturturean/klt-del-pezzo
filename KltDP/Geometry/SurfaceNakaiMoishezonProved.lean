import KltDP.Literature.Hartshorne.SurfaceNakaiMoishezon

/-!
# Actual Cartier consumers of the full published surface ampleness criterion

The source and full literal keep the original Weil statement. These consumers
use the separately compiled Cartier--Weil transport; no numerical positivity
or raw criterion premise is hidden in the actual surface object.
-/

noncomputable section

open AlgebraicGeometry
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceHodgeIndexSource

universe u

namespace KltDP.Geometry.SurfaceNakaiMoishezonProved

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The whole published iff on every original Weil divisor. -/
theorem published (D : X.WeilDivisor) :
    AmpleSerre.IsAmple (divisorLine X hregular D) ↔
      0 < divisorPairing X hregular D D ∧
        ∀ C : X.PrimeCurve, 0 < divisorPairing X hregular D (Finsupp.single C 1) :=
  SurfaceNakaiMoishezonSource.raw_apply X hregular
    Literature.Hartshorne.surface_nakai_moishezon_literal D

/-- The actual Cartier line sheaf is ample exactly under the original numerical tests. -/
theorem cartier_isAmple_iff (D : CartierDivisor X.toScheme) :
    AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D) ↔
      0 < intersectionPairing X hregular D D ∧
        ∀ C : X.PrimeCurve,
          0 < intersectionPairing X hregular D (X.primeCurveCartier hregular C) :=
  SurfaceNakaiMoishezonSource.cartier_isAmple_iff X hregular
    Literature.Hartshorne.surface_nakai_moishezon_literal D

/-- Positive square and positive degree on every original prime curve suffice. -/
theorem cartier_isAmple_of_positive (D : CartierDivisor X.toScheme)
    (hDD : 0 < intersectionPairing X hregular D D)
    (hDC : ∀ C : X.PrimeCurve,
      0 < intersectionPairing X hregular D (X.primeCurveCartier hregular C)) :
    AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D) :=
  (cartier_isAmple_iff X hregular D).mpr ⟨hDD, hDC⟩

end KltDP.Geometry.SurfaceNakaiMoishezonProved
