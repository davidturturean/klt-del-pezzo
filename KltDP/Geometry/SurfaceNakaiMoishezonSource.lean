import KltDP.Geometry.SurfaceHodgeIndexSource

/-!
Conditional original-object translation of the full Hartshorne V Theorem 1.10.
This diagnostic contains no axiom. The whole iff is retained for every original
Weil divisor, on the same regular integral projective surface as the source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SurfaceHodgeIndexSource

universe u

namespace KltDP.Geometry.SurfaceNakaiMoishezonSource

/-- Complete surface Nakai--Moishezon criterion on the original source objects. -/
def RawStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of k))
    (hIntegral : IsIntegral Y) (hprojective : IsProjectiveOverField f)
    (hdimension : topologicalKrullDim Y = 2)
    (hregular : ∀ y : Y, RegularPoint Y y),
    let X := sourceSurface Y f hIntegral hprojective hdimension hregular
    ∀ D : X.WeilDivisor,
      AmpleSerre.IsAmple (divisorLine X hregular D) ↔
        0 < divisorPairing X hregular D D ∧
          ∀ C : X.PrimeCurve, 0 < divisorPairing X hregular D (Finsupp.single C 1)

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Specialization preserves the original underlying scheme and structure map. -/
theorem raw_apply (raw : RawStatement.{u}) (D : X.WeilDivisor) :
    AmpleSerre.IsAmple (divisorLine X hregular D) ↔
      0 < divisorPairing X hregular D D ∧
        ∀ C : X.PrimeCurve, 0 < divisorPairing X hregular D (Finsupp.single C 1) :=
  raw k X.toScheme X.structureMorphism X.integral X.projective X.dimension_two hregular D

/-- The original Cartier criterion is a proved transport of the complete Weil iff. -/
theorem cartier_isAmple_iff (raw : RawStatement.{u}) (D : CartierDivisor X.toScheme) :
    AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D) ↔
      0 < intersectionPairing X hregular D D ∧
        ∀ C : X.PrimeCurve,
          0 < intersectionPairing X hregular D (X.primeCurveCartier hregular C) := by
  have h := raw_apply X hregular raw ((X.regularCartierWeilEquiv hregular) D)
  simpa only [divisorLine, divisorPairing, AddEquiv.symm_apply_apply] using h

/-- Sufficient numerical conditions produce the actual ample Cartier line sheaf. -/
theorem cartier_isAmple_of_positive (raw : RawStatement.{u})
    (D : CartierDivisor X.toScheme) (hDD : 0 < intersectionPairing X hregular D D)
    (hDC : ∀ C : X.PrimeCurve,
      0 < intersectionPairing X hregular D (X.primeCurveCartier hregular C)) :
    AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D) :=
  (cartier_isAmple_iff X hregular raw D).mpr ⟨hDD, hDC⟩

end KltDP.Geometry.SurfaceNakaiMoishezonSource
