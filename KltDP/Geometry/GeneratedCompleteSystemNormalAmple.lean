import KltDP.Geometry.GeneratedCompleteSystemNormalFactor
import KltDP.Geometry.FinitePullbackImageLineAmple

/-! Ampleness of the original image line on the constructed normal factor. -/

open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.GeneratedCompleteSystemNormalFactor

open CompleteLinearSystemSections CompleteLinearSystemMap

/-- The original line on the actual normal factor is ample, with finiteness
and the original projective coordinate cover supplied by proved producers. -/
theorem line_isAmple {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
    [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)
    (hG : Positivity.IsGloballyGenerated L.obj) :
    AmpleSerre.IsAmple (line f L hpos hG) := by
  letI : IsFinite (toImage f L hpos hG) := toImage_isFinite f L hpos hG
  exact FinitePullbackImageLineAmple.finite_pullback_degreeOne_isAmple
    k (dimension f L - 1) (toImage f L hpos hG)
    (SchematicImageGlued.inclusion (morphism f L hpos))

end KltDP.Geometry.GeneratedCompleteSystemNormalFactor
