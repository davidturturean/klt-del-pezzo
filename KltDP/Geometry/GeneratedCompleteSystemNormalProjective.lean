import KltDP.Geometry.GeneratedCompleteSystemNormalFactor
import KltDP.Geometry.FiniteOverProjective

/-! Projectivity of the constructed normal factor through its original finite image map. -/

open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.GeneratedCompleteSystemNormalFactor

open CompleteLinearSystemSections CompleteLinearSystemMap

/-- The actual relative-spectrum target is projective over the original field.
Neither target projectivity nor a target embedding is an input. -/
theorem structureMorphism_isProjective
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
    [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)
    (hG : Positivity.IsGloballyGenerated L.obj) :
    IsProjectiveOverField (structureMorphism f L hpos hG) := by
  letI : IsFinite (toImage f L hpos hG) := toImage_isFinite f L hpos hG
  exact IsProjectiveOverField.comp_isFinite (toImage f L hpos hG)
    (imageStructure f L hpos) (imageStructure_isProjective f L hpos)

end KltDP.Geometry.GeneratedCompleteSystemNormalFactor
