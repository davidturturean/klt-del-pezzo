import KltDP.Geometry.GeneratedCompleteSystemNormalFactor
import KltDP.Geometry.ProperBirationalDimension

/-! Dimension of the actual generated complete-system normal factor. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.GeneratedCompleteSystemNormalFactor

open CompleteLinearSystemSections CompleteLinearSystemMap

attribute [local instance] KeelCompleteSystem.completeSystemDomain_isIntegral
  KeelCompleteSystem.completeSystemImage_isIntegral

/-- The original birational source factor preserves the dimension of its
actual relative-spectrum target. -/
theorem target_dimension_eq
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (L : InvertibleSheaf X)
    [IsProper f] [IsIntegral X] (hpos : 0 < dimension f L)
    (hG : Positivity.IsGloballyGenerated L.obj)
    (hbir : IsBirationalScheme (SchematicImageGlued.toImage (morphism f L hpos))) :
    topologicalKrullDim (target f L hpos hG) = topologicalKrullDim X := by
  letI : IsIntegral (target f L hpos hG) := target_isIntegral f L hpos hG
  letI : IsProper (fromSource f L hpos hG) := fromSource_isProper f L hpos hG
  letI : IsProper (structureMorphism f L hpos hG) := structureMorphism_isProper f L hpos hG
  exact (topologicalKrullDim_eq_of_proper_birational
    (fromSource f L hpos hG) (structureMorphism f L hpos hG)
    (fromSource_isBirationalScheme f L hpos hG hbir)).symm

/-- The same constructed target has dimension two for the original surface. -/
theorem target_dimension_two
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
    (hpos : 0 < dimension X.structureMorphism L)
    (hG : Positivity.IsGloballyGenerated L.obj)
    (hbir : IsBirationalScheme
      (SchematicImageGlued.toImage (morphism X.structureMorphism L hpos))) :
    topologicalKrullDim (target X.structureMorphism L hpos hG) = 2 :=
  (target_dimension_eq X.structureMorphism L hpos hG hbir).trans X.dimension_two

end KltDP.Geometry.GeneratedCompleteSystemNormalFactor
