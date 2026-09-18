import KltDP.Geometry.GeneratedCompleteSystemNormalDimension
import KltDP.Geometry.GeneratedCompleteSystemNormalProjective

/-! The original generated normal factor as a normal projective surface. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.GeneratedCompleteSystemNormalFactor

open CompleteLinearSystemSections CompleteLinearSystemMap

attribute [local instance] KeelCompleteSystem.completeSystemDomain_isIntegral
  KeelCompleteSystem.completeSystemImage_isIntegral

/-- The wrapper retains the original relative-spectrum target and its
original field structure. All four geometric properties are proved. -/
def normalProjectiveSurface
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)
    (hpos : 0 < dimension X.structureMorphism L)
    (hG : Positivity.IsGloballyGenerated L.obj)
    (hbir : IsBirationalScheme
      (SchematicImageGlued.toImage (morphism X.structureMorphism L hpos))) :
    NormalProjectiveSurface k where
  toScheme := target X.structureMorphism L hpos hG
  structureMorphism := structureMorphism X.structureMorphism L hpos hG
  integral := target_isIntegral X.structureMorphism L hpos hG
  normal := target_isNormal X.structureMorphism L hpos hG X.normal
  projective := structureMorphism_isProjective X.structureMorphism L hpos hG
  dimension_two := target_dimension_two X L hpos hG hbir

end KltDP.Geometry.GeneratedCompleteSystemNormalFactor
