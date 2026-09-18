import KltDP.Geometry.MinimalResolutionDebts
import KltDP.Literature.Hartshorne.SurfaceProjectivity

/-!
# An actual regular proper surface as a normal projective surface

The original scheme and original field structure morphism are retained
definitionally. Normality uses the existing regular-local UFD theorem;
projectivity uses the previously admitted isolated full Hartshorne statement.
Regularity and dimension are genuine geometric inputs to this generic
adapter, and must be proved for any particular constructed blowup source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Equip the given integral regular proper two-dimensional scheme with
its derived normal/projective surface properties, retaining its original map. -/
def regularProperSurface {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hreg : ∀ x, RegularPoint X x) (hdim : topologicalKrullDim X = 2) :
    NormalProjectiveSurface k where
  toScheme := X
  structureMorphism := f
  integral := inferInstance
  normal := isNormalScheme_of_regularPoint hreg
  projective := KltDP.Literature.Hartshorne.nonsingular_complete_surface_projective_literal
    k X f inferInstance inferInstance inferInstance inferInstance inferInstance hreg hdim
  dimension_two := hdim

/-- A proper birational morphism from this actual regular source is a
resolution of the original target. No replacement morphism is introduced. -/
theorem regularProperSurface_isResolution
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : NormalProjectiveSurface k) (X : Scheme.{u}) [IsIntegral X]
    (b : X ⟶ T.toScheme) [IsProper b]
    (hreg : ∀ x, RegularPoint X x) (hdim : topologicalKrullDim X = 2)
    (hbir : IsBirationalScheme b) :
    letI : IsProper T.structureMorphism := T.projective.isProper
    IsResolution (regularProperSurface X (b ≫ T.structureMorphism) hreg hdim) T b := by
  letI : IsProper T.structureMorphism := T.projective.isProper
  exact ⟨rfl, hreg, ⟨hbir.map_genericPoint, hbir.isIso_stalkMap_genericPoint⟩⟩

end KltDP.Geometry

#check @KltDP.Geometry.regularProperSurface
#print axioms KltDP.Geometry.regularProperSurface
#check @KltDP.Geometry.regularProperSurface_isResolution
#print axioms KltDP.Geometry.regularProperSurface_isResolution
