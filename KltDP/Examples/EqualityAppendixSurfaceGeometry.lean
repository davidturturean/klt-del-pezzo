import KltDP.Examples.EqualityAppendixSurfaceIntegral
import KltDP.Geometry.SmoothFieldAllPointsRegular
import KltDP.Geometry.RegularProperSurface

/-!
# The original mixed appendix surface as a normal projective surface

The proper projection and its nonempty actual isomorphism open give dimension
two. The original smooth structure map then gives regularity at every stalk.
The existing regular-proper-surface adapter supplies the normal projective
packaging, preserving the literal mixed surface and its structure morphism.
It retains that adapter's existing isolated projectivity source dependency.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.EqualityAppendixSurface

open KltDP.Geometry FrobeniusProjectivePoints FrobeniusStageDimension

variable {k : Type u} [Field k] [CharP k 3] [IsAlgClosed k]

instance surface_integral : IsIntegral (surface (k := k)) := surface_isIntegral

theorem surface_dimension_two : topologicalKrullDim (surface (k := k)) = 2 := by
  letI : IsIntegral (projectiveProduct k) :=
    FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral
  letI := centersComplement_nonempty (k := k)
  letI := projection_restrict_isIso (k := k)
  exact (topologicalKrullDim_eq_of_proper_isomorphism_open projection
    projectiveProductToSpec centersComplement).trans projectiveProduct_topologicalKrullDim

theorem surface_regular (x : surface (k := k)) : RegularPoint (surface (k := k)) x := by
  letI := structureMap_smoothTwo (k := k)
  letI : IsSmooth (structureMap (k := k)) := IsSmoothOfRelativeDimension.isSmooth 2 _
  exact SmoothFieldRegularPoints.regularPoints_of_isSmooth_of_dimension_le_two
    structureMap surface_dimension_two.le x

def normalProjectiveSurface : NormalProjectiveSurface k :=
  regularProperSurface surface structureMap surface_regular surface_dimension_two

@[simp] theorem normalProjectiveSurface_toScheme :
    (normalProjectiveSurface (k := k)).toScheme = surface (k := k) := rfl

@[simp] theorem normalProjectiveSurface_structureMorphism :
    (normalProjectiveSurface (k := k)).structureMorphism = structureMap (k := k) := rfl

theorem structureMap_projective : IsProjectiveOverField (structureMap (k := k)) :=
  (normalProjectiveSurface (k := k)).projective

theorem surface_normal : IsNormalScheme (surface (k := k)) :=
  (normalProjectiveSurface (k := k)).normal

instance normalProjectiveSurface_smoothTwo :
    IsSmoothOfRelativeDimension 2 (normalProjectiveSurface (k := k)).structureMorphism :=
  structureMap_smoothTwo

end KltDP.Examples.EqualityAppendixSurface
