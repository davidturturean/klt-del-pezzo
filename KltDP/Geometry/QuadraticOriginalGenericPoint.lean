import KltDP.Geometry.OriginalQuadraticSurjective
import KltDP.Geometry.CartierDivisorPullback

/-!
# The actual quadratic projection preserves the original generic point

The image of a generic point is generic in the closure of the image.
Actual surjectivity of the original quadratic projection therefore gives
the generic-point condition needed by the existing Cartier pullback.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- Actual surjectivity between integral schemes gives the Cartier-pullback generic-point condition. -/
theorem genericPointPreserving_of_surjective {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : Function.Surjective f.base) :
    GenericPointPreserving f := by
  constructor
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, Set.range_eq_univ.mpr hf, closure_univ] using
    (genericPoint_spec X).image (show Continuous f.base by fun_prop)

namespace QuadraticCoverAtlas.Data

/-- The original quadratic projection preserves generic points whenever its actual cover is integral. -/
theorem morphism_genericPointPreserving {X : Scheme.{u}} [IsIntegral X]
    {ι : Type u} (D : QuadraticCoverAtlas.Data X ι) [IsIntegral D.scheme] :
    GenericPointPreserving D.morphism := by
  letI := D.morphism_isSurjective
  exact genericPointPreserving_of_surjective D.morphism D.morphism.surjective

end QuadraticCoverAtlas.Data
end KltDP.Geometry

#print axioms KltDP.Geometry.QuadraticCoverAtlas.Data.morphism_genericPointPreserving
