import KltDP.Geometry.CartierDivisorPullback
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
The original generic point is preserved by a dominant morphism of
integral schemes. This uses the pinned topological generic-point image
theorem and the original dense range, without a function-field premise.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

/-- Dominance supplies the original generic-point equality. -/
theorem genericPointPreserving_of_isDominant {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    GenericPointPreserving f := by
  constructor
  apply ((genericPoint_spec Y).eq _).symm
  have h := (genericPoint_spec X).image (show Continuous f.base by fun_prop)
  rwa [Set.image_univ, f.denseRange.closure_range] at h

end KltDP.Geometry
