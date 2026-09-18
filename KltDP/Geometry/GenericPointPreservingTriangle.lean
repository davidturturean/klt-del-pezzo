import KltDP.Geometry.CartierDivisorPullback

/-!
# Generic-point preservation from an original triangle

This opaque lemma keeps the three scheme maps abstract while evaluating
their actual equation at the original generic point.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.GenericPointPreservingTriangle

variable {T X Y : Scheme.{u}} [IsIntegral T] [IsIntegral X] [IsIntegral Y]
  (a : T ⟶ Y) [GenericPointPreserving a] (c : Y ⟶ X)
  (j : T ⟶ X) [GenericPointPreserving j]

/-- If the first map and the composite preserve generic points, so does the second map. -/
theorem right_of_comp_eq (h : a ≫ c = j) : GenericPointPreserving c := by
  constructor
  have hc := congrArg (fun f : T ⟶ X => f.base (genericPoint T)) h
  change c.base (a.base (genericPoint T)) = j.base (genericPoint T) at hc
  rw [GenericPointPreserving.base_genericPoint (π := a),
    GenericPointPreserving.base_genericPoint (π := j)] at hc
  exact hc

end KltDP.Geometry.GenericPointPreservingTriangle
