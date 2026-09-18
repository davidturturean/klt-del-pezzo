import KltDP.Geometry.CartierDivisorPullback

/-!
# Compatibility of the original stalk and function-field maps

Both embeddings into the original function fields are the pinned
stalk-specialization maps. Their commutative square is the naturality of
the original scheme stalk map, with no compatibility hypothesis.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry

variable {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [GenericPointPreserving π]

/-- The original function-field map commutes with the original stalk map
and the canonical fraction-field embeddings at every source point. -/
theorem functionFieldMap_stalk_algebraMap (x : S) (r : X.presheaf.stalk (π.base x)) :
    functionFieldMap π (algebraMap (X.presheaf.stalk (π.base x)) X.functionField r) =
      algebraMap (S.presheaf.stalk x) S.functionField (π.stalkMap x r) := by
  have hX : genericPoint X ⤳ π.base x := (genericPoint_spec X).specializes trivial
  have hS : genericPoint S ⤳ x := (genericPoint_spec S).specializes trivial
  have h : X.presheaf.stalkSpecializes hX ≫ functionFieldMap π =
      π.stalkMap x ≫ S.presheaf.stalkSpecializes hS := by
    rw [functionFieldMap, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact Scheme.stalkSpecializes_stalkMap π (genericPoint S) x hS
  exact ConcreteCategory.congr_hom h r

end KltDP.Geometry
