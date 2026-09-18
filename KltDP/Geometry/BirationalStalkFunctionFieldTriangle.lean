import KltDP.Geometry.BirationalFunctionFieldStalkAlgebra

/-!
# The original stalk map and original function-field map commute

This is pinned stalk-generization naturality, with the original
generic-point transport in functionFieldMap retained explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalStalkFunctionFieldTriangle

variable {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ X) [GenericPointPreserving π]

/-- The literal stalk-ring map commutes with the original generizations
to the two function fields. No map compatibility is assumed. -/
theorem stalkMap_to_functionField (y : S) (a : X.presheaf.stalk (π.base y)) :
    algebraMap (S.presheaf.stalk y) S.functionField (π.stalkMap y a) =
      functionFieldMap π
        (algebraMap (X.presheaf.stalk (π.base y)) X.functionField a) := by
  have h : π.stalkMap y ≫
        S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes trivial) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫
        functionFieldMap π := by
    unfold functionFieldMap
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact (Scheme.stalkSpecializes_stalkMap π (genericPoint S) y
      ((genericPoint_spec S).specializes trivial)).symm
  exact congrArg (fun g : X.presheaf.stalk (π.base y) ⟶ S.functionField => g a) h

end KltDP.Geometry.BirationalStalkFunctionFieldTriangle
