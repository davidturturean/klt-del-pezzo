import KltDP.Geometry.GenericFiberIntegral
import KltDP.Geometry.GenericFiberRegular
import KltDP.Geometry.GenericSurfaceFiberDimensionBound
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper

/-! The native generic-fiber geometry of an actual dominant map from the
original regular projective surface to the original projective line. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace KltDP.Geometry.SurfaceProjectiveLineGenericFiber

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance line_integral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

theorem structure_triangle
    (f : S.toScheme ⟶ projectiveSpace k 1)
    (hf : f ≫ projectiveSpaceToSpec k 1 = S.structureMorphism) :
    f.fiberι (genericPoint (projectiveSpace k 1)) ≫ S.structureMorphism =
      f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1)) ≫
        ((projectiveSpace k 1).fromSpecResidueField
          (genericPoint (projectiveSpace k 1)) ≫ projectiveSpaceToSpec k 1) := by
  rw [← hf, ← Category.assoc]
  change (pullback.fst _ _ ≫ f) ≫ projectiveSpaceToSpec k 1 = _
  rw [pullback.condition, Category.assoc]
  rfl

theorem geometry
    (hS : ∀ x : S.Point, RegularPoint S.toScheme x)
    (f : S.toScheme ⟶ projectiveSpace k 1) [IsDominant f]
    (hf : f ≫ projectiveSpaceToSpec k 1 = S.structureMorphism) :
    IsIntegral (f.fiber (genericPoint (projectiveSpace k 1))) ∧
      IsProper (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) ∧
      (∀ x : f.fiber (genericPoint (projectiveSpace k 1)),
        RegularPoint (f.fiber (genericPoint (projectiveSpace k 1))) x) ∧
      topologicalKrullDim (f.fiber (genericPoint (projectiveSpace k 1))) ≤ 1 := by
  letI : IsProper (f ≫ projectiveSpaceToSpec k 1) := by rw [hf]; infer_instance
  letI : IsProper f := IsProper.of_comp_of_isSeparated f (projectiveSpaceToSpec k 1)
  have hp : IsProper (f.fiberToSpecResidueField
      (genericPoint (projectiveSpace k 1))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact ⟨GenericFiberIntegral.isIntegral f, hp, GenericFiberRegular.regularPoints f hS,
    GenericSurfaceFiberDimensionBound.dimension_le_one f S.dimension_two.le
      (by simpa using projectiveSpace_topologicalKrullDim k 1)⟩

#print axioms geometry
#print axioms structure_triangle

end KltDP.Geometry.SurfaceProjectiveLineGenericFiber
