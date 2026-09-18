import KltDP.Geometry.ZeroDimensionalIntegralScalarIso
import KltDP.Geometry.GenericFiberIsomorphismBirational
import KltDP.Geometry.GenericFiberIntegral
import KltDP.Geometry.GenericSurfaceFiberDimensionBound
import KltDP.Geometry.ProperBirationalDimension
import KltDP.Geometry.ProjectivePlane

/-! The original generic fiber has dimension one when its original global
scalar arrow is an isomorphism. Algebraic closedness concerns only the
original ground field, as in the existing proper-birational dimension theorem. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SurfaceGenericFiberDimensionOne

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance line_integral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

theorem one_le
    (f : S.toScheme ⟶ projectiveSpace k 1) [IsProper f] [IsDominant f]
    [hscalar : IsIso ((Scheme.ΓSpecIso
      ((projectiveSpace k 1).residueField (genericPoint (projectiveSpace k 1)))).inv ≫
        (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))).appTop)] :
    1 ≤ topologicalKrullDim (f.fiber (genericPoint (projectiveSpace k 1))) := by
  let F := f.fiber (genericPoint (projectiveSpace k 1))
  letI : IsIntegral F := GenericFiberIntegral.isIntegral f
  letI : Nonempty (IrreducibleCloseds F) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ F, isClosed_univ⟩⟩
  have hnonneg : 0 ≤ topologicalKrullDim F := Order.krullDim_nonneg
  apply (WithBot.one_le_iff_pos _).mpr
  apply lt_of_not_ge
  intro hnonpos
  have hzero : topologicalKrullDim F = 0 := le_antisymm hnonpos hnonneg
  letI : IsIso (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) :=
    @ZeroDimensionalIntegralScalarIso.structureMap_isIso F inferInstance
      ((projectiveSpace k 1).residueField (genericPoint (projectiveSpace k 1)))
      inferInstance (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1)))
      hzero hscalar
  have hbir := GenericFiberIsomorphismBirational.isBirationalScheme f
  have hbad := target_dimension_two_of_proper_birational S f
    (projectiveSpaceToSpec k 1) hbir
  rw [projectiveSpace_topologicalKrullDim] at hbad
  norm_num at hbad

theorem dimension_eq_one
    (f : S.toScheme ⟶ projectiveSpace k 1) [IsProper f] [IsDominant f]
    [IsIso ((Scheme.ΓSpecIso
      ((projectiveSpace k 1).residueField (genericPoint (projectiveSpace k 1)))).inv ≫
        (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))).appTop)] :
    topologicalKrullDim (f.fiber (genericPoint (projectiveSpace k 1))) = 1 := by
  apply le_antisymm
  · exact GenericSurfaceFiberDimensionBound.dimension_le_one f S.dimension_two.le
      (by simpa using projectiveSpace_topologicalKrullDim k 1)
  · exact one_le S f

#print axioms one_le
#print axioms dimension_eq_one

end KltDP.Geometry.SurfaceGenericFiberDimensionOne
