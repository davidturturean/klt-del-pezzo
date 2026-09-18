import KltDP.Geometry.SurfaceGenericFiberDimensionOne
import KltDP.Geometry.ProperIntegralCurveEulerOne
import KltDP.Geometry.FiberEulerFunction

/-! Euler characteristic one gives exact dimension one for the original
generic fiber. The scalar isomorphism is derived from the actual Euler
value using only the already-proved dimension-at-most-one bound. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.SurfaceGenericFiberDimensionOne

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance line_integral_euler : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

theorem dimension_eq_one_of_eulerCharacteristic_eq_one
    (f : S.toScheme ⟶ projectiveSpace k 1) [IsProper f] [IsDominant f]
    (hχ : ModuleCohomology.eulerCharacteristic
      (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1)))
      (SheafOfModules.unit
        (f.fiber (genericPoint (projectiveSpace k 1))).ringCatSheaf) = 1) :
    topologicalKrullDim (f.fiber (genericPoint (projectiveSpace k 1))) = 1 := by
  letI : IsIntegral (f.fiber (genericPoint (projectiveSpace k 1))) :=
    GenericFiberIntegral.isIntegral f
  letI : IsProper (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hdim := GenericSurfaceFiberDimensionBound.dimension_le_one f S.dimension_two.le
    (by simpa using projectiveSpace_topologicalKrullDim k 1)
  letI : IsIso ((Scheme.ΓSpecIso
      ((projectiveSpace k 1).residueField (genericPoint (projectiveSpace k 1)))).inv ≫
        (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))).appTop) :=
    ProperIntegralCurveEulerOne.globalScalar_isIso
      (f.fiberToSpecResidueField (genericPoint (projectiveSpace k 1))) hdim hχ
  exact dimension_eq_one S f

theorem dimension_eq_one_of_fiberEuler_eq_one
    (f : S.toScheme ⟶ projectiveSpace k 1) [IsProper f] [IsDominant f]
    (hχ : fiberEuler f (SheafOfModules.unit S.toScheme.ringCatSheaf)
      (genericPoint (projectiveSpace k 1)) = 1) :
    topologicalKrullDim (f.fiber (genericPoint (projectiveSpace k 1))) = 1 := by
  apply dimension_eq_one_of_eulerCharacteristic_eq_one S f
  exact (fiberEuler_unit f (genericPoint (projectiveSpace k 1))).symm.trans hχ

#print axioms dimension_eq_one_of_eulerCharacteristic_eq_one
#print axioms dimension_eq_one_of_fiberEuler_eq_one

end KltDP.Geometry.SurfaceGenericFiberDimensionOne
