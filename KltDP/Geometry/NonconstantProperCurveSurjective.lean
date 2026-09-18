import KltDP.Geometry.NonconstantCurveGenericPoint
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! An actual nonconstant proper map to the original integral Noetherian
curve is dominant and surjective. Generic-point preservation is supplied
by the existing dimension-one topology theorem, not assumed. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NonconstantProperCurveSurjective

theorem dominant_of_genericPointPreserving
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [GenericPointPreserving f] : IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.mpr
    ⟨genericPoint X, GenericPointPreserving.base_genericPoint⟩)

theorem surjective_of_nonconstant_base
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [NoetherianSpace Y]
    (f : X ⟶ Y) [IsProper f] (hdim : topologicalKrullDim Y ≤ 1)
    (hnonconstant : ¬ ∃ y : Y, ∀ x : X, f.base x = y) :
    GenericPointPreserving f ∧ IsDominant f ∧ Function.Surjective f.base := by
  letI : GenericPointPreserving f :=
    ProperNonconstantCurve.genericPointPreserving_of_nonconstant_base f hdim hnonconstant
  letI : IsDominant f := dominant_of_genericPointPreserving f
  letI : Surjective f :=
    surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  exact ⟨inferInstance, inferInstance, f.surjective⟩

end KltDP.Geometry.NonconstantProperCurveSurjective
