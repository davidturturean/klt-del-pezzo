import KltDP.Geometry.ProjectiveLineCanonicalTransition
import KltDP.Compatibility.InvertibleTensorUnit
import KltDP.Geometry.ProjectiveLineSections

/-!
# The overlap transition unit of the frames of `Ω_{P¹}`, as a chart evaluation

The atlas `ProjectiveLineCanonicalInvertible.localTrivializations` has, on each standard open, the
over-site unit isomorphism `openChartToOverUnitIso (chartOpen k i) Ω (chartOpenUnitIso k i).symm`
(`localTrivializations_unitIso_hom`), exactly as the accepted point-ideal atlas
(`FrobeniusProjectiveCoordinatePicard.originalAtlas_unitIso_hom`). Hence the overlap restriction of
the transition unit `frameTransitionUnits k ⟨0⟩ ⟨1⟩` is the section obtained by evaluating the
chart-1 trivialisation on `1` and reading the result in the chart-0 trivialisation
(**`frameTransitionUnits_overlap_value`**).

With `ProjectiveLineCanonicalTransition.canonicalDegree_eq_overlapExponent`, the computation of
`deg K_{P¹}` is thereby reduced to evaluating the two chart trivialisations of `Ω_{P¹}` on the
overlap `Spec k[T, T⁻¹]`: the remaining steps are the normalised-frame identifications
(`OpenFrameTransitionCoefficient.normalizedFrameIso`, `coefficient`) with the frames `dt`, `ds` and
the relation `ds = −t⁻² dt` (`baseRingDerivation_inv`); see `F04_CANONICAL_PLAN.md` §4.1.

**Not proved here:** the value of that section (`−T⁻²` in the Laurent ring), hence `deg K_{P¹} = −2`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open KltDP.Geometry.ProjectiveLineComparison KltDP.Geometry.ProjectiveLineTransitionExtension
open KltDP.Geometry.ProjectiveLineSections

universe u

namespace KltDP.Geometry.ProjectiveLineCanonical

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

/-- The over-site unit isomorphism of the frame atlas is the chart trivialisation. -/
theorem localTrivializations_unitIso_hom (i : ULift.{u} (Fin 2)) :
    ((localTrivializations k).unitIso i).hom =
      (openChartToOverUnitIso (standardOpens k i) (cotangent k)
        (chartOpenUnitIso k i.down).symm).inv := by
  simp only [localTrivializations, KltDP.SheafOfModules.LocalTrivializations.unitIso,
    localTrivializationsOfOpenCharts, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem localTrivializations_unitIso_inv (i : ULift.{u} (Fin 2)) :
    ((localTrivializations k).unitIso i).inv =
      (openChartToOverUnitIso (standardOpens k i) (cotangent k)
        (chartOpenUnitIso k i.down).symm).hom :=
  (Iso.inv_eq_inv ((localTrivializations k).unitIso i)
    (openChartToOverUnitIso (standardOpens k i) (cotangent k)
      (chartOpenUnitIso k i.down).symm).symm).mpr (localTrivializations_unitIso_hom k i)

-- The unfolding below exposes the `transitionUnitOn` form syntactically; the recursion depth is
-- raised as in the accepted `ClosedImmersionPushforwardCohomology` and `FrobeniusExceptionalPicardExponent`.
set_option maxRecDepth 4096 in
/-- **The overlap transition unit of the frames is a chart evaluation**: the chart-1 trivialisation
applied to `1`, read back through the chart-0 trivialisation, on the overlap. -/
theorem frameTransitionUnits_overlap_value :
    (overlapRestriction k (frameTransitionUnits k ⟨0⟩ ⟨1⟩) :
      Γ(projectiveSpace k 1, overlapOpen k)) =
      (openChartToOverUnitIso (chartOpen k 0) (cotangent k) (chartOpenUnitIso k 0).symm).inv.val.app
        (op (Over.mk (homOfLE (overlapOpen_le_left k))))
        ((openChartToOverUnitIso (chartOpen k 1) (cotangent k) (chartOpenUnitIso k 1).symm).hom.val.app
          (op (Over.mk (homOfLE (overlapOpen_le_right k))))
            (1 : Γ(projectiveSpace k 1, overlapOpen k))) := by
  unfold overlapRestriction
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, frameTransitionUnits,
    TransitionUnitExtraction.transitionUnits]
  rw [TransitionUnitExtraction.transitionUnitOn_restrict]
  simp only [TransitionUnitExtraction.transitionUnitOn, KltDP.Module.transitionUnit_val,
    TransitionUnitExtraction.chartEquiv_apply, TransitionUnitExtraction.chartEquiv_symm_apply,
    localTrivializations_unitIso_hom, localTrivializations_unitIso_inv]
  rfl

end KltDP.Geometry.ProjectiveLineCanonical
