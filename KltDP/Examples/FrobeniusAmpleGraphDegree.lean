import KltDP.Geometry.AmpleSerreDegreeBound
import KltDP.Examples.FrobeniusGraphFirstFiberDegree
import KltDP.Examples.FrobeniusStageOneProjective

/-!
# Ample sheaves have positive degree on the actual strict graph curves

The first fibre class has degree one on each actual strict graph curve,
by the geometric local-length computation. If an ample sheaf had degree
zero there, the Serre degree bound would force that same first fibre degree
to be zero. Ample implies nef, so exclusion of zero gives strict positivity.

There is no assumed positive-degree test class: its value one is proved
for the original geometric fibre class. General contact stages retain their
projectivity hypothesis. At stage one, the independently proved projective
embedding discharges this hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusAmpleGraphDegree

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformPairing
open FrobeniusGraphFirstFiberDegree FrobeniusStageOneProjective

variable {k : Type u} [Field k] [IsAlgClosed k] (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- Strict positivity on the actual strict graph, with the geometric
degree-one fibre row discharged by its proved local intersection calculation. -/
theorem graphStrict_restrictionDegree_pos (m : ℕ)
    (L : InvertibleSheaf (stageSurface (n + 1) hproj).toScheme)
    (hL : AmpleSerre.IsAmple L) :
    0 < (graphStrictPrimeCurve n hproj m).restrictionDegree L := by
  have hnef := AmpleNefUnconditional.isNef_of_isAmple (stageSurface (n + 1) hproj) L hL
  rw [Positivity.isNef_iff_forall_primeCurve] at hnef
  by_contra hnot
  have hzero : (graphStrictPrimeCurve n hproj m).restrictionDegree L = 0 :=
    le_antisymm (le_of_not_gt hnot) (hnef (graphStrictPrimeCurve n hproj m))
  have hvan := AmpleSerreDegreeBound.picardRestrictionDegree_eq_zero_of_ample_degree_zero
    (stageSurface (n + 1) hproj) L hL (graphStrictPrimeCurve n hproj m) hzero
    (firstFiberTotalClass (k := k) (n + 1)).toMul
  have hone := graphStrictPairing_firstFiberTotalClass_eq_one (k := k) n hproj m
  change (graphStrictPrimeCurve n hproj m).picardRestrictionDegree
    (firstFiberTotalClass (k := k) (n + 1)).toMul = 1 at hone
  rw [hvan] at hone
  exact zero_ne_one hone

/-- At the first actual blowup stage, no projectivity premise remains. -/
theorem stageOne_graph_restrictionDegree_pos (m : ℕ)
    (L : InvertibleSheaf (stageOneSurface (k := k)).toScheme)
    (hL : AmpleSerre.IsAmple L) :
    0 < (graphStrictPrimeCurve 0 (stage_one_projective (k := k)) m).restrictionDegree L :=
  graphStrict_restrictionDegree_pos 0 stage_one_projective m L hL

end KltDP.Examples.FrobeniusAmpleGraphDegree
