import KltDP.Examples.FrobeniusGlobalExceptionalNormalEuler
import KltDP.AdmissionProbe.ProperCohomologyConsumers
import KltDP.Geometry.ProjectiveProper

/-!
# The exceptional normal has Euler difference `-1`, unconditionally

The accepted `FrobeniusGlobalExceptionalNormalEuler` proves that the normal sheaf `O_X(E)|_E` of the
exceptional curve `E` of a global point blowup (`globalExceptionalInclusion A`), pulled to `P¹` along
the accepted exceptional/`P¹` isomorphism, has Euler characteristic difference `-1` against `O_{P¹}`,
with the single premise `hfinite : FiniteDimensional k (H¹(P¹, O))`. This module discharges that
premise: `P¹` is proper over `k` (accepted `projectiveSpaceToSpec_isProper`) and its structure module
is coherent (accepted `unit_isCoherent`), so the accepted proper-cohomology finiteness consumer
(`ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional`, the literal Stacks 02O6 adapter)
gives `projectiveLine_unit_hOne_finiteDimensional`. The Euler difference `-1` — the numerical input
`E² = -1` of F09 for Proposition 10.1's table — is exported unconditionally as
`f09_exceptional_euler_difference`, together with the affine-model and Picard-class forms. No surface
intersection number is asserted: the statement is the degree of `O_X(E)|_E` on `E ≅ P¹` as an Euler
difference.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalEulerUnconditional

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalLine FrobeniusExceptionalNormal
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalNormal
open FrobeniusGlobalExceptionalBase FrobeniusExceptionalNormalEuler
open FrobeniusGlobalExceptionalNormalEuler

variable {k : Type u} [Field k]

/-- `H¹(P¹, O)` is finite-dimensional over `k`: the projective line is proper over `k` and its
structure module is coherent, so the accepted proper-cohomology consumer applies. -/
theorem projectiveLine_unit_hOne_finiteDimensional :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)) := by
  letI : IsCoherentModule (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :=
    unit_isCoherent
  exact KltDP.AdmissionProbe.ProperCohomologyConsumers.proper_baseFunctor_finiteDimensional
    (projectiveSpaceToSpec k 1) _ 1

/-- The affine-model exceptional normal pulled to `P¹` has Euler difference `-1`. -/
theorem normal_euler_difference_eq_neg_one' :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
          (schemeNormalSheaf (exceptionalι (centerIdeal (k := k))))) -
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = -1 :=
  normal_euler_difference_eq_neg_one projectiveLine_unit_hOne_finiteDimensional

/-- The same difference on the normal Picard class. -/
theorem normal_picardEuler_difference_eq_neg_one' :
    picardEulerValue (projectiveSpaceToSpec k 1) (normalLine (k := k)).toPic -
      picardEulerValue (projectiveSpaceToSpec k 1) (1 : (projectiveSpace k 1).Pic) = -1 :=
  normal_picardEuler_difference_eq_neg_one projectiveLine_unit_hOne_finiteDimensional

/-- The global exceptional normal of a point blowup, pulled to `P¹`, has Euler difference `-1`. -/
theorem globalNormalOnProjectiveLine_euler_difference_eq_neg_one' (A : PlaneChartedScheme k) :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePullback (globalExceptionalProjectiveLineIso A).inv).obj
          (schemeNormalSheaf (globalExceptionalInclusion A))) -
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = -1 :=
  globalNormalOnProjectiveLine_euler_difference_eq_neg_one A
    projectiveLine_unit_hOne_finiteDimensional

end KltDP.Examples.FrobeniusExceptionalEulerUnconditional

namespace KltDP.Examples

open KltDP.Geometry KltDP.Geometry.ModuleCohomology
open FrobeniusExceptionalNormal FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalNormal
open FrobeniusGlobalExceptionalBase FrobeniusExceptionalEulerUnconditional

/-- **F09 numerical input**: for the point blowup of any plane-charted scheme `A` at the selected
point, the normal sheaf `O_X(E)|_E` of the exceptional curve `E`, pulled to `P¹` along the accepted
exceptional/`P¹` isomorphism, has Euler characteristic difference `-1` against `O_{P¹}` — the degree
`E² = -1` — with no finiteness premise. -/
theorem f09_exceptional_euler_difference (k : Type u) [Field k] (A : PlaneChartedScheme k) :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePullback (globalExceptionalProjectiveLineIso A).inv).obj
          (schemeNormalSheaf (globalExceptionalInclusion A))) -
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = -1 :=
  globalNormalOnProjectiveLine_euler_difference_eq_neg_one' A

/-- The bundle has exactly one universe parameter. -/
theorem f09_exceptional_euler_difference_universe_check (k : Type u) [Field k]
    (A : PlaneChartedScheme k) : True := by
  have _ := f09_exceptional_euler_difference.{u} k A
  trivial

end KltDP.Examples
