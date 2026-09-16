import KltDP.Geometry.RationalPointPushforwardCohomology
import KltDP.Geometry.SurfaceCohomologyVanishing
import KltDP.Geometry.ProjectivePlane
import KltDP.Geometry.ProjectiveProper
import KltDP.Geometry.StructureSheafHZeroFinite
import KltDP.Geometry.InvertibleCoherentModule
import KltDP.Examples.FrobeniusCoordinateIdealEuler
import KltDP.Examples.FrobeniusExceptionalNormalCoordinateIdeal

/-!
# The original coordinate ideal and exceptional normal have Euler difference -1

Only finite-dimensionality of the original H1 of the structure sheaf on P1
is retained as an input. Its H0 is finite by the existing proper integral
global-functions theorem. The original ideal sequence and point cohomology
then prove finiteness for the ideal; the existing dimension bound handles
every degree above one. Euler additivity gives the numerical difference.

The existing actual normal-to-point-kernel isomorphism transports the result
on P1. Its source is the pullback of the original exceptional normal along
the original exceptional/P1 isomorphism. No cohomology comparison between
different schemes, intrinsic degree definition, or surface intersection
formula is asserted. Stacks 02O6 is not admitted or used by this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalNormalEuler

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalLine FrobeniusExceptionalNormal
open FrobeniusProjectiveCoordinateIdeal FrobeniusProjectiveCoordinatePicard
open FrobeniusCoordinateIdealEuler FrobeniusExceptionalNormalCoordinateIdeal

variable {k : Type u} [Field k]

/-- The existing projective dimension and Noetherian topology give the
ordinary cohomology bound for every actual module on P1. -/
theorem cohomology_subsingleton_above_one (M : (projectiveSpace k 1).Modules)
    (n : ℕ) (hn : 1 < n) : Subsingleton (H M n) := by
  letI := projectiveSpace_noetherianSpace k 1
  apply scheme_H_subsingleton_of_dimension_lt (projectiveSpace k 1) M n
  rw [projectiveSpace_topologicalKrullDim]
  exact_mod_cast hn

/-- Once its two low degrees are finite, every actual cohomology group is
finite for the same original structure-map action. -/
theorem cohomology_finite_of_zero_one (M : (projectiveSpace k 1).Modules)
    (hzero : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 0).obj M))
    (hone : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj M))
    (n : ℕ) :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj M) := by
  cases n with
  | zero => exact hzero
  | succ n =>
      cases n with
      | zero => exact hone
      | succ n =>
          letI := baseModule (projectiveSpaceToSpec k 1) M (n + 1 + 1)
          letI : Subsingleton
              ((baseFunctor (projectiveSpaceToSpec k 1) (n + 1 + 1)).obj M) :=
            cohomology_subsingleton_above_one M (n + 1 + 1) (by omega)
          exact Module.Finite.of_surjective
            (0 : k →ₗ[k] H M (n + 1 + 1)) (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- Actual H0 of the structure module is already finite, over every field. -/
theorem unit_hZero_finiteDimensional :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 0).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)) := by
  letI := projectiveSpace_isIntegral k 1
  exact StructureSheafCohomology.hZero_moduleFinite (projectiveSpaceToSpec k 1)

/-- Only the original H1 finiteness is needed for all structure-sheaf degrees. -/
theorem unit_cohomology_finiteDimensional
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) (n : ℕ) :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf)) :=
  cohomology_finite_of_zero_one _ unit_hZero_finiteDimensional hfinite n

/-- H0 of the original ideal injects into the already finite H0 of O. -/
theorem coordinateIdeal_hZero_finiteDimensional :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 0).obj
      (coordinateIdealLine (k := k)).obj) := by
  letI : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 0).obj
      (coordinateIdealSequence (k := k)).X₂) := unit_hZero_finiteDimensional (k := k)
  exact FiniteDimensional.of_injective
    (((baseFunctor (projectiveSpaceToSpec k 1) 0).map
      (coordinateIdealSequence (k := k)).f).hom)
    (baseMap_zero_injective (projectiveSpaceToSpec k 1)
      coordinateIdealSequence coordinateIdealSequence_shortExact)

/-- In the original LES, H0 of the point and H1 of O are finite endpoints
around H1 of the ideal. The pinned exact-sequence Noetherian result applies. -/
theorem coordinateIdeal_hOne_finiteDimensional
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (coordinateIdealLine (k := k)).obj) := by
  let S := coordinateIdealSequence (k := k)
  have hS : S.ShortExact := coordinateIdealSequence_shortExact
  letI : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 0).obj S.X₃) :=
    RationalPointPushforward.cohomology_finiteDimensional coordinatePoint
      (projectiveSpaceToSpec k 1)
      (FrobeniusProjectivePoints.pointMorphism_over_base (0 : k)) 0
  letI : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj S.X₂) :=
    hfinite
  letI : IsNoetherian k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj S.X₁) :=
    isNoetherian_of_range_eq_ker
      (baseConnectingArrow (projectiveSpaceToSpec k 1) S hS 0).hom
      (((baseFunctor (projectiveSpaceToSpec k 1) 1).map S.f).hom)
      (LinearMap.exact_iff.mp
        (baseExact_after_connecting (projectiveSpaceToSpec k 1) S hS 0)).symm
  exact Module.IsNoetherian.finite k
    ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj S.X₁)

/-- All original ideal cohomology is finite from the single H1(O) premise. -/
theorem coordinateIdeal_cohomology_finiteDimensional
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) (n : ℕ) :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj
      (coordinateIdealLine (k := k)).obj) :=
  cohomology_finite_of_zero_one _ coordinateIdeal_hZero_finiteDimensional
    (coordinateIdeal_hOne_finiteDimensional hfinite) n

/-- The existing actual point sequence has numerical Euler difference -1. -/
theorem coordinateIdeal_euler_difference_eq_neg_one
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) :
    eulerCharacteristic (projectiveSpaceToSpec k 1) (coordinateIdealLine (k := k)).obj -
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = -1 := by
  have h := coordinateIdeal_euler_difference (k := k) 1
    (coordinateIdeal_cohomology_finiteDimensional hfinite)
    (unit_cohomology_finiteDimensional hfinite)
    (RationalPointPushforward.cohomology_finiteDimensional coordinatePoint
      (projectiveSpaceToSpec k 1)
      (FrobeniusProjectivePoints.pointMorphism_over_base (0 : k)))
    (cohomology_subsingleton_above_one _)
    (cohomology_subsingleton_above_one _)
    (fun n hn => RationalPointPushforward.cohomology_subsingleton_of_pos
      coordinatePoint n (by omega))
  rw [picardEulerValue_toPic, picardEulerValue_one,
    RationalPointPushforward.eulerCharacteristic_eq_one coordinatePoint
      (projectiveSpaceToSpec k 1)
      (FrobeniusProjectivePoints.pointMorphism_over_base (0 : k))] at h
  exact h

/-- The actual normal on P1 inherits finiteness through its original kernel iso. -/
theorem normal_cohomology_finiteDimensional
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) (n : ℕ) :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj
      (normalLine (k := k)).obj) := by
  letI : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj
      (schemeKernelIdeal (coordinatePoint (k := k)))) :=
    coordinateIdeal_cohomology_finiteDimensional hfinite n
  exact Module.Finite.equiv
    (((baseFunctor (projectiveSpaceToSpec k 1) n).mapIso
      (normalCoordinateKernelIso (k := k)).symm).toLinearEquiv)

/-- The original exceptional normal, pulled to the original P1, has the
same numerical Euler difference. The actual embedding and map stay visible. -/
theorem normal_euler_difference_eq_neg_one
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
          (schemeNormalSheaf (exceptionalι (centerIdeal (k := k))))) -
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = -1 := by
  calc
    _ = eulerCharacteristic (projectiveSpaceToSpec k 1) (coordinateIdealLine (k := k)).obj -
        eulerCharacteristic (projectiveSpaceToSpec k 1)
          (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :=
      congrArg (fun z : ℤ => z - eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))
        (eulerCharacteristic_eq_of_iso (projectiveSpaceToSpec k 1)
          (normalCoordinateKernelIso (k := k)))
    _ = -1 := coordinateIdeal_euler_difference_eq_neg_one hfinite

/-- The same difference expressed on the original normal Picard class. -/
theorem normal_picardEuler_difference_eq_neg_one
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) :
    picardEulerValue (projectiveSpaceToSpec k 1) (normalLine (k := k)).toPic -
      picardEulerValue (projectiveSpaceToSpec k 1) (1 : (projectiveSpace k 1).Pic) = -1 := by
  rw [picardEulerValue_toPic, picardEulerValue_one]
  exact normal_euler_difference_eq_neg_one hfinite

/-- The structure module satisfies the literal coherence predicate. -/
theorem unit_isCoherent :
    IsCoherentModule (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) := by
  letI := projectiveSpace_isLocallyNoetherian k 1
  infer_instance

/-- The original coordinate ideal is coherent through its proved invertibility. -/
theorem coordinateIdeal_isCoherent : IsCoherentModule (coordinateIdealLine (k := k)).obj := by
  letI := projectiveSpace_isLocallyNoetherian k 1
  exact (coordinateIdealLine (k := k)).isCoherent

/-- The original normal on P1 is likewise coherent. -/
theorem normal_isCoherent : IsCoherentModule (normalLine (k := k)).obj := by
  letI := projectiveSpace_isLocallyNoetherian k 1
  exact (normalLine (k := k)).isCoherent

end KltDP.Examples.FrobeniusExceptionalNormalEuler
