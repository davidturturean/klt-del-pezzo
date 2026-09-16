import KltDP.Examples.FrobeniusGlobalExceptionalBase
import KltDP.Examples.FrobeniusExceptionalNormalEuler

/-!
# Euler difference for the original global exceptional normal pulled to P1

The original global normal is pulled along the inverse of the constructed
global exceptional/P1 isomorphism. Pullback composition and the proved
global-to-affine normal comparison identify that actual module with the
original affine exceptional normal already pulled to P1. All subsequent
cohomology and Euler comparisons take place on this single original P1,
with its original coefficient-field action.

Only finite-dimensionality of the original H1 of O on P1 remains a premise.
No cohomology transport between different schemes, degree definition, or
surface self-intersection formula is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusGlobalExceptionalNormalEuler

open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalLine FrobeniusExceptionalNormal
open FrobeniusGlobalBlowupStages FrobeniusGlobalExceptionalNormal
open FrobeniusGlobalExceptionalBase FrobeniusExceptionalNormalEuler

variable {k : Type u} [Field k] (A : PlaneChartedScheme k)

/-- The original global normal, pulled to P1, is the already computed original affine normal. -/
def globalNormalOnProjectiveLineIso :
    (schemeModulePullback (globalExceptionalProjectiveLineIso A).inv).obj
        (schemeNormalSheaf (globalExceptionalInclusion A)) ≅
      (schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
        (schemeNormalSheaf (exceptionalι (centerIdeal (k := k)))) :=
  ((schemeModulePullbackCompIso (exceptionalProjectiveLineIso (k := k)).inv
    (affineExceptionalIso A).hom).app
      (schemeNormalSheaf (globalExceptionalInclusion A))).symm ≪≫
    (schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).mapIso
      (globalNormalPullbackIso A)

/-- Finiteness transfers on the same P1 using its same original field action. -/
theorem globalNormalOnProjectiveLine_cohomology_finiteDimensional
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) (n : ℕ) :
    FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj
      ((schemeModulePullback (globalExceptionalProjectiveLineIso A).inv).obj
        (schemeNormalSheaf (globalExceptionalInclusion A)))) := by
  letI : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) n).obj
      ((schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
        (schemeNormalSheaf (exceptionalι (centerIdeal (k := k)))))) :=
    normal_cohomology_finiteDimensional hfinite n
  exact Module.Finite.equiv
    (((baseFunctor (projectiveSpaceToSpec k 1) n).mapIso
      (globalNormalOnProjectiveLineIso A).symm).toLinearEquiv)

/-- The existing P1 bound applies to the actual pulled global normal. -/
theorem globalNormalOnProjectiveLine_cohomology_subsingleton_above_one
    (n : ℕ) (hn : 1 < n) :
    Subsingleton (H ((schemeModulePullback (globalExceptionalProjectiveLineIso A).inv).obj
      (schemeNormalSheaf (globalExceptionalInclusion A))) n) :=
  cohomology_subsingleton_above_one _ n hn

/-- The original global normal pulled to P1 has Euler difference -1, with only H1(O) finiteness. -/
theorem globalNormalOnProjectiveLine_euler_difference_eq_neg_one
    (hfinite : FiniteDimensional k ((baseFunctor (projectiveSpaceToSpec k 1) 1).obj
      (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))) :
    eulerCharacteristic (projectiveSpaceToSpec k 1)
        ((schemeModulePullback (globalExceptionalProjectiveLineIso A).inv).obj
          (schemeNormalSheaf (globalExceptionalInclusion A))) -
      eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) = -1 := by
  calc
    _ = eulerCharacteristic (projectiveSpaceToSpec k 1)
          ((schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
            (schemeNormalSheaf (exceptionalι (centerIdeal (k := k))))) -
        eulerCharacteristic (projectiveSpaceToSpec k 1)
          (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf) :=
      congrArg (fun z : ℤ => z - eulerCharacteristic (projectiveSpaceToSpec k 1)
        (_root_.SheafOfModules.unit (projectiveSpace k 1).ringCatSheaf))
        (eulerCharacteristic_eq_of_iso (projectiveSpaceToSpec k 1)
          (globalNormalOnProjectiveLineIso A))
    _ = -1 := normal_euler_difference_eq_neg_one hfinite

end KltDP.Examples.FrobeniusGlobalExceptionalNormalEuler
