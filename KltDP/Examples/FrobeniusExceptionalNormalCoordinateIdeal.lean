import KltDP.Examples.FrobeniusExceptionalNormal
import KltDP.Examples.FrobeniusProjectiveCoordinatePicard

/-!
# The original exceptional normal and the original coordinate-point ideal

The two original invertible sheaves have the same proved Picard value.
Injectivity of the existing exponent therefore identifies their actual
isomorphism classes, and the original skeleton relation supplies an
actual module-sheaf isomorphism. This is an existence construction; no
frame normalization, Proj twisting-sheaf identity or degree is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusExceptionalNormalCoordinateIdeal

open KltDP.Geometry KltDP.Geometry.AffineBlowup
open FrobeniusBlowupContact FrobeniusExceptionalLine FrobeniusExceptionalNormal
open FrobeniusProjectiveCoordinateIdeal FrobeniusProjectiveCoordinatePicard

variable {k : Type u} [Field k]

/-- The actual normal and actual point ideal represent the same original Picard class. -/
theorem normal_toPic_eq_coordinateIdeal :
    (normalLine (k := k)).toPic = (coordinateIdealLine (k := k)).toPic := by
  apply ProjectiveLinePicardExponent.hom_injective k
  change Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k
      (normalLine (k := k)).toPic) =
    Multiplicative.ofAdd (ProjectiveLinePicardExponent.value k
      (coordinateIdealLine (k := k)).toPic)
  rw [normalPicardValue_eq_neg_one, coordinatePicardValue_eq_neg_one]

/-- Equality of the original skeleton classes gives an actual sheaf isomorphism. -/
theorem normalCoordinateKernel_nonempty :
    Nonempty ((normalLine (k := k)).obj ≅ schemeKernelIdeal (coordinatePoint (k := k))) := by
  letI := Scheme.Modules.monoidalCategory (projectiveSpace k 1)
  have h := congrArg (fun p : (projectiveSpace k 1).Pic =>
    (p : Skeleton (projectiveSpace k 1).Modules)) (normal_toPic_eq_coordinateIdeal (k := k))
  exact Quotient.exact
    ((InvertibleSheaf.toPic_val (normalLine (k := k))).symm.trans
      (h.trans (InvertibleSheaf.toPic_val (coordinateIdealLine (k := k)))))

/-- An actual isomorphism retaining the original exceptional embedding and original point kernel. -/
def normalCoordinateKernelIso :
    (schemeModulePullback (exceptionalProjectiveLineIso (k := k)).inv).obj
        (schemeNormalSheaf (exceptionalι (centerIdeal (k := k)))) ≅
      schemeKernelIdeal (coordinatePoint (k := k)) :=
  Classical.choice (normalCoordinateKernel_nonempty (k := k))

end KltDP.Examples.FrobeniusExceptionalNormalCoordinateIdeal
