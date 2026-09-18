import KltDP.Geometry.SquareZeroPencilFiberEuler
import KltDP.Geometry.ClosedPointFiberEulerTransport

/-! The original square-zero pencil's residue-field Euler function is one
at every closed point. This is exactly the native fiber value used by
flat-family Euler local constancy, with its scalar dictionary discharged. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
local instance residueEulerSourceIntegral : IsIntegral X.toScheme := X.integral
local instance residueEulerTargetIntegral : IsIntegral (projectiveSpace k 1) :=
  projectiveSpace_isIntegral k 1

/-- The native residue-field Euler value of each original closed fiber. -/
theorem squareZero_closedResidueFiber_eulerCharacteristic_eq_one
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (F : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (π : X.toScheme ⟶ projectiveSpace k 1) [GenericPointPreserving π] [QuasiCompact π]
    (hπ : π ≫ projectiveSpaceToSpec k 1 = X.structureMorphism)
    (eF : (pullbackInvertibleSheaf π
      (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
        cartierDivisorModule X.toScheme F)
    (x : projectiveSpace k 1) (hclosed : IsClosed ({x} : Set (projectiveSpace k 1))) :
    eulerCharacteristic (π.fiberToSpecResidueField x)
      (_root_.SheafOfModules.unit (π.fiber x).ringCatSheaf) = 1 := by
  rw [ClosedPointFiberEulerTransport.eulerCharacteristic_eq π (projectiveSpaceToSpec k 1) x hclosed]
  exact X.squareZero_pencil_closedFiber_eulerCharacteristic_eq_one hX K eK F hFF hKF π hπ eF x hclosed

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_closedResidueFiber_eulerCharacteristic_eq_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_closedResidueFiber_eulerCharacteristic_eq_one
