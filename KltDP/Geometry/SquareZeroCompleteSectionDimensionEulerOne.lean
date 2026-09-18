import KltDP.Geometry.SquareZeroCompleteSectionDimension
import KltDP.Geometry.SquareZeroNefSectionsEulerOne

/-! The original complete section space has dimension two, and its first
cohomology vanishes, assuming only chi(O)=1 and the original square-zero data. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

include eK in
/-- Riemann–Roch and original point evaluation determine the complete
section space and its first cohomology. -/
theorem squareZero_hZero_eq_two_and_hOne_eq_zero_of_euler_one
    (hchi : eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1)
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 0 = 2 ∧
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 1 = 0 := by
  have hle := X.squareZero_hZero_le_two hX K eK F hF hFF hKF
  have heq := X.squareZero_hZero_eq_hOne_add_two_of_euler_one hX K eK hchi F hF hFF hKF
  omega

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_hZero_eq_two_and_hOne_eq_zero_of_euler_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_hZero_eq_two_and_hOne_eq_zero_of_euler_one
