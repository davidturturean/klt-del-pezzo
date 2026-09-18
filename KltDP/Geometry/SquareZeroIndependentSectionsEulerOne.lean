import KltDP.Geometry.SquareZeroNefSectionsEulerOne
import KltDP.Geometry.CartierIndependentSectionRatio

/-! Euler characteristic one and the original square-zero numerical
data supply two actual independent sections of O(F). -/

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
  (hchi : eulerCharacteristic X.structureMorphism
    (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1)

local instance squareZeroEulerOneIndependentIntegral : IsIntegral X.toScheme := X.integral

include eK hchi in
/-- The two actual sections use precisely the original cohomological
base-field scalar action. -/
theorem exists_two_independent_sections_of_nef_squareZero_of_euler_one (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme F)
    ∃ s : Fin 2 → sections (cartierDivisorModule X.toScheme F), LinearIndependent k s := by
  letI := baseSectionsModule X.structureMorphism (cartierDivisorModule X.toScheme F)
  have hdim := X.squareZero_two_le_hZero_of_euler_one hX K eK hchi F hF hFF hKF
  rw [cohomologyDimension_zero_eq_finrank_sections] at hdim
  exact exists_linearIndependent_of_le_finrank hdim

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.exists_two_independent_sections_of_nef_squareZero_of_euler_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_two_independent_sections_of_nef_squareZero_of_euler_one
