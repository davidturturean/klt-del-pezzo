import KltDP.Geometry.SquareZeroPicardPrimitive
import KltDP.Geometry.NegativeNefCartierPowers

/-! The original nef square-zero divisor has h0(F)=h1(F)+2 as soon
as the original structure sheaf has Euler characteristic one. The proof
uses actual nefness and Cartier Riemann–Roch. -/

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
/-- Original nefness and the two literal intersections give the exact RR
section-dimension identity when the original Euler characteristic is one. -/
theorem squareZero_hZero_eq_hOne_add_two_of_euler_one
    (hchi : eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1)
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 0 =
      cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 1 + 2 := by
  have hneg : X.intersectionPairing hX (K - F) F < 0 := by
    rw [sub_eq_add_neg, X.intersectionPairing_add_left hX,
      X.intersectionPairing_neg_left hX, hKF, hFF]
    norm_num
  have hz : cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (K - F)) 0 = 0 := by
    simpa only [one_smul] using
      NegativeNefCartierPowers.hZero_positive_multiple_eq_zero X hX (K - F) F
        hF hneg 1 Nat.one_pos
  have hinter : X.intersectionPairing hX F (F - K) = 2 := by
    rw [sub_eq_add_neg, X.intersectionPairing_add_right hX,
      X.intersectionPairing_neg_right hX, hFF,
      X.intersectionPairing_symm hX F K, hKF]
    norm_num
  have hrr := X.cartier_riemannRoch hX K eK F
  rw [hz, hinter, hchi] at hrr
  have heq : (cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme F) 0 : ℚ) =
      (cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme F) 1 : ℚ) + 2 := by
    norm_num at hrr
    linarith only [hrr]
  exact_mod_cast heq

include eK in
/-- The original complete system has at least two independent section dimensions. -/
theorem squareZero_two_le_hZero_of_euler_one
    (hchi : eulerCharacteristic X.structureMorphism
      (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) = 1)
    (F : CartierDivisor X.toScheme)
    (hF : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme F))
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2) :
    2 ≤ cohomologyDimension X.structureMorphism (cartierDivisorModule X.toScheme F) 0 := by
  rw [X.squareZero_hZero_eq_hOne_add_two_of_euler_one hX K eK hchi F hF hFF hKF]
  omega

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_hZero_eq_hOne_add_two_of_euler_one
#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_two_le_hZero_of_euler_one
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_two_le_hZero_of_euler_one
