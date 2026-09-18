import KltDP.Geometry.NegativeNefCanonicalLinePowers

/-! All original Cartier multiples vanish under the actual nef-line sign. -/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Geometry.NegativeNefCanonicalTensorPowers

/-- This original divisor-sheaf version matches the full published
pluricanonical-vanishing criterion without changing the original K. -/
theorem hZero_multiple_of_negative_nef_line
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
    (D : CartierDivisor X.toScheme) (H : InvertibleSheaf X.toScheme)
    (hH : Positivity.IsNef X.structureMorphism H)
    (hnegative : X.picardPairing hX (cartierPicardClass X.toScheme D) H.toPic < 0)
    (n : ℕ) (hn : 0 < n) :
    cohomologyDimension X.structureMorphism
      (cartierDivisorModule X.toScheme (n • D)) 0 = 0 := by
  let A := X.picardRepresentative H.toPic
  have hclass : cartierPicardClass X.toScheme A = H.toPic :=
    X.cartierPicardClass_picardRepresentative H.toPic
  have hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A) :=
    NefPositiveSelfIntersectionBig.isNef_of_toPic_eq X hclass.symm hH
  have hDA : X.intersectionPairing hX D A < 0 := by
    rw [← X.picardPairing_class hX D A, hclass]
    exact hnegative
  exact NegativeNefCartierPowers.hZero_positive_multiple_eq_zero X hX D A hA hDA n hn

end KltDP.Geometry.NegativeNefCanonicalTensorPowers
#print axioms KltDP.Geometry.NegativeNefCanonicalTensorPowers.hZero_multiple_of_negative_nef_line
