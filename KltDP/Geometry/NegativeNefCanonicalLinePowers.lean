import KltDP.Geometry.NegativeNefCanonicalTensorPowers
import KltDP.Geometry.NefPositiveSelfIntersectionBig

/-! Vanishing from the original nef line and its actual canonical pairing. -/
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u
namespace KltDP.Geometry.NegativeNefCanonicalTensorPowers
open InvertibleSheafSectionPowers SmoothSurfaceKaehlerAtlas SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance originalCanonicalLineIntegral : IsIntegral X.toScheme := X.integral

/-- The original nef line need not be supplied with a Cartier model.
The existing representative construction transports its actual class. -/
theorem canonicalTensorPower_hZero_of_negative_nef_line
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (H : InvertibleSheaf X.toScheme)
    (hH : Positivity.IsNef X.structureMorphism H)
    (hnegative : X.picardPairing hregular
      (cartierPicardClass X.toScheme K) H.toPic < 0)
    (n : ℕ) (hn : 0 < n) :
    cohomologyDimension X.structureMorphism
      (power (canonicalSheafOfSmoothSurface X.structureMorphism) n).obj 0 = 0 := by
  let A := X.picardRepresentative H.toPic
  have hclass : cartierPicardClass X.toScheme A = H.toPic :=
    X.cartierPicardClass_picardRepresentative H.toPic
  have hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A) :=
    NefPositiveSelfIntersectionBig.isNef_of_toPic_eq X hclass.symm hH
  have hKA : X.intersectionPairing hregular K A < 0 := by
    rw [← X.picardPairing_class hregular K A, hclass]
    exact hnegative
  exact canonicalTensorPower_hZero_of_negative_nef X hregular K A eK hA hKA n hn

end KltDP.Geometry.NegativeNefCanonicalTensorPowers
#print axioms KltDP.Geometry.NegativeNefCanonicalTensorPowers.canonicalTensorPower_hZero_of_negative_nef_line
