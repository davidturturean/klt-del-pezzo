import KltDP.Geometry.NegativeNefCartierPowers
import KltDP.Geometry.SectionRatioHZero
import KltDP.Geometry.InvertibleSheafSectionPowers
import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# Vanishing for the actual positive canonical tensor powers

The existing Cartier-multiple vanishing is transported through actual sheaf
isomorphisms and the already constructed tensor powers. The canonical input
is the original exterior differential sheaf, not an assumed numerical class.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.NegativeNefCanonicalTensorPowers

open InvertibleSheafSectionPowers SmoothSurfaceKaehlerAtlas
open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

local instance canonicalPowerIntegral : IsIntegral X.toScheme := X.integral

/-- Negative intersection kills H0 of every actual positive tensor power
of the original line, for any actual Cartier representative of that line. -/
theorem hZero_tensorPower_of_negative_nef
    (L : InvertibleSheaf X.toScheme) (D A : CartierDivisor X.toScheme)
    (eD : cartierDivisorModule X.toScheme D ≅ L.obj)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hnegative : X.intersectionPairing hregular D A < 0)
    (n : ℕ) (hn : 0 < n) :
    cohomologyDimension X.structureMorphism (power L n).obj 0 = 0 := by
  have hp := SchemeKernelIdealIsoTransport.toPic_eq_of_iso
    (cartierDivisorInvertibleSheaf X.toScheme D) L eD
  rw [← Positivity.picardHZero_toPic X.structureMorphism (power L n),
    power_toPic, ← hp,
    ← SectionRatioHZero.cohomologyDimension_eq_picard_power X.structureMorphism D n]
  exact NegativeNefCartierPowers.hZero_positive_multiple_eq_zero
    X hregular D A hA hnegative n hn

/-- Every positive pluricanonical space vanishes when the actual canonical
Cartier representative has negative intersection with an original nef line. -/
theorem canonicalTensorPower_hZero_of_negative_nef
    [IsSmoothOfRelativeDimension 2 X.structureMorphism]
    (K A : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hnegative : X.intersectionPairing hregular K A < 0)
    (n : ℕ) (hn : 0 < n) :
    cohomologyDimension X.structureMorphism
      (power (canonicalSheafOfSmoothSurface X.structureMorphism) n).obj 0 = 0 := by
  exact hZero_tensorPower_of_negative_nef X hregular
    (canonicalSheafOfSmoothSurface X.structureMorphism) K A
    (eK ≪≫ (canonicalSheafOfSmoothSurfaceIsoExterior X.structureMorphism).symm)
    hA hnegative n hn

end KltDP.Geometry.NegativeNefCanonicalTensorPowers

#check @KltDP.Geometry.NegativeNefCanonicalTensorPowers.canonicalTensorPower_hZero_of_negative_nef
#print axioms KltDP.Geometry.NegativeNefCanonicalTensorPowers.hZero_tensorPower_of_negative_nef
#print axioms KltDP.Geometry.NegativeNefCanonicalTensorPowers.canonicalTensorPower_hZero_of_negative_nef
