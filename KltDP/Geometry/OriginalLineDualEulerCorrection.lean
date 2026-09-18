import KltDP.Geometry.InverseCartierEulerCorrection
import KltDP.Geometry.PicardEulerValue
import KltDP.Examples.FrobeniusExceptionalNormal

/-!
# The RR correction for the original line's actual dual

The existing evaluation identifies the dual's actual Picard class with
the inverse original class. Euler characteristic descends through the
actual sheaf isomorphism quotient, so a Cartier representative supplies
the RR correction without choosing a different line bundle for the cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SmoothCanonicalExteriorComparison

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

/-- Actual dual Euler characteristic agrees with O(-D) for an original Cartier class. -/
theorem dual_euler_eq_inverseCartier (L : InvertibleSheaf S.toScheme)
    (D : CartierDivisor S.toScheme) (hD : cartierPicardClass S.toScheme D = L.toPic) :
    eulerCharacteristic S.structureMorphism (schemeDualSheaf L.obj) =
      eulerCharacteristic S.structureMorphism (cartierDivisorModule S.toScheme (-D)) := by
  calc
    _ = picardEulerValue S.structureMorphism (dualInvertibleSheaf L).toPic :=
      (picardEulerValue_toPic S.structureMorphism (dualInvertibleSheaf L)).symm
    _ = picardEulerValue S.structureMorphism (L.toPic⁻¹) := by
      rw [dualInvertibleSheaf_toPic]
    _ = picardEulerValue S.structureMorphism (cartierPicardClass S.toScheme (-D)) := by
      rw [cartierPicardClass_neg, hD]
    _ = _ := picardEulerValue_toPic S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme (-D))

variable (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  (K : CartierDivisor S.toScheme)
  (eK : cartierDivisorModule S.toScheme K ≅
    relativeDifferentialExterior S.structureMorphism 2)

include eK

/-- The unit-plus-dual correction uses the same original line, with its
Cartier representative constructed from the original Picard class. -/
theorem unit_add_dual_euler (L : InvertibleSheaf S.toScheme) :
    (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) +
      (eulerCharacteristic S.structureMorphism (schemeDualSheaf L.obj) : ℚ) =
      2 * (eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) +
        (S.intersectionPairing hregular (S.picardRepresentative L.toPic)
          (S.picardRepresentative L.toPic + K) : ℚ) / 2 := by
  rw [S.dual_euler_eq_inverseCartier L (S.picardRepresentative L.toPic)
    (S.cartierPicardClass_picardRepresentative L.toPic)]
  exact S.unit_add_inverseCartier_euler hregular K eK (S.picardRepresentative L.toPic)

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.unit_add_dual_euler
#print axioms KltDP.Geometry.NormalProjectiveSurface.unit_add_dual_euler
