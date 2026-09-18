import KltDP.Geometry.EulerPolynomialRegular
import KltDP.Geometry.CartierEulerPairingDegree

/-!
# The actual Euler–Riemann–Roch difference is additive

The original Euler pairing is the original intersection pairing on a regular
surface. Consequently twice the Euler characteristic, after subtracting the
quadratic intersection term, has an additive difference from any fixed
Cartier canonical candidate. This file uses no Riemann–Roch or duality input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

set_option autoImplicit false

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The forward Euler difference on actual Cartier divisors. -/
theorem eulerCharacteristic_cartier_add (D E : CartierDivisor X.toScheme) :
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (D + E)) =
      eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme D) +
        eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme E) -
        eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) +
        intersectionPairing X hregular D E := by
  rw [X.eulerCharacteristic_cartierDivisorModule,
    X.eulerCharacteristic_cartierDivisorModule,
    X.eulerCharacteristic_cartierDivisorModule, cartierPicardClass_add,
    X.picardEulerValue_mul_of_regular hregular, picardEulerValue_one,
    ← X.cartierEulerPairing_eq_picardEulerPairing,
    X.cartierEulerPairing_eq_intersectionPairing_of_regular hregular]

/-- Twice the literal Euler–Riemann–Roch difference, with its original
intersection term, is an additive homomorphism. -/
def canonicalEulerDefectHom (K : CartierDivisor X.toScheme) :
    CartierDivisor X.toScheme →+ ℤ where
  toFun D :=
    2 * eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme D) -
      2 * eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
      intersectionPairing X hregular D (D - K)
  map_zero' := by
    rw [X.intersectionPairing_zero_left,
      eulerCharacteristic_eq_of_iso X.structureMorphism
        (cartierDivisorModuleZeroIsoUnit X.toScheme)]
    ring
  map_add' D E := by
    rw [X.eulerCharacteristic_cartier_add hregular]
    simp only [sub_eq_add_neg, X.intersectionPairing_add_left,
      X.intersectionPairing_add_right, X.intersectionPairing_neg_right]
    rw [X.intersectionPairing_symm hregular E D]
    ring

theorem canonicalEulerDefectHom_apply (K D : CartierDivisor X.toScheme) :
    X.canonicalEulerDefectHom hregular K D =
      2 * eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme D) -
        2 * eulerCharacteristic X.structureMorphism
          (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
        intersectionPairing X hregular D (D - K) := rfl

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.eulerCharacteristic_cartier_add
#print axioms KltDP.Geometry.NormalProjectiveSurface.eulerCharacteristic_cartier_add
#check @KltDP.Geometry.NormalProjectiveSurface.canonicalEulerDefectHom
#print axioms KltDP.Geometry.NormalProjectiveSurface.canonicalEulerDefectHom
