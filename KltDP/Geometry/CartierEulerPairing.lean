import KltDP.Geometry.SurfaceEulerAdditive
import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.CartierPicardHom
import KltDP.Geometry.CartierTensorProduct

/-!
# The Euler-characteristic pairing of Cartier divisors on a normal projective surface

`D₁ · D₂ := χ(O) − χ(O(−D₁)) − χ(O(−D₂)) + χ(O(−D₁−D₂))` (`cartierEulerPairing`), with
`χ = eulerCharacteristic X.structureMorphism` (finite by the accepted 02O6 consumers). It is symmetric
(`cartierEulerPairing_comm`, from `D₁ + D₂ = D₂ + D₁`) and depends only on the Picard classes of
`O(D₁)`, `O(D₂)`: it is the value of the pairing on the Picard group
`picardEulerPairing p q := χ(1) − χ(p⁻¹) − χ(q⁻¹) + χ(p⁻¹ q⁻¹)` (through the accepted
`picardEulerValue`, `cartierPicardClass_neg`, `cartierPicardClass_add`).

**Not proved here** (recorded in `F03_RESTRICTION_ADAPTERS.md`, task 16): bilinearity of the pairing,
and the identification `(D_C) · D = intersectionNumber C D` for a Cartier prime curve `C`; the latter
needs the comparison `χ_X(i_*M) = χ_C(M)` for the closed immersion `i : C → X` in all degrees and the
projection formula `i_*O_C ⊗ O_X(−D) ≅ i_*(i^*O_X(−D))`, neither of which is claimed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The Euler-characteristic pairing on the Picard group:
`⟨p, q⟩ := χ(O) − χ(p⁻¹) − χ(q⁻¹) + χ(p⁻¹ q⁻¹)`. -/
def picardEulerPairing (p q : X.toScheme.Pic) : ℤ :=
  picardEulerValue X.structureMorphism 1 - picardEulerValue X.structureMorphism p⁻¹ -
    picardEulerValue X.structureMorphism q⁻¹ + picardEulerValue X.structureMorphism (p⁻¹ * q⁻¹)

/-- Symmetry of the Picard pairing. -/
theorem picardEulerPairing_comm (p q : X.toScheme.Pic) :
    X.picardEulerPairing p q = X.picardEulerPairing q p := by
  unfold picardEulerPairing
  rw [mul_comm]
  ring

/-- **The Euler-characteristic pairing of two Cartier divisors**:
`D₁ · D₂ := χ(O) − χ(O(−D₁)) − χ(O(−D₂)) + χ(O(−D₁−D₂))`. -/
def cartierEulerPairing (D₁ D₂ : CartierDivisor X.toScheme) : ℤ :=
  eulerCharacteristic X.structureMorphism (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) -
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₁)) -
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-D₂)) +
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme (-(D₁ + D₂)))

/-- **Symmetry** of the Euler-characteristic pairing. -/
theorem cartierEulerPairing_comm (D₁ D₂ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ = X.cartierEulerPairing D₂ D₁ := by
  unfold cartierEulerPairing
  rw [add_comm D₁ D₂]
  ring

/-- `χ(O(E))` is the Euler value of the Picard class of `O(E)`. -/
theorem eulerCharacteristic_cartierDivisorModule (E : CartierDivisor X.toScheme) :
    eulerCharacteristic X.structureMorphism (cartierDivisorModule X.toScheme E) =
      picardEulerValue X.structureMorphism (cartierPicardClass X.toScheme E) :=
  (picardEulerValue_toPic X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme E)).symm

/-- The Cartier pairing is the Picard pairing of the classes `[O(D₁)]`, `[O(D₂)]`. -/
theorem cartierEulerPairing_eq_picardEulerPairing (D₁ D₂ : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D₁ D₂ =
      X.picardEulerPairing (cartierPicardClass X.toScheme D₁) (cartierPicardClass X.toScheme D₂) := by
  unfold cartierEulerPairing picardEulerPairing
  rw [← picardEulerValue_one, X.eulerCharacteristic_cartierDivisorModule,
    X.eulerCharacteristic_cartierDivisorModule, X.eulerCharacteristic_cartierDivisorModule,
    cartierPicardClass_neg, cartierPicardClass_neg, cartierPicardClass_neg, cartierPicardClass_add,
    mul_inv]

/-- The pairing depends only on the Picard classes of the two divisors. -/
theorem cartierEulerPairing_eq_of_cartierPicardClass_eq {D₁ D₁' D₂ D₂' : CartierDivisor X.toScheme}
    (h₁ : cartierPicardClass X.toScheme D₁ = cartierPicardClass X.toScheme D₁')
    (h₂ : cartierPicardClass X.toScheme D₂ = cartierPicardClass X.toScheme D₂') :
    X.cartierEulerPairing D₁ D₂ = X.cartierEulerPairing D₁' D₂' := by
  rw [X.cartierEulerPairing_eq_picardEulerPairing, X.cartierEulerPairing_eq_picardEulerPairing, h₁, h₂]

end KltDP.Geometry.NormalProjectiveSurface
