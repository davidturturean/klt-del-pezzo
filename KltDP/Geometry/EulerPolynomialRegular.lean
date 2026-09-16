import KltDP.Geometry.EulerPairingUnconditional
import KltDP.Support.QuadraticRefinementZPow

/-!
# The actual Euler polynomial on a regular projective surface

The compiled bilinearity of the actual Picard Euler pairing identifies its inverse-class
convention with the forward second difference. The generic additive-correction argument then
gives an explicit rational polynomial for the actual Euler value on every integer power and
every product of two integer powers. Its mixed coefficient is the actual Picard Euler pairing.

All geometric polynomial theorems retain regularity of the given normal projective surface
and an algebraically closed base field. No universal normal-surface literature literal is
constructed, and no Riemann--Roch, canonical, positivity, bigness, or Hodge statement follows here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry KltDP.Geometry.ModuleCohomology KltDP.Support.QuadraticRefinement

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The linear coefficient of the Euler polynomial along a Picard class. -/
def eulerLinearCoefficient (p : X.toScheme.Pic) : ℚ :=
  (picardEulerValue X.structureMorphism p : ℚ) -
    (picardEulerValue X.structureMorphism 1 : ℚ) - (X.picardEulerPairing p p : ℚ) / 2

/-- The quadratic coefficient is half the actual self-pairing. -/
def eulerQuadraticCoefficient (p : X.toScheme.Pic) : ℚ :=
  (X.picardEulerPairing p p : ℚ) / 2

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- The inverse-class sign convention disappears when both arguments are inverted. -/
theorem picardEulerPairing_inv_inv_of_regular (p q : X.toScheme.Pic) :
    X.picardEulerPairing p⁻¹ q⁻¹ = X.picardEulerPairing p q :=
  bilinear_inv_inv X.picardEulerPairing
    (X.picardEulerPairing_mul_left_of_regular hregular)
    (X.picardEulerPairing_mul_right_of_regular hregular) p q

/-- The actual Euler value has the actual pairing as its forward second difference. -/
theorem picardEulerValue_mul_of_regular (p q : X.toScheme.Pic) :
    picardEulerValue X.structureMorphism (p * q) =
      picardEulerValue X.structureMorphism p + picardEulerValue X.structureMorphism q -
        picardEulerValue X.structureMorphism 1 + X.picardEulerPairing p q := by
  have hinv := X.picardEulerPairing_inv_inv_of_regular hregular p q
  have hval : X.picardEulerPairing p⁻¹ q⁻¹ =
      picardEulerValue X.structureMorphism 1 - picardEulerValue X.structureMorphism p -
        picardEulerValue X.structureMorphism q + picardEulerValue X.structureMorphism (p * q) := by
    simp only [picardEulerPairing, inv_inv]
  rw [hval] at hinv
  linarith only [hinv]

/-- The integral formula before division by two, for every integer exponent. -/
theorem picardEulerValue_zpow_twice_of_regular (p : X.toScheme.Pic) (n : ℤ) :
    2 * picardEulerValue X.structureMorphism (p ^ n) =
      2 * picardEulerValue X.structureMorphism 1 +
        n * (2 * picardEulerValue X.structureMorphism p -
          2 * picardEulerValue X.structureMorphism 1 - X.picardEulerPairing p p) +
        n ^ 2 * X.picardEulerPairing p p :=
  two_mul_apply_zpow (picardEulerValue X.structureMorphism) X.picardEulerPairing
    (X.picardEulerPairing_mul_left_of_regular hregular)
    (X.picardEulerPairing_mul_right_of_regular hregular)
    (X.picardEulerValue_mul_of_regular hregular) p n

/-- The actual Euler value agrees with this quadratic polynomial on every integer power. -/
theorem picardEulerValue_zpow_polynomial_of_regular (p : X.toScheme.Pic) (n : ℤ) :
    (picardEulerValue X.structureMorphism (p ^ n) : ℚ) =
      (picardEulerValue X.structureMorphism 1 : ℚ) +
        X.eulerLinearCoefficient p * (n : ℚ) + X.eulerQuadraticCoefficient p * (n : ℚ) ^ 2 := by
  simpa only [eulerLinearCoefficient, eulerQuadraticCoefficient] using
    apply_zpow_rat (picardEulerValue X.structureMorphism) X.picardEulerPairing
      (X.picardEulerPairing_mul_left_of_regular hregular)
      (X.picardEulerPairing_mul_right_of_regular hregular)
      (X.picardEulerValue_mul_of_regular hregular) p n

/-- The integral two-variable formula, before division by two. -/
theorem picardEulerValue_zpow_mul_zpow_twice_of_regular (p q : X.toScheme.Pic) (m n : ℤ) :
    2 * picardEulerValue X.structureMorphism (p ^ m * q ^ n) =
      2 * picardEulerValue X.structureMorphism 1 +
        m * (2 * picardEulerValue X.structureMorphism p -
          2 * picardEulerValue X.structureMorphism 1 - X.picardEulerPairing p p) +
        n * (2 * picardEulerValue X.structureMorphism q -
          2 * picardEulerValue X.structureMorphism 1 - X.picardEulerPairing q q) +
        m ^ 2 * X.picardEulerPairing p p + 2 * (m * n) * X.picardEulerPairing p q +
        n ^ 2 * X.picardEulerPairing q q :=
  two_mul_apply_zpow_mul_zpow (picardEulerValue X.structureMorphism) X.picardEulerPairing
    (X.picardEulerPairing_mul_left_of_regular hregular)
    (X.picardEulerPairing_mul_right_of_regular hregular)
    (X.picardEulerValue_mul_of_regular hregular) p q m n

/-- The mixed coefficient of this actual two-variable Euler polynomial is the Euler pairing. -/
theorem picardEulerValue_zpow_mul_zpow_polynomial_of_regular
    (p q : X.toScheme.Pic) (m n : ℤ) :
    (picardEulerValue X.structureMorphism (p ^ m * q ^ n) : ℚ) =
      (picardEulerValue X.structureMorphism 1 : ℚ) +
        X.eulerLinearCoefficient p * (m : ℚ) + X.eulerLinearCoefficient q * (n : ℚ) +
        X.eulerQuadraticCoefficient p * (m : ℚ) ^ 2 +
        (X.picardEulerPairing p q : ℚ) * ((m : ℚ) * (n : ℚ)) +
        X.eulerQuadraticCoefficient q * (n : ℚ) ^ 2 := by
  simpa only [eulerLinearCoefficient, eulerQuadraticCoefficient] using
    apply_zpow_mul_zpow_rat (picardEulerValue X.structureMorphism) X.picardEulerPairing
      (X.picardEulerPairing_mul_left_of_regular hregular)
      (X.picardEulerPairing_mul_right_of_regular hregular)
      (X.picardEulerValue_mul_of_regular hregular) p q m n

/-- A coefficient-form polynomial statement for this regular surface only. -/
theorem exists_picardEulerPolynomial_of_regular (p q : X.toScheme.Pic) :
    ∃ a₀₀ a₁₀ a₀₁ a₂₀ a₀₂ : ℚ, ∀ m n : ℤ,
      (picardEulerValue X.structureMorphism (p ^ m * q ^ n) : ℚ) =
        a₀₀ + a₁₀ * (m : ℚ) + a₀₁ * (n : ℚ) + a₂₀ * (m : ℚ) ^ 2 +
          (X.picardEulerPairing p q : ℚ) * ((m : ℚ) * (n : ℚ)) + a₀₂ * (n : ℚ) ^ 2 := by
  refine ⟨(picardEulerValue X.structureMorphism 1 : ℚ),
    X.eulerLinearCoefficient p, X.eulerLinearCoefficient q,
    X.eulerQuadraticCoefficient p, X.eulerQuadraticCoefficient q, ?_⟩
  exact fun m n => X.picardEulerValue_zpow_mul_zpow_polynomial_of_regular hregular p q m n

/-- The single-power formula on any actual sheaf representing that tensor power. -/
theorem eulerCharacteristic_zpow_of_toPic_eq (L M : InvertibleSheaf X.toScheme) (n : ℤ)
    (hM : M.toPic = L.toPic ^ n) :
    (eulerCharacteristic X.structureMorphism M.obj : ℚ) =
      (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ) +
      X.eulerLinearCoefficient L.toPic * (n : ℚ) +
      X.eulerQuadraticCoefficient L.toPic * (n : ℚ) ^ 2 := by
  have h := X.picardEulerValue_zpow_polynomial_of_regular hregular L.toPic n
  rw [← hM, picardEulerValue_toPic X.structureMorphism M, picardEulerValue_one] at h
  exact h

/-- The mixed formula on an actual sheaf with the indicated tensor-product Picard class. -/
theorem eulerCharacteristic_zpow_mul_zpow_of_toPic_eq
    (L M N : InvertibleSheaf X.toScheme) (m n : ℤ)
    (hN : N.toPic = L.toPic ^ m * M.toPic ^ n) :
    (eulerCharacteristic X.structureMorphism N.obj : ℚ) =
      (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ) +
      X.eulerLinearCoefficient L.toPic * (m : ℚ) + X.eulerLinearCoefficient M.toPic * (n : ℚ) +
      X.eulerQuadraticCoefficient L.toPic * (m : ℚ) ^ 2 +
      (X.picardEulerPairing L.toPic M.toPic : ℚ) * ((m : ℚ) * (n : ℚ)) +
      X.eulerQuadraticCoefficient M.toPic * (n : ℚ) ^ 2 := by
  have h := X.picardEulerValue_zpow_mul_zpow_polynomial_of_regular hregular L.toPic M.toPic m n
  rw [← hN, picardEulerValue_toPic X.structureMorphism N, picardEulerValue_one] at h
  exact h

end Regular

end KltDP.Geometry.NormalProjectiveSurface
