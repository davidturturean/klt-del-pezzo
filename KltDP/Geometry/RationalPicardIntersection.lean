import KltDP.Geometry.HodgeIndexReduction
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Scalar extension of the original Picard intersection pairing

The accepted integer Picard pairing is bundled as an integer bilinear form
using its existing additive homomorphism. Mathlib's existing `BilinForm.baseChange`
then extends this same form to the existing `RationalPicard = ℚ ⊗[ℤ] Additive Pic`.
The pure-tensor formula recovers the original pairing, and pairing with the
rationalized class of an actual prime curve is the existing rational restriction
degree on that curve.

The hypotheses are an actual normal projective surface over an algebraically
closed field and regularity of all its stalks. No Euler-polynomial, Riemann–Roch,
Hodge-index or finite-dimensionality premise enters. This module does not assert
finite dimensionality or construct a new class quotient.
-/

noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- The accepted integer pairing, bundled using `picardPairingHom`.
That homomorphism fixes its second argument; symmetry identifies the displayed
bilinear form with the original ordering in the next theorem. -/
def integralPicardIntersectionBilinForm :
    LinearMap.BilinForm ℤ (Additive X.toScheme.Pic) :=
  (AddMonoidHom.mk'
    (fun p : Additive X.toScheme.Pic => (X.picardPairingHom hregular p.toMul).toIntLinearMap)
    (fun p p' => by
      apply LinearMap.ext
      intro q
      change picardPairing X hregular q.toMul (p + p').toMul =
        picardPairing X hregular q.toMul p.toMul + picardPairing X hregular q.toMul p'.toMul
      simpa only [toMul_add] using
        X.picardPairing_mul_right_of_regular hregular q.toMul p.toMul p'.toMul)).toIntLinearMap

@[simp]
theorem integralPicardIntersectionBilinForm_apply (p q : Additive X.toScheme.Pic) :
    X.integralPicardIntersectionBilinForm hregular p q =
      picardPairing X hregular p.toMul q.toMul := by
  change picardPairing X hregular q.toMul p.toMul = _
  exact X.picardPairing_symm hregular q.toMul p.toMul

/-- The integer form is symmetric on the original Picard group. -/
theorem integralPicardIntersectionBilinForm_isSymm :
    (X.integralPicardIntersectionBilinForm hregular).IsSymm := by
  intro p q
  rw [integralPicardIntersectionBilinForm_apply, integralPicardIntersectionBilinForm_apply]
  exact X.picardPairing_symm hregular p.toMul q.toMul

/-- The Q-bilinear scalar extension on the existing rationalized Picard group. -/
def rationalPicardIntersectionBilinForm : LinearMap.BilinForm ℚ X.RationalPicard :=
  (X.integralPicardIntersectionBilinForm hregular).baseChange ℚ

/-- On pure tensors, both scalar factors multiply the same original integer pairing. -/
@[simp]
theorem rationalPicardIntersectionBilinForm_tmul_tmul (a b : ℚ)
    (p q : Additive X.toScheme.Pic) :
    X.rationalPicardIntersectionBilinForm hregular (a ⊗ₜ[ℤ] p) (b ⊗ₜ[ℤ] q) =
      a * b * (picardPairing X hregular p.toMul q.toMul : ℚ) := by
  rw [rationalPicardIntersectionBilinForm, LinearMap.BilinForm.baseChange_tmul,
    integralPicardIntersectionBilinForm_apply, zsmul_eq_mul]
  ring

/-- The canonical images of integral classes retain their original intersection. -/
@[simp]
theorem rationalPicardIntersectionBilinForm_inclusion (p q : Additive X.toScheme.Pic) :
    X.rationalPicardIntersectionBilinForm hregular
        (X.picardTensorInclusion p) (X.picardTensorInclusion q) =
      (picardPairing X hregular p.toMul q.toMul : ℚ) := by
  change X.rationalPicardIntersectionBilinForm hregular
    ((1 : ℚ) ⊗ₜ[ℤ] p) ((1 : ℚ) ⊗ₜ[ℤ] q) = _
  rw [rationalPicardIntersectionBilinForm_tmul_tmul, one_mul, one_mul]

/-- Symmetry survives scalar extension without a dimension assumption. -/
theorem rationalPicardIntersectionBilinForm_isSymm :
    (X.rationalPicardIntersectionBilinForm hregular).IsSymm :=
  LinearMap.BilinForm.IsSymm.baseChange ℚ
    (X.integralPicardIntersectionBilinForm_isSymm hregular)

/-- The rationalized Picard class of the actual prime curve's Cartier divisor. -/
def primeCurveRationalPicardClass (C : X.PrimeCurve) : X.RationalPicard :=
  X.picardTensorInclusion
    (Additive.ofMul (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C)))

/-- Pairing against an actual prime curve recovers its already defined Q-linear degree test. -/
theorem rationalPicardIntersectionBilinForm_primeCurve (v : X.RationalPicard)
    (C : X.PrimeCurve) :
    X.rationalPicardIntersectionBilinForm hregular v
        (X.primeCurveRationalPicardClass hregular C) =
      X.rationalPicardRestrictionDegree C v := by
  have hmaps :
      (X.rationalPicardIntersectionBilinForm hregular).flip
          (X.primeCurveRationalPicardClass hregular C) =
        X.rationalPicardRestrictionDegree C := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a p
    change X.rationalPicardIntersectionBilinForm hregular (a ⊗ₜ[ℤ] p)
        ((1 : ℚ) ⊗ₜ[ℤ]
          Additive.ofMul (cartierPicardClass X.toScheme (X.primeCurveCartier hregular C))) = _
    rw [rationalPicardIntersectionBilinForm_tmul_tmul,
      rationalPicardRestrictionDegree_tmul, mul_one, toMul_ofMul,
      X.picardPairing_primeCurveClass hregular p.toMul C]
  exact congrArg (fun f : X.RationalPicard →ₗ[ℚ] ℚ => f v) hmaps

/-- Integral Cartier divisors retain their actual intersection after rationalization. -/
theorem rationalPicardIntersectionBilinForm_cartier (D E : CartierDivisor X.toScheme) :
    X.rationalPicardIntersectionBilinForm hregular
        (X.picardTensorInclusion (cartierPicardHom X.toScheme D))
        (X.picardTensorInclusion (cartierPicardHom X.toScheme E)) =
      (intersectionPairing X hregular D E : ℚ) := by
  rw [rationalPicardIntersectionBilinForm_inclusion, cartierPicardHom_apply,
    cartierPicardHom_apply, X.picardPairing_class hregular D E]

end KltDP.Geometry.NormalProjectiveSurface
