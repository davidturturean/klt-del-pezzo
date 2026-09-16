import KltDP.Geometry.IntersectionPairing
import KltDP.Geometry.CartierEulerPairingDegree
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bilinearity of the actual Cartier Euler pairing on a regular surface

The four-term Euler expression satisfies a cocycle identity. The Cartier divisors whose pairing
is additive in the second argument form an additive subgroup: the cocycle identity propagates
this property through sums and negatives. Every prime-curve Cartier divisor belongs to that
subgroup by the accepted effective-divisor degree theorem. The accepted Cartier--Weil equivalence
expresses every Cartier divisor as a finite integer combination of those divisors.

Thus `cartierEulerPairingAdditive_of_regular` discharges the existing
`CartierEulerPairingAdditive` proposition on a regular normal projective surface over an
algebraically closed field. The proof uses the existing actual Cartier divisors and Euler pairing;
it has no numerical-intersection literal, Riemann--Roch hypothesis, or new geometric assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The four-term Euler expression is a normalized two-cocycle. -/
theorem cartierEulerPairing_cocycle (D E F : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D E + X.cartierEulerPairing (D + E) F =
      X.cartierEulerPairing D (E + F) + X.cartierEulerPairing E F := by
  unfold cartierEulerPairing
  rw [add_assoc D E F]
  ring

/-- The actual zero Cartier divisor pairs to zero. -/
theorem cartierEulerPairing_zero_left (D : CartierDivisor X.toScheme) :
    X.cartierEulerPairing 0 D = 0 := by
  rw [X.cartierEulerPairing_eq_picardEulerPairing, cartierPicardClass_zero]
  unfold picardEulerPairing
  simp only [inv_one, one_mul]
  ring

theorem cartierEulerPairing_zero_right (D : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D 0 = 0 := by
  rw [X.cartierEulerPairing_comm, X.cartierEulerPairing_zero_left]

/-- The additivity locus of the actual Euler pairing is an additive subgroup. -/
private def cartierEulerAdditiveSubgroup : AddSubgroup (CartierDivisor X.toScheme) where
  carrier := {D | ∀ E F : CartierDivisor X.toScheme,
    X.cartierEulerPairing D (E + F) = X.cartierEulerPairing D E + X.cartierEulerPairing D F}
  zero_mem' := by
    intro E F
    rw [X.cartierEulerPairing_zero_left, X.cartierEulerPairing_zero_left,
      X.cartierEulerPairing_zero_left, add_zero]
  add_mem' := by
    intro D D' hD hD' E F
    have hsum (T : CartierDivisor X.toScheme) :
        X.cartierEulerPairing (D + D') T =
          X.cartierEulerPairing D T + X.cartierEulerPairing D' T := by
      have hc := X.cartierEulerPairing_cocycle D D' T
      rw [hD D' T] at hc
      linarith only [hc]
    rw [hsum, hsum, hsum, hD E F, hD' E F]
    ring
  neg_mem' := by
    intro D hD E F
    have hneg (T : CartierDivisor X.toScheme) :
        X.cartierEulerPairing (-D) T = -X.cartierEulerPairing D T := by
      have hc := X.cartierEulerPairing_cocycle D (-D) T
      rw [add_neg_cancel, X.cartierEulerPairing_zero_left, hD (-D) T] at hc
      linarith only [hc]
    rw [hneg, hneg, hneg, hD E F]
    ring

section Regular

variable [IsAlgClosed k] (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

include hregular

/-- The existing additivity proposition holds for the actual Euler pairing on a regular surface. -/
theorem cartierEulerPairingAdditive_of_regular : CartierEulerPairingAdditive X := by
  classical
  intro D
  change D ∈ cartierEulerAdditiveSubgroup X
  have hprime (C : X.PrimeCurve) :
      X.primeCurveCartier hregular C ∈ cartierEulerAdditiveSubgroup X := by
    intro E F
    exact X.cartierEulerPairing_add_right_of_hasRegularEquations
      (X.primeCurveCartier hregular C) (X.primeCurveCartier_hasRegularEquations hregular C) E F
  have hD : D = (X.regularCartierWeilEquiv hregular).symm
      ((X.cartierToWeilHom D).sum Finsupp.single) := by
    rw [Finsupp.sum_single, ← X.regularCartierWeilEquiv_apply hregular D,
      AddEquiv.symm_apply_apply]
  rw [hD, map_finsuppSum]
  unfold Finsupp.sum
  refine sum_mem fun C _ => ?_
  change (X.regularCartierWeilEquiv hregular).symm
    (Finsupp.single C ((X.cartierToWeilHom D) C)) ∈ cartierEulerAdditiveSubgroup X
  have hsingle : (Finsupp.single C ((X.cartierToWeilHom D) C) : X.WeilDivisor) =
      ((X.cartierToWeilHom D) C) • Finsupp.single C (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_zsmul]
  exact (cartierEulerAdditiveSubgroup X).zsmul_mem (hprime C) _

/-- Additivity in the second argument for arbitrary Cartier divisors on a regular surface. -/
theorem cartierEulerPairing_add_right_of_regular (D E F : CartierDivisor X.toScheme) :
    X.cartierEulerPairing D (E + F) = X.cartierEulerPairing D E + X.cartierEulerPairing D F :=
  X.cartierEulerPairingAdditive_of_regular hregular D E F

/-- Additivity in the first argument, by symmetry of the actual Euler expression. -/
theorem cartierEulerPairing_add_left_of_regular (D E F : CartierDivisor X.toScheme) :
    X.cartierEulerPairing (D + E) F = X.cartierEulerPairing D F + X.cartierEulerPairing E F := by
  rw [X.cartierEulerPairing_comm (D + E) F,
    X.cartierEulerPairing_add_right_of_regular hregular F D E,
    X.cartierEulerPairing_comm F D, X.cartierEulerPairing_comm F E]

end Regular

end KltDP.Geometry.NormalProjectiveSurface
