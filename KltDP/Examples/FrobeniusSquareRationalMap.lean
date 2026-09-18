import KltDP.Examples.FrobeniusGlobalGraphCompatibility
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# The fraction-field lift of the original square substitution

The lift below uses the existing polynomial expansion map, which is
definitionally the original `polynomialPowerHom 2`. Its equation on every
polynomial determines it uniquely on the rational function field. The
comparison with the projective scheme's original generic stalk map is a
separate geometric adapter.
-/

noncomputable section

universe u

namespace KltDP.Examples.FrobeniusSquareRationalMap

open FrobeniusGlobalGraphCompatibility
open scoped nonZeroDivisors

variable (k : Type u) [Field k]

/-- The coefficient-fixed square chart map extended to fractions. -/
def squareHom : RatFunc k →ₐ[k] RatFunc k :=
  RatFunc.mapAlgHom (Polynomial.expand k 2)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.expand_injective (R := k) (by decide : 0 < 2)))

/-- The extension retains the original ring map on every polynomial. -/
theorem squareHom_polynomial (f : Polynomial k) :
    squareHom k (algebraMap (Polynomial k) (RatFunc k) f) =
      algebraMap (Polynomial k) (RatFunc k) (polynomialPowerHom 2 f) := by
  have h := RatFunc.map_apply_div (Polynomial.expand k 2)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.expand_injective (R := k) (by decide : 0 < 2))) f 1
  simpa only [map_one, div_one] using h

@[simp]
theorem squareHom_X : squareHom k RatFunc.X = (RatFunc.X : RatFunc k) ^ 2 := by
  simpa only [RatFunc.algebraMap_X, polynomialPowerHom_X, map_pow] using
    squareHom_polynomial k Polynomial.X

/-- An actual field map agreeing with the square chart map is this lift. -/
theorem squareHom_unique (g : RatFunc k →+* RatFunc k)
    (hg : ∀ f : Polynomial k,
      g (algebraMap (Polynomial k) (RatFunc k) f) =
        algebraMap (Polynomial k) (RatFunc k) (polynomialPowerHom 2 f)) :
    g = (squareHom k).toRingHom := by
  apply RingHom.ext
  intro z
  rw [← RatFunc.num_div_denom z]
  simp only [map_div₀, hg, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    squareHom_polynomial]

/-- The rational coordinate has odd degree, so it is not a square over any field. -/
theorem X_not_square (z : RatFunc k) : z ^ 2 ≠ RatFunc.X := by
  intro h
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact RatFunc.X_ne_zero h.symm
  have hd := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hz hz, RatFunc.intDegree_X] at hd
  omega

end KltDP.Examples.FrobeniusSquareRationalMap
