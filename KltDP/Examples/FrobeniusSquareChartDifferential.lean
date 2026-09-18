import KltDP.Examples.FrobeniusGraphPicardClassPowerCharts
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Zero differential of the original square substitution

The original projective power map is represented on both reciprocal
polynomial charts by `polynomialPowerHom 2`, as proved by
`polynomialChartMap_power_both`. Every native differential image of that
actual ring map vanishes in characteristic two. The last statement also
retains this vanishing after evaluation in any original k-algebra.

These are differential statements about the actual chart substitution;
the generic field degree and its global sheaf comparison are separate.
-/

noncomputable section

universe u v

namespace KltDP.Examples.FrobeniusSquareChartDifferential

open FrobeniusGlobalGraphCompatibility

variable {k : Type u} [Field k] [CharP k 2]

/-- The derivative of every polynomial in the image of the original
coefficient-fixed square substitution is zero. -/
theorem derivative_polynomialPowerHom_two (f : Polynomial k) :
    Polynomial.derivative (polynomialPowerHom 2 f) = 0 := by
  change Polynomial.derivative (f.comp (Polynomial.X ^ 2)) = 0
  rw [Polynomial.derivative_comp, Polynomial.derivative_X_pow]
  have htwo : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
  rw [htwo, Polynomial.C_0, zero_mul, zero_mul]

/-- Every original Kähler differential image of the square chart map
vanishes, with the original k-algebra structure on the polynomial ring. -/
theorem differential_polynomialPowerHom_two (f : Polynomial k) :
    KaehlerDifferential.D k (Polynomial k) (polynomialPowerHom 2 f) = 0 := by
  rw [KaehlerDifferential.polynomial_D_apply,
    derivative_polynomialPowerHom_two, zero_smul]

/-- The same vanishing holds after the actual evaluation map into any
k-algebra, in particular for the original localized chart rings. -/
theorem differential_aeval_polynomialPowerHom_two
    {A : Type v} [CommRing A] [Algebra k A] (x : A) (f : Polynomial k) :
    KaehlerDifferential.D k A (Polynomial.aeval x (polynomialPowerHom 2 f)) = 0 := by
  rw [Derivation.comp_aeval_eq, derivative_polynomialPowerHom_two, map_zero, zero_smul]

end KltDP.Examples.FrobeniusSquareChartDifferential
