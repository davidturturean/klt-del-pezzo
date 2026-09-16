import KltDP.Examples.FrobeniusGraphPicardClassRulingCombination
import KltDP.Examples.FrobeniusGraphPicardClassLocalEquations

/-!
# The ruling combination's original graph equations and their signs

Its diagonal equations are g00 and -g11. Its mixed equations are
h01 and -h10, for the original polynomial h=1-u^p*v. These are
identities of units in the original product function field, obtained
from its actual projection coordinates. The signs are recorded
explicitly before passing to the Cartier quotient by regular units.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassRulingEquations

open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusGraphPicardClassPowerCharts FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusGraphPicardClassCoordinateComparison FrobeniusGraphPicardClassEquationTransition
open FrobeniusGraphPicardClassRulingDivisors FrobeniusGraphPicardClassLocalEquations
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassRulingCombination

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- Nonvanishing comes from the original reciprocal coordinates and original diagonal equation. -/
theorem mixed_equation_nonzero (p : ℕ) (i : Fin 2) :
    productFunctionFieldMap (k := k) i (otherIndex i) (1 - uCoord ^ p * vCoord) ≠ 0 := by
  rw [mixed_equation_factor, productFunctionFieldMap_v]
  apply mul_ne_zero
  · fin_cases i
    · change rulingCoordinate (k := k) 1 (otherIndex 0) ≠ 0
      simpa only [otherIndex, Equiv.swap_apply_left, rulingCoordinate_one,
        rulingRight_eq_inverse] using inv_ne_zero (rulingLeft_ne_zero (k := k) 1)
    · change rulingCoordinate (k := k) 1 (otherIndex 1) ≠ 0
      simpa only [otherIndex, Equiv.swap_apply_right, rulingCoordinate_zero] using
        rulingLeft_ne_zero (k := k) 1
  · exact (diagonalGraphEquationUnit (k := k) p i).ne_zero

def mixedFunctionUnit (p : ℕ) (i : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  Units.mk0 (productFunctionFieldMap i (otherIndex i) (1 - uCoord ^ p * vCoord))
    (mixed_equation_nonzero p i)

/-- On the finite diagonal the ruling combination has exactly the original graph equation. -/
theorem rulingCombinationEquation_zero_zero (p : ℕ) :
    rulingCombinationEquation (k := k) p 0 0 = diagonalGraphEquationUnit p 0 := by
  apply Units.ext
  simp only [rulingCombinationEquation, rulingInfinityEquation, ↓reduceIte, one_pow,
    mul_one, graphFunctionUnit, diagonalGraphEquationUnit, Units.val_mk0] <;> rfl

/-- On the infinity diagonal its equation is the negative of the original graph equation. -/
theorem rulingCombinationEquation_one_one (p : ℕ) :
    rulingCombinationEquation (k := k) p 1 1 = -diagonalGraphEquationUnit p 1 := by
  apply Units.ext
  change graphFunction p * (rulingRight 0) ^ p * rulingRight 1 =
    -chartFunctionFieldMap 1 (vCoord - uCoord ^ p)
  rw [reverse_graph_equation, neg_mul, neg_neg, rulingRight_eq_inverse,
    rulingRight_eq_inverse, ← rationalX_eq_rulingLeft, ← rationalY_eq_rulingLeft]
  ring

/-- On the first mixed chart it is exactly the original mixed section's rational unit. -/
theorem rulingCombinationEquation_zero_one (p : ℕ) :
    rulingCombinationEquation (k := k) p 0 1 = mixedFunctionUnit p 0 := by
  apply Units.ext
  change graphFunction p * 1 ^ p * rulingRight 1 =
    productFunctionFieldMap 0 (otherIndex 0) (1 - uCoord ^ p * vCoord)
  rw [mixed_equation_factor]
  simp only [productFunctionFieldMap_v, otherIndex, Equiv.swap_apply_left,
    rulingCoordinate_one, one_pow, mul_one]
  change graphFunction p * rulingRight 1 = rulingRight 1 * graphFunction p
  exact mul_comm _ _

/-- On the second mixed chart the equation has the explicit harmless minus sign. -/
theorem rulingCombinationEquation_one_zero (p : ℕ) :
    rulingCombinationEquation (k := k) p 1 0 = -mixedFunctionUnit p 1 := by
  apply Units.ext
  change graphFunction p * (rulingRight 0) ^ p * 1 =
    -productFunctionFieldMap 1 (otherIndex 1) (1 - uCoord ^ p * vCoord)
  rw [mixed_equation_factor, reverse_graph_equation]
  simp only [productFunctionFieldMap_v, otherIndex, Equiv.swap_apply_right,
    rulingCoordinate_zero, mul_one]
  rw [rulingRight_eq_inverse, ← rationalX_eq_rulingLeft, ← rationalY_eq_rulingLeft]
  calc
    graphFunction p * (rationalX)⁻¹ ^ p =
        graphFunction p * (rationalX)⁻¹ ^ p * ((rationalY) * (rationalY)⁻¹) := by
      rw [mul_inv_cancel₀ (rationalY_ne_zero (k := k)), mul_one]
    _ = _ := by ring

end KltDP.Examples.FrobeniusGraphPicardClassRulingEquations
