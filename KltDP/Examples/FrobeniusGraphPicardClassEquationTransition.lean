import KltDP.Examples.FrobeniusGraphPicardClassCoordinateComparison
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The exact reciprocal-chart graph equation

The second diagonal graph equation is expressed in the same original
function field as the first. Its transition factor includes the actual
minus sign and the powers prescribed by the two ruling coordinates.
This rational identity is a local-equation input; by itself it does not
assert gluing or a global Picard-class equality.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassEquationTransition

open FrobeniusProjectivePoints FrobeniusBlowupContact
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassRational
open FrobeniusGraphPicardClassRulingCoordinates
open FrobeniusGraphPicardClassCoordinateComparison

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

theorem rationalX_ne_zero : rationalX (k := k) ≠ 0 := by
  rw [rationalX_eq_rulingLeft]
  exact rulingLeft_ne_zero 0

theorem rationalY_ne_zero : rationalY (k := k) ≠ 0 := by
  rw [rationalY_eq_rulingLeft]
  exact rulingLeft_ne_zero 1

/-- The exact original chart equation, including the minus sign from reversal. -/
theorem reverse_graph_equation (p : ℕ) :
    chartFunctionFieldMap (k := k) 1 (vCoord - uCoord ^ p) =
      -((rationalX)⁻¹ ^ p * (rationalY)⁻¹) * graphFunction p := by
  rw [map_sub, map_pow, reverse_chart_u, reverse_chart_v, graphFunction_eq_coordinates]
  rw [inv_pow]
  field_simp [rationalX_ne_zero (k := k), rationalY_ne_zero (k := k)]
  <;> ring
  all_goals simp only [true_or]

/-- The reverse local equation is nonzero on the actual integral surface. -/
theorem reverse_graph_equation_ne_zero (p : ℕ) :
    chartFunctionFieldMap (k := k) 1 (vCoord - uCoord ^ p) ≠ 0 := by
  rw [reverse_graph_equation]
  exact mul_ne_zero
    (neg_ne_zero.mpr (mul_ne_zero
      (pow_ne_zero p (inv_ne_zero (rationalX_ne_zero (k := k))))
      (inv_ne_zero (rationalY_ne_zero (k := k)))))
    (graphFunction_ne_zero p)

end KltDP.Examples.FrobeniusGraphPicardClassEquationTransition
