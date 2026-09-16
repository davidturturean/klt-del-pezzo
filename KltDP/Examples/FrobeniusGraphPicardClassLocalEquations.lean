import KltDP.Examples.FrobeniusGraphPicardClassNormalization

/-!
# Actual local equations of the normalized graph Cartier divisor

The fixed-frame Cartier construction and the original ideal inclusion
identify the rational local equation on every genuine trivialization
chart. On the two original diagonal planes this is exactly the original
polynomial graph equation, with no unspecified scalar or regular unit.

These two planes do not cover the product. The mixed-point comparison
needed for the global ruling relation remains a separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassLocalEquations

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism FrobeniusBlowupContact
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational FrobeniusGraphPicardClassEquationTransition
open FrobeniusGraphPicardClassCartier FrobeniusGraphPicardClassNormalization

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The actual graph function fixes the local equation in every original ideal frame. -/
def graphChartEquationUnit (p : ℕ)
    (c : LineBundleTrivializationChart (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p))) : (projectiveProduct k).functionFieldˣ :=
  graphFunctionUnit p * lineBundleChartValueUnit (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
    (firstGraphTrivialization p) c

/-- The equation is the original inclusion of the actual chart generator. -/
theorem graphChartEquationUnit_val (p : ℕ)
    (c : LineBundleTrivializationChart (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p))) :
    (graphChartEquationUnit p c : (projectiveProduct k).functionField) =
      (projectiveProduct k).germToFunctionField c.openSet
        ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op c.openSet)
          (lineBundleChartGenerator (projectiveProduct k)
            (schemeKernelIdeal (projectiveGraphMorphism p)) c)) :=
  (graphInclusion_graphFunction_factor p c.openSet
    (lineBundleChartGenerator (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p)) c)).symm

/-- Separate the additive equation calculation from the concrete graph construction. -/
private theorem subtract_inverse_equation {G A : Type*} [CommGroup G] [AddCommGroup A]
    (f : Additive G →+ A) (x y : G) :
    f (Additive.ofMul x) - f (Additive.ofMul y⁻¹) = f (Additive.ofMul (x * y)) := by
  rw [_root_.ofMul_inv, map_neg, sub_neg_eq_add, _root_.ofMul_mul, map_add]

/-- The actual constructed divisor has these equations on every genuine ideal frame. -/
theorem graphDivisorCandidate_chart (p : ℕ)
    (c : LineBundleTrivializationChart (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p))) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show c.openSet ≤ ⊤ from le_top)).op (graphDivisorCandidate p) =
      cartierEquationClassHom (projectiveProduct k) c.openSet
        (Additive.ofMul (graphChartEquationUnit p c)) := by
  rw [graphDivisorCandidate, map_sub, graphPrincipalDivisor, principalCartierDivisorHom,
    cartierEquationClassHom_restrict, graphIdealCartierDivisor_equations]
  exact subtract_inverse_equation
    (cartierEquationClassHom (projectiveProduct k) c.openSet) (graphFunctionUnit p)
    (lineBundleChartValueUnit (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
      (firstGraphTrivialization p) c)

/-- Each original diagonal polynomial is a nonzero rational function. -/
def diagonalGraphEquationUnit (p : ℕ) (i : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  Units.mk0 (chartFunctionFieldMap i (vCoord - uCoord ^ p)) (by
    fin_cases i
    · exact graphFunction_ne_zero p
    · exact reverse_graph_equation_ne_zero p)

theorem graphChartEquationUnit_diagonal (p : ℕ) (i : Fin 2) :
    graphChartEquationUnit (k := k) p (diagonalGraphChart p i) =
      diagonalGraphEquationUnit p i := by
  apply Units.ext
  rw [graphChartEquationUnit_val]
  change (projectiveProduct k).germToFunctionField (diagonalOpen i)
      ((schemeKernelIdealι (projectiveGraphMorphism p)).val.app (op (diagonalOpen i))
        (diagonalGraphGenerator p i)) = _
  rw [diagonalGraphGenerator_inclusion]
  rfl

/-- The normalized Cartier divisor restricts to the original graph equation on each diagonal. -/
theorem graphDivisorCandidate_diagonal (p : ℕ) (i : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show diagonalOpen i ≤ ⊤ from le_top)).op (graphDivisorCandidate p) =
      cartierEquationClassHom (projectiveProduct k) (diagonalOpen i)
        (Additive.ofMul (diagonalGraphEquationUnit p i)) := by
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show (diagonalGraphChart p i).openSet ≤ ⊤ from le_top)).op
        (graphDivisorCandidate p) = _
  rw [graphDivisorCandidate_chart, graphChartEquationUnit_diagonal]
  rfl

end KltDP.Examples.FrobeniusGraphPicardClassLocalEquations
