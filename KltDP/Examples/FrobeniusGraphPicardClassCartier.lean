import KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors
import KltDP.Geometry.CartierPicardComparison

/-!
# A Cartier representative of the original graph ideal with fixed normalization

The existing Cartier-to-Picard construction is applied to the literal
graph kernel and its first original equation frame. Its actual module
isomorphism identifies the resulting Cartier class with that graph ideal.
Subtracting from the principal divisor of the original graph function
gives the inverse ideal class, with the generic normalization fixed for
the subsequent comparison of local graph equations.

No comparison with the ruling divisors is asserted in this construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassCartier

open KltDP.Geometry
open FrobeniusProjectivePoints FrobeniusProjectiveMorphism
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

local instance graphKernelInvertible (p : ℕ) :
    KltDP.SheafOfModules.IsInvertible (R := (projectiveProduct k).ringCatSheaf)
      (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)) :=
  graphKernel_isInvertible p

/-- The generic trivialization is the inverse of the original first graph-equation frame. -/
def firstGraphTrivialization (p : ℕ) :
    (schemeKernelIdeal (projectiveGraphMorphism (k := k) p)).over (diagonalOpen 0) ≅
      _root_.SheafOfModules.unit ((projectiveProduct k).ringCatSheaf.over (diagonalOpen 0)) :=
  (openChartToOverUnitIso (diagonalOpen 0)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (originalOpenFrame p (some 0))).symm

/-- The actual existing gluing construction is used with that fixed trivialization. -/
def graphIdealCartierDivisor (p : ℕ) : CartierDivisor (projectiveProduct k) :=
  (exists_cartierDivisor_of_lineBundle (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
    (firstGraphTrivialization p)).choose

/-- Its equations are the actual inverse generator values supplied by the proved construction. -/
theorem graphIdealCartierDivisor_equations (p : ℕ)
    (c : LineBundleTrivializationChart (projectiveProduct k)
      (schemeKernelIdeal (projectiveGraphMorphism p))) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show c.openSet ≤ ⊤ from le_top)).op (graphIdealCartierDivisor p) =
      cartierEquationClassHom (projectiveProduct k) c.openSet
        (Additive.ofMul ((lineBundleChartValueUnit (projectiveProduct k)
          (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
          (firstGraphTrivialization p) c)⁻¹)) :=
  (exists_cartierDivisor_of_lineBundle (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
    (firstGraphTrivialization p)).choose_spec c

/-- The constructed O(D) is isomorphic to the literal original graph kernel. -/
def graphIdealCartierIso (p : ℕ) :
    schemeKernelIdeal (projectiveGraphMorphism (k := k) p) ≅
      cartierDivisorModule (projectiveProduct k) (graphIdealCartierDivisor p) :=
  lineBundleCartierIso (projectiveProduct k)
    (schemeKernelIdeal (projectiveGraphMorphism p)) (diagonalOpen 0)
    (firstGraphTrivialization p) (graphIdealCartierDivisor p)
    (graphIdealCartierDivisor_equations p)

theorem graphIdealCartierDivisor_picard (p : ℕ) :
    cartierPicardClass (projectiveProduct k) (graphIdealCartierDivisor p) =
      (graphIdealLine (k := k) p).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveProduct k)
  apply Units.ext
  rw [cartierPicardClass_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨(graphIdealCartierIso p).symm⟩

/-- This representative of the inverse graph ideal fixes the original graph-function scale. -/
def graphDivisorCandidate (p : ℕ) : CartierDivisor (projectiveProduct k) :=
  graphPrincipalDivisor p - graphIdealCartierDivisor p

/-- Its class is that of the original graph ideal's inverse, by the constructed module isomorphism. -/
theorem graphDivisorCandidate_picard (p : ℕ) :
    cartierPicardHom (projectiveProduct k) (graphDivisorCandidate p) =
      -Additive.ofMul (graphIdealLine (k := k) p).toPic := by
  rw [graphDivisorCandidate, map_sub, graphPrincipalDivisor_picard, zero_sub]
  exact congrArg (fun c : (projectiveProduct k).Pic => -Additive.ofMul c)
    (graphIdealCartierDivisor_picard p)

end KltDP.Examples.FrobeniusGraphPicardClassCartier
