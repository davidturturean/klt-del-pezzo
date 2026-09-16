import KltDP.Examples.FrobeniusGraphPicardClassMixedCoordinates
import KltDP.Examples.FrobeniusGraphPicardClassRulingDivisors

/-!
# The actual ruling combination on all four original product charts

The principal divisor of the original graph function, together with p
times the first infinity ruling and the second infinity ruling, gives
an actual Cartier divisor. Its equations on every original product
chart follow from the already constructed ruling restrictions and the
Cartier sheaf homomorphisms. Equality with the original graph divisor
is a subsequent local comparison on a full cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassRulingCombination

open KltDP.Geometry
open FrobeniusProjectivePoints
open FrobeniusGraphPicardClassIntegral FrobeniusGraphPicardClassRational
open FrobeniusGraphPicardClassRulingDivisors FrobeniusGraphPicardClassMixedCoordinates

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

/-- The actual Cartier divisor predicted by the graph's bidegree. -/
def rulingCombination (p : ℕ) : CartierDivisor (projectiveProduct k) :=
  graphPrincipalDivisor p + p • rulingInfinityDivisor 0 + rulingInfinityDivisor 1

def rulingCombinationEquation (p : ℕ) (i j : Fin 2) : (projectiveProduct k).functionFieldˣ :=
  graphFunctionUnit p * rulingInfinityEquation 0 i ^ p * rulingInfinityEquation 1 j

private theorem rulingInfinityDivisor_productOpen (d i j : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show productOpen i j ≤ ⊤ from le_top)).op (rulingInfinityDivisor d) =
      cartierEquationClassHom (projectiveProduct k) (productOpen i j)
        (Additive.ofMul (rulingInfinityEquation d (productIndex d i j))) := by
  let X := projectiveProduct k
  let V : X.Opens := productOpen i j
  let U : X.Opens := rulingOpen d (productIndex d i j)
  have hVU : V ≤ U := productOpen_le_rulingChart d i j
  have h := congrArg (fun s => (cartierDivisorSheaf X).val.map (homOfLE hVU).op s)
    (rulingInfinityDivisor_restrict (k := k) d (productIndex d i j))
  dsimp only at h
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    cartierEquationClassHom_restrict] at h
  exact h

/-- The formula holds as a restriction of the actual constructed Cartier divisor. -/
theorem rulingCombination_productOpen (p : ℕ) (i j : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show productOpen i j ≤ ⊤ from le_top)).op (rulingCombination p) =
      cartierEquationClassHom (projectiveProduct k) (productOpen i j)
        (Additive.ofMul (rulingCombinationEquation p i j)) := by
  rw [rulingCombination, map_add, map_add, map_nsmul,
    graphPrincipalDivisor, principalCartierDivisorHom, cartierEquationClassHom_restrict,
    rulingInfinityDivisor_productOpen, rulingInfinityDivisor_productOpen]
  have hzero : productIndex 0 i j = i := if_pos rfl
  have hone : productIndex 1 i j = j := if_neg (by decide)
  rw [hzero, hone]
  rw [← map_nsmul, ← map_add, ← map_add]
  congr 1

/-- Its Picard class contains precisely the two actual ruling classes. -/
theorem rulingCombination_picard (p : ℕ) :
    cartierPicardHom (projectiveProduct k) (rulingCombination p) =
      p • cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 0) +
        cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 1) := by
  rw [rulingCombination, map_add, map_add, map_nsmul, graphPrincipalDivisor_picard, zero_add]

end KltDP.Examples.FrobeniusGraphPicardClassRulingCombination
