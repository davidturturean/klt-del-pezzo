import KltDP.Examples.FrobeniusGraphPicardClassFullCover
import KltDP.Examples.FrobeniusGraphPicardClassComplement

/-!
# The original graph-minus-rulings Cartier relation on the full product

The normalized Cartier representative of the original graph equals
div(y-x^p)+p*A_infinity+B_infinity. Equality is checked on the actual
full cover by both diagonal opens and both graph-free mixed basic opens.
The local minus signs disappear only through the actual regular unit -1.

The Picard equality concerns the original graph ideal and the constructed
actual infinity ruling divisors. Comparing those ruling classes with
the pulled-back original coordinate-point ideal is still separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Examples.FrobeniusGraphPicardClassRulingRelation

open KltDP.Geometry
open FrobeniusProjectivePoints
open FrobeniusGraphPicardClassPowerCharts FrobeniusGraphPicardClassDiagonal
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassIntegral
open FrobeniusGraphPicardClassCartier FrobeniusGraphPicardClassLocalEquations
open FrobeniusGraphPicardClassMixedCoordinates FrobeniusGraphPicardClassRulingDivisors
open FrobeniusGraphPicardClassRulingCombination FrobeniusGraphPicardClassRulingEquations
open FrobeniusGraphPicardClassFullCover FrobeniusGraphPicardClassComplement

variable {k : Type u} [Field k]

local instance productIntegral : IsIntegral (projectiveProduct k) :=
  projectiveProduct_isIntegral

private theorem cartierEquation_neg (U : (projectiveProduct k).Opens) [Nonempty U]
    (f : (projectiveProduct k).functionFieldˣ) :
    cartierEquationClassHom (projectiveProduct k) U (Additive.ofMul (-f)) =
      cartierEquationClassHom (projectiveProduct k) U (Additive.ofMul f) := by
  have hu : Units.map ((projectiveProduct k).germToFunctionField U).hom.toMonoidHom
      (-1 : Γ(projectiveProduct k, U)ˣ) = -1 := by
    apply Units.ext
    change (projectiveProduct k).germToFunctionField U (-1) = -1
    rw [map_neg, map_one]
  have h := cartierEquationClassHom_mul_regular_unit (projectiveProduct k) U f
    (-1 : Γ(projectiveProduct k, U)ˣ)
  simpa only [hu, mul_neg_one] using h

private theorem graph_ruling_diagonal (p : ℕ) (i : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show diagonalOpen i ≤ ⊤ from le_top)).op (graphDivisorCandidate p) =
      (cartierDivisorSheaf (projectiveProduct k)).val.map
        (homOfLE (show diagonalOpen i ≤ ⊤ from le_top)).op (rulingCombination p) := by
  have h := rulingCombination_productOpen (k := k) p i i
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
    (homOfLE (show diagonalOpen i ≤ ⊤ from le_top)).op (rulingCombination p) = _ at h
  rw [graphDivisorCandidate_diagonal, h]
  fin_cases i
  · change cartierEquationClassHom (projectiveProduct k) (diagonalOpen 0)
      (Additive.ofMul (diagonalGraphEquationUnit p 0)) =
        cartierEquationClassHom (projectiveProduct k) (diagonalOpen 0)
          (Additive.ofMul (rulingCombinationEquation p 0 0))
    rw [rulingCombinationEquation_zero_zero]
  · change cartierEquationClassHom (projectiveProduct k) (diagonalOpen 1)
      (Additive.ofMul (diagonalGraphEquationUnit p 1)) =
        cartierEquationClassHom (projectiveProduct k) (diagonalOpen 1)
          (Additive.ofMul (rulingCombinationEquation p 1 1))
    rw [rulingCombinationEquation_one_one, cartierEquation_neg]

private theorem graph_companion_zero (p : ℕ) (i : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show companionOpen p i ≤ ⊤ from le_top)).op (graphDivisorCandidate p) = 0 := by
  let z : companionOpen (k := k) p i :=
    Nonempty.some (companionOpen_nonempty (k := k) p i)
  letI : Nonempty (graphComplement (k := k) p) :=
    ⟨⟨z.val, companionOpen_le_complement p i z.property⟩⟩
  have h := congrArg (fun s => (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (companionOpen_le_complement (k := k) p i)).op s)
    (graphDivisorCandidate_complement (k := k) p)
  dsimp only at h
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, map_zero] at h
  exact h

private theorem ruling_companion_zero (p : ℕ) (i : Fin 2) :
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show companionOpen p i ≤ ⊤ from le_top)).op (rulingCombination p) = 0 := by
  have h := congrArg (fun s => (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (companionOpen_le_mixed (k := k) p i)).op s)
    (rulingCombination_productOpen (k := k) p i (otherIndex i))
  dsimp only at h
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    cartierEquationClassHom_restrict] at h
  have hu : cartierEquationClassHom (projectiveProduct k) (companionOpen p i)
      (Additive.ofMul (mixedFunctionUnit p i)) = 0 := by
    rw [← companionUnit_image]
    exact cartierEquationClassHom_map_regular_unit (projectiveProduct k)
      (companionOpen p i) (companionUnit p i)
  fin_cases i
  · change _ = cartierEquationClassHom (projectiveProduct k) (companionOpen p 0)
      (Additive.ofMul (rulingCombinationEquation p 0 (otherIndex 0))) at h
    simp only [otherIndex, Equiv.swap_apply_left] at h
    rw [rulingCombinationEquation_zero_one] at h
    exact h.trans hu
  · change _ = cartierEquationClassHom (projectiveProduct k) (companionOpen p 1)
      (Additive.ofMul (rulingCombinationEquation p 1 (otherIndex 1))) at h
    simp only [otherIndex, Equiv.swap_apply_right] at h
    rw [rulingCombinationEquation_one_zero, cartierEquation_neg] at h
    exact h.trans hu

/-- Equality holds for the actual Cartier divisors on the whole original product. -/
theorem graphDivisorCandidate_eq_rulingCombination (p : ℕ) :
    graphDivisorCandidate (k := k) p = rulingCombination p := by
  apply (cartierDivisorSheaf (projectiveProduct k)).eq_of_locally_eq'
    (comparisonOpen p) ⊤
    (fun a => homOfLE (show comparisonOpen p a ≤ ⊤ from le_top))
    (comparisonOpens_iSup p).ge
  intro a
  cases a with
  | inl i => exact graph_ruling_diagonal p i
  | inr i => exact (graph_companion_zero p i).trans (ruling_companion_zero p i).symm

/-- The actual inverse graph-ideal class is the sum of the two actual infinity-ruling classes. -/
theorem inverse_graphIdeal_picard_eq_rulings (p : ℕ) :
    -Additive.ofMul (graphIdealLine (k := k) p).toPic =
      p • cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 0) +
        cartierPicardHom (projectiveProduct k) (rulingInfinityDivisor 1) := by
  rw [← graphDivisorCandidate_picard, graphDivisorCandidate_eq_rulingCombination,
    rulingCombination_picard]

end KltDP.Examples.FrobeniusGraphPicardClassRulingRelation
