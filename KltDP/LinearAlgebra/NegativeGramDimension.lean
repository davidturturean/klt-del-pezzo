import KltDP.LinearAlgebra.CanonicalCorrection
import KltDP.LinearAlgebra.NegativeSubspaceDimension
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Dimension bounds from an actual negative Gram matrix

The matrix here is `CanonicalCorrection.negativeGram B v`: its entries
are the negatives of the actual pairings `B (v i) (v j)`. Its quadratic
form is the negative of the square of the actual finite linear
combination. Positive definiteness therefore proves strict negativity,
linear independence, and a strict dimension bound when the ambient space
contains a vector of positive square.

The finite pairing identity works over a commutative ring. The order
arguments are stated over `ℚ`, as needed for rational divisor classes in
the dimension argument of manuscript `thm:no-even-nodes`. No symmetry
hypothesis on the ambient bilinear form is needed: positive definiteness
already includes the required symmetry of the supplied Gram matrix.

This module constructs no cover, surface, ample class, or exceptional
curve. Applying it to the manuscript still requires the actual divisor
classes and intersection form, positive definiteness of their negative
Gram matrix, the positive ample class, and the ambient Picard dimension.
Neither linear independence nor the resulting rank bound is a premise.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix CanonicalCorrection
open scoped BigOperators

section Pairing

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Fintype ι]

/-- The actual negative Gram matrix computes the negative of the bilinear
pairing of two supplied finite linear combinations. -/
theorem negativeGram_dotProduct_mulVec (B : LinearMap.BilinForm R V)
    (v : ι → V) (c d : ι → R) :
    dotProduct c (negativeGram B v *ᵥ d) =
      -B (correction v c) (correction v d) := by
  rw [pairing_correction_left]
  simp only [dotProduct, negativeGram_mulVec_apply, mul_neg, Finset.sum_neg_distrib]

/-- The quadratic form of the actual negative Gram matrix is the negative
square of the actual finite linear combination. -/
theorem negativeGram_quadratic_form (B : LinearMap.BilinForm R V)
    (v : ι → V) (c : ι → R) :
    dotProduct c (negativeGram B v *ᵥ c) =
      -B (∑ i, c i • v i) (∑ i, c i • v i) :=
  negativeGram_dotProduct_mulVec B v c c

end Pairing

section Rational

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]

/-- Positive definiteness of the actual negative Gram matrix proves strict
negativity for every nonzero coefficient vector. -/
theorem negativeGram_posDef_strictly_negative (B : LinearMap.BilinForm ℚ V)
    (v : ι → V) (hA : (negativeGram B v).PosDef) :
    ∀ c : ι → ℚ, c ≠ 0 →
      B (∑ i, c i • v i) (∑ i, c i • v i) < 0 := by
  intro c hc
  have hpos : 0 < dotProduct c (negativeGram B v *ᵥ c) := by
    simpa only [star_trivial] using hA.2 c hc
  rw [negativeGram_quadratic_form] at hpos
  exact neg_pos.mp hpos

/-- The supplied vectors are linearly independent; this is derived from
their actual Gram matrix rather than required separately. -/
theorem negativeGram_posDef_linearIndependent (B : LinearMap.BilinForm ℚ V)
    (v : ι → V) (hA : (negativeGram B v).PosDef) :
    LinearIndependent ℚ v :=
  linearIndependent_of_negative_combinations B v
    (negativeGram_posDef_strictly_negative B v hA)

/-- A family with positive definite negative Gram matrix has fewer members
than the ambient dimension if an actual positive vector exists. -/
theorem negativeGram_posDef_card_lt_finrank [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (v : ι → V)
    (hA : (negativeGram B v).PosDef) (hpositive : ∃ x : V, 0 < B x x) :
    Fintype.card ι < Module.finrank ℚ V :=
  negative_combinations_card_lt_finrank B v
    (negativeGram_posDef_strictly_negative B v hA) hpositive

/-- In particular the actual negative family cannot have the full ambient
dimension in the presence of an actual positive vector. -/
theorem negativeGram_posDef_card_ne_finrank [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (v : ι → V)
    (hA : (negativeGram B v).PosDef) (hpositive : ∃ x : V, 0 < B x x) :
    Fintype.card ι ≠ Module.finrank ℚ V :=
  ne_of_lt (negativeGram_posDef_card_lt_finrank B v hA hpositive)

end Rational

end KltDP.LinearAlgebra
