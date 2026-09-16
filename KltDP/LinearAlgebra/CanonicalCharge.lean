import KltDP.LinearAlgebra.CanonicalCorrection
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Canonical charge of an actual correction

This is the second identity in manuscript `lem:projection`, equation
`eq:green-charge`. The vectors and form are actual module data:
`A i j = -B (G i) (G j)`, `q i = B K (G i)`, `p i = B P (G i)`,
and `L = -(K + ∑ i, coeff i • G i)` is the constructed corrected class.

The existing canonical-correction pairing formula and uniqueness of a
solution of `A *ᵥ coeff = q` give
`p · (A⁻¹ *ᵥ q) = p · coeff = 1 - B L P`.
The strict upper bound follows from an explicit positive pairing `B L P`.
Neither a projection identity nor a canonical-charge identity is assumed.

The equality works over a commutative ring; the strict bound uses an ordered
commutative ring. There is no ambient dimension, independence, nondegeneracy,
or rank-one hypothesis in this adapter, since those hypotheses belong to
the separate square/projection identity. Geometric interpretation of `K`,
`G`, and `P`, adjunction `-B K P = 1`, identification of the constructed class
with the anticanonical pullback, the actual row equation, invertibility,
and positivity remain obligations of the geometric application.
-/

namespace KltDP.LinearAlgebra.CanonicalCharge

open Matrix CanonicalCorrection

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [Fintype ι]

/-- Rearranging the proved degree formula gives the coefficient charge.
No inverse or row equation is needed for this finite pairing calculation. -/
theorem coefficient_charge_eq_one_sub_degree
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm)
    (K : V) (G : ι → V) (coeff : ι → R) (P : V) (hKP : -B K P = 1) :
    dotProduct (contactVector B P G) coeff =
      1 - B (correctedClass K G coeff) P := by
  rw [correctedClass_pairing_of_neg_canonical_eq_one B hB K G coeff P hKP]
  ring

variable [DecidableEq ι]

/-- The actual matrix equation identifies the inverse charge with the
coefficient charge; both then equal one minus the corrected degree. -/
theorem canonical_charge_identity_of_solve
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm)
    (K : V) (G : ι → V) (coeff : ι → R) (P : V)
    (hA : IsUnit (negativeGram B G))
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G)
    (hKP : -B K P = 1) :
    dotProduct (contactVector B P G)
        ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G) =
      dotProduct (contactVector B P G) coeff ∧
    dotProduct (contactVector B P G) coeff =
      1 - B (correctedClass K G coeff) P := by
  constructor
  · rw [← coefficients_eq_inverse_of_solve B K G coeff hA hrow]
  · exact coefficient_charge_eq_one_sub_degree B hB K G coeff P hKP

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Positive corrected degree gives the strict canonical-charge budget.
The two equalities and the strict inequality are all conclusions. -/
theorem canonical_charge_identity_and_lt_one
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm)
    (K : V) (G : ι → V) (coeff : ι → R) (P : V)
    (hA : IsUnit (negativeGram B G))
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G)
    (hKP : -B K P = 1) (hdegree : 0 < B (correctedClass K G coeff) P) :
    dotProduct (contactVector B P G)
        ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G) =
      dotProduct (contactVector B P G) coeff ∧
    dotProduct (contactVector B P G) coeff =
      1 - B (correctedClass K G coeff) P ∧
    dotProduct (contactVector B P G)
        ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G) < 1 := by
  have h := canonical_charge_identity_of_solve B hB K G coeff P hA hrow hKP
  refine ⟨h.1, h.2, ?_⟩
  rw [h.1, h.2]
  exact sub_lt_self 1 hdegree

end Ordered

end KltDP.LinearAlgebra.CanonicalCharge
