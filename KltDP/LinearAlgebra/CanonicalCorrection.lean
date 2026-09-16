import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-!
# Squares and pairings of an actual canonical correction

For a symmetric bilinear form `B`, supplied vectors `G i`, and a vector `K`,
the negative Gram matrix has entries `-B (G i) (G j)` and the source vector
has entries `B K (G i)`. A solution of the actual matrix equation defines
`D = ∑ i, coeff i • G i` and `H = -(K + D)`. We compute the actual square
of `H` and its pairing with every supplied vector `C`. Invertibility of
the actual negative Gram matrix gives the inverse-matrix specialization.

This is the bilinear algebra in manuscript `lem:square-degree`. A geometric
application must separately identify these vectors and the bilinear form
with divisor classes and their intersection pairing, prove the matrix
equation and invertibility, and supply the adjunction identity `-B K C = 1`
when using the degree-one specialization. None of those geometric adapters
is asserted here. The algebra works over any commutative ring and uses no
division by two.
-/

namespace KltDP.LinearAlgebra.CanonicalCorrection

open Matrix
open scoped BigOperators

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The actual negative Gram matrix of the supplied vectors. -/
def negativeGram (B : LinearMap.BilinForm R V) (G : ι → V) : Matrix ι ι R :=
  fun i j => -B (G i) (G j)

/-- The actual pairings of the supplied vector `K` with the family. -/
def sourceVector (B : LinearMap.BilinForm R V) (K : V) (G : ι → V) : ι → R :=
  fun i => B K (G i)

/-- Contacts use the orientation `B C (G i)` of the manuscript. -/
def contactVector (B : LinearMap.BilinForm R V) (C : V) (G : ι → V) : ι → R :=
  fun i => B C (G i)

variable [Fintype ι]

/-- The correction is the actual finite linear combination in the module. -/
def correction (G : ι → V) (coeff : ι → R) : V := ∑ i, coeff i • G i

/-- The corrected vector is the negative of the sum of `K` and its correction. -/
def correctedClass (K : V) (G : ι → V) (coeff : ι → R) : V :=
  -(K + correction G coeff)

/-- Pairing in the first argument of the actual linear combination. -/
theorem pairing_correction_left (B : LinearMap.BilinForm R V)
    (G : ι → V) (coeff : ι → R) (x : V) :
    B (correction G coeff) x = dotProduct coeff (fun i => B (G i) x) := by
  simp only [correction, B.sum_left, B.smul_left, dotProduct]

/-- Pairing in the second argument, expressed in the contact-first order. -/
theorem pairing_correction_right (B : LinearMap.BilinForm R V)
    (G : ι → V) (coeff : ι → R) (x : V) :
    B x (correction G coeff) = dotProduct (fun i => B x (G i)) coeff := by
  simp only [correction, B.sum_right, B.smul_right, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Each row of the negative Gram matrix computes the negative pairing
of its family vector with the actual correction. -/
theorem negativeGram_mulVec_apply (B : LinearMap.BilinForm R V)
    (G : ι → V) (coeff : ι → R) (i : ι) :
    (negativeGram B G *ᵥ coeff) i = -B (G i) (correction G coeff) := by
  rw [pairing_correction_right]
  simp only [negativeGram, Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib]

/-- The actual row equation determines every family-correction pairing. -/
theorem family_pairing_correction_of_solve (B : LinearMap.BilinForm R V)
    (K : V) (G : ι → V) (coeff : ι → R)
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G) (i : ι) :
    B (G i) (correction G coeff) = -sourceVector B K G i := by
  have hi := congrFun hrow i
  rw [negativeGram_mulVec_apply] at hi
  simpa only [neg_neg] using congrArg Neg.neg hi

/-- The canonical-correction pairing follows from its actual coefficients. -/
theorem canonical_pairing_correction (B : LinearMap.BilinForm R V)
    (K : V) (G : ι → V) (coeff : ι → R) :
    B K (correction G coeff) = dotProduct (sourceVector B K G) coeff :=
  pairing_correction_right B G coeff K

/-- The correction square is minus the source-coefficient pairing.
This consequence of the row equation does not require symmetry. -/
theorem correction_square_of_solve (B : LinearMap.BilinForm R V)
    (K : V) (G : ι → V) (coeff : ι → R)
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G) :
    B (correction G coeff) (correction G coeff) =
      -dotProduct (sourceVector B K G) coeff := by
  rw [pairing_correction_left]
  unfold dotProduct
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change coeff i * B (G i) (correction G coeff) = -(sourceVector B K G i * coeff i)
  rw [family_pairing_correction_of_solve B K G coeff hrow i]
  ring

/-- The actual corrected vector has square `K² + q · coeff`. -/
theorem correctedClass_square_of_solve (B : LinearMap.BilinForm R V)
    (hB : B.IsSymm) (K : V) (G : ι → V) (coeff : ι → R)
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G) :
    B (correctedClass K G coeff) (correctedClass K G coeff) =
      B K K + dotProduct (sourceVector B K G) coeff := by
  have hKD := canonical_pairing_correction B K G coeff
  have hDK := (hB.eq (correction G coeff) K).trans hKD
  have hDD := correction_square_of_solve B K G coeff hrow
  simp only [correctedClass, B.neg_left, B.neg_right, neg_neg,
    B.add_left, B.add_right, hKD, hDK, hDD]
  ring

/-- The degree formula is the actual pairing of the corrected class with
`C`; it does not require a matrix equation or invertibility. -/
theorem correctedClass_pairing (B : LinearMap.BilinForm R V)
    (hB : B.IsSymm) (K : V) (G : ι → V) (coeff : ι → R) (C : V) :
    B (correctedClass K G coeff) C =
      -B K C - dotProduct (contactVector B C G) coeff := by
  have hDC : B (correction G coeff) C = dotProduct (contactVector B C G) coeff :=
    (hB.eq (correction G coeff) C).trans (pairing_correction_right B G coeff C)
  rw [correctedClass, B.neg_left, B.add_left, hDC]
  ring

/-- Specializing an actual canonical pairing of negative one gives the
degree-one formula. The required adjunction equality remains explicit. -/
theorem correctedClass_pairing_of_neg_canonical_eq_one
    (B : LinearMap.BilinForm R V) (hB : B.IsSymm)
    (K : V) (G : ι → V) (coeff : ι → R) (C : V) (hKC : -B K C = 1) :
    B (correctedClass K G coeff) C =
      1 - dotProduct (contactVector B C G) coeff := by
  rw [correctedClass_pairing B hB, hKC]

section Inverse

variable [DecidableEq ι]

/-- Invertibility of the actual matrix proves that its inverse gives a
solution of the row equation. -/
theorem inverse_source_solves (B : LinearMap.BilinForm R V)
    (K : V) (G : ι → V) (hA : IsUnit (negativeGram B G)) :
    negativeGram B G *ᵥ ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G) =
      sourceVector B K G := by
  letI : Invertible (negativeGram B G) := hA.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- Every actual solution agrees with the inverse-matrix solution. -/
theorem coefficients_eq_inverse_of_solve (B : LinearMap.BilinForm R V)
    (K : V) (G : ι → V) (coeff : ι → R) (hA : IsUnit (negativeGram B G))
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G) :
    coeff = (negativeGram B G)⁻¹ *ᵥ sourceVector B K G := by
  letI : Invertible (negativeGram B G) := hA.invertible
  rw [← hrow, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]

/-- The square of an actual solved correction, in inverse-matrix form. -/
theorem correctedClass_square_inverse_of_solve (B : LinearMap.BilinForm R V)
    (hB : B.IsSymm) (K : V) (G : ι → V) (coeff : ι → R)
    (hA : IsUnit (negativeGram B G))
    (hrow : negativeGram B G *ᵥ coeff = sourceVector B K G) :
    B (correctedClass K G coeff) (correctedClass K G coeff) =
      B K K + dotProduct (sourceVector B K G)
        ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G) := by
  rw [correctedClass_square_of_solve B hB K G coeff hrow,
    ← coefficients_eq_inverse_of_solve B K G coeff hA hrow]

/-- The explicitly constructed inverse correction has the square formula,
with its row equation proved rather than supplied as an extra premise. -/
theorem correctedClass_square_inverse (B : LinearMap.BilinForm R V)
    (hB : B.IsSymm) (K : V) (G : ι → V) (hA : IsUnit (negativeGram B G)) :
    B (correctedClass K G ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G))
      (correctedClass K G ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G)) =
      B K K + dotProduct (sourceVector B K G)
        ((negativeGram B G)⁻¹ *ᵥ sourceVector B K G) :=
  correctedClass_square_of_solve B hB K G _ (inverse_source_solves B K G hA)

end Inverse

end KltDP.LinearAlgebra.CanonicalCorrection
