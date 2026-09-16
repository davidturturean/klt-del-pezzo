import KltDP.LinearAlgebra.Stieltjes
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Restricting a Stieltjes system to actual principal coordinates

An injective index map selects an actual principal submatrix. Restricting a
nonnegative solution drops nonpositive off-diagonal summands from each row,
so the restricted row image dominates the restricted source. Positive
definiteness transfers through the actual coordinate-embedding matrix, and
the Stieltjes maximum principle gives the inverse-source comparison.
-/

namespace KltDP.LinearAlgebra

open Matrix

variable {I J 𝕜 : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Field 𝕜]

/-- The actual coordinate embedding, with one unit entry in each selected
column and zeros elsewhere. Injectivity of the index map is a theorem
hypothesis, not part of this matrix definition. -/
def coordinateEmbeddingMatrix (e : J → I) : Matrix I J 𝕜 :=
  (1 : Matrix I I 𝕜).submatrix id e

omit [Fintype I] in
/-- Reading an embedded vector at a selected coordinate returns its original
coordinate. This proves that the embedding loses no vectors. -/
theorem coordinateEmbeddingMatrix_mulVec_apply (e : J → I) (he : Function.Injective e)
    (x : J → 𝕜) (j : J) : (coordinateEmbeddingMatrix e *ᵥ x) (e j) = x j := by
  simp [coordinateEmbeddingMatrix, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
    Matrix.one_apply, he.eq_iff]

omit [Fintype I] in
/-- The actual embedding matrix is injective on vectors. -/
theorem coordinateEmbeddingMatrix_mulVec_injective (e : J → I)
    (he : Function.Injective e) : Function.Injective (coordinateEmbeddingMatrix (𝕜 := 𝕜) e).mulVec := by
  intro x y hxy
  ext j
  have h := congrFun hxy (e j)
  simpa only [coordinateEmbeddingMatrix_mulVec_apply e he] using h

section Star

variable [StarRing 𝕜]

omit [Fintype J] [DecidableEq J] in
/-- The principal matrix is the actual congruence by the coordinate embedding.
This identity does not require the index map to be injective. -/
theorem coordinateEmbeddingMatrix_congruence (A : Matrix I I 𝕜) (e : J → I) :
    (coordinateEmbeddingMatrix e)ᴴ * A * coordinateEmbeddingMatrix e = A.submatrix e e := by
  simp only [coordinateEmbeddingMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  calc
    _ = ((1 : Matrix I I 𝕜) * A * 1).submatrix e e := by
      rw [Matrix.submatrix_mul (he₂ := Function.bijective_id),
        Matrix.submatrix_mul (he₂ := Function.bijective_id), Matrix.submatrix_id_id]
    _ = _ := by rw [Matrix.one_mul, Matrix.mul_one]

end Star

section Ordered

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq J] in
/-- Restricting a nonnegative vector to principal coordinates deletes only
nonpositive summands from the full row. This is the exact row inequality
used by the manuscript's path comparison. -/
theorem mulVec_le_principal_mulVec (A : Matrix I I 𝕜) (e : J → I)
    (he : Function.Injective e) (coeff : I → 𝕜)
    (hcoeff : ∀ i, 0 ≤ coeff i) (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (j : J) :
    (A *ᵥ coeff) (e j) ≤ ((A.submatrix e e) *ᵥ (coeff ∘ e)) j := by
  let selected : Finset I := Finset.univ.image e
  have hsum : ∑ i ∈ selected, A (e j) i * coeff i =
      ((A.submatrix e e) *ᵥ (coeff ∘ e)) j := by
    dsimp [selected]
    rw [Finset.sum_image (fun a _ b _ hab => he hab)]
    rfl
  have hneg : ∑ i ∈ selected, -(A (e j) i * coeff i) ≤
      ∑ i : I, -(A (e j) i * coeff i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
    intro i _ hi
    apply neg_nonneg.mpr
    have hji : e j ≠ i := by
      intro h
      apply hi
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩
    exact mul_nonpos_of_nonpos_of_nonneg (hOff (e j) i hji) (hcoeff i)
  simp only [Finset.sum_neg_distrib, neg_le_neg_iff] at hneg
  rw [hsum] at hneg
  exact hneg

omit [DecidableEq J] in
/-- A full system equation supplies the principal row comparison; the
comparison is proved from actual omitted summands rather than assumed. -/
theorem source_le_principal_mulVec (A : Matrix I I 𝕜) (e : J → I)
    (he : Function.Injective e) (coeff source : I → 𝕜)
    (hcoeff : ∀ i, 0 ≤ coeff i) (hOff : ∀ i j, i ≠ j → A i j ≤ 0)
    (heq : A *ᵥ coeff = source) :
    ∀ j, source (e j) ≤ ((A.submatrix e e) *ᵥ (coeff ∘ e)) j := by
  intro j
  rw [← heq]
  exact mulVec_le_principal_mulVec A e he coeff hcoeff hOff j

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] in
/-- The diagonal-minus-two source restricts to the actual principal source. -/
theorem principal_diagonal_source (A : Matrix I I 𝕜) (e : J → I) :
    (fun j => A.submatrix e e j j - 2) = (fun i => A i i - 2) ∘ e := rfl

variable [StarRing 𝕜] [TrivialStar 𝕜]

omit [IsStrictOrderedRing 𝕜] [TrivialStar 𝕜] in
/-- Positive definiteness of an actual principal submatrix. The pin has the
congruence theorem; this adapter supplies its injective embedding hypothesis. -/
theorem posDef_principal_submatrix {A : Matrix I I 𝕜} (hA : A.PosDef)
    (e : J → I) (he : Function.Injective e) : (A.submatrix e e).PosDef := by
  rw [← coordinateEmbeddingMatrix_congruence A e]
  exact hA.conjTranspose_mul_mul_same (coordinateEmbeddingMatrix_mulVec_injective e he)

/-- The principal inverse-source solution lies below the restriction of an
actual nonnegative full solution. All matrix and source hypotheses are stated. -/
theorem principal_inverse_source_le (A : Matrix I I 𝕜) (e : J → I)
    (he : Function.Injective e) (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (coeff source : I → 𝕜)
    (hcoeff : ∀ i, 0 ≤ coeff i) (heq : A *ᵥ coeff = source) :
    ∀ j, ((A.submatrix e e)⁻¹ *ᵥ (source ∘ e)) j ≤ coeff (e j) := by
  have hB := posDef_principal_submatrix hA e he
  have hBoff : ∀ i j, i ≠ j → A.submatrix e e i j ≤ 0 := by
    intro i j hij
    exact hOff (e i) (e j) (fun h => hij (he h))
  letI : Invertible (A.submatrix e e) := (isUnit_of_posDef hB).invertible
  have hrows := source_le_principal_mulVec A e he coeff source hcoeff hOff heq
  have hdiff : ∀ j, 0 ≤ ((A.submatrix e e) *ᵥ
      ((coeff ∘ e) - (A.submatrix e e)⁻¹ *ᵥ (source ∘ e))) j := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]
    intro j
    exact sub_nonneg.mpr (hrows j)
  have hnonneg := nonneg_of_mulVec_nonneg hB hBoff hdiff
  intro j
  exact sub_nonneg.mp (hnonneg j)

/-- For a nonnegative source, comparison applies to the actual full inverse
solution. Its nonnegativity and full system equation are derived here. -/
theorem principal_inverse_mulVec_le (A : Matrix I I 𝕜) (e : J → I)
    (he : Function.Injective e) (hA : A.PosDef)
    (hOff : ∀ i j, i ≠ j → A i j ≤ 0) (source : I → 𝕜)
    (hsource : ∀ i, 0 ≤ source i) :
    ∀ j, ((A.submatrix e e)⁻¹ *ᵥ (source ∘ e)) j ≤ (A⁻¹ *ᵥ source) (e j) := by
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  apply principal_inverse_source_le A e he hA hOff (A⁻¹ *ᵥ source) source
    (stieltjes_inverse_mulVec_nonnegative hA hOff hsource)
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

end Ordered

end KltDP.LinearAlgebra
