import KltDP.LinearAlgebra.Stieltjes
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Cast

/-!
# Singleton elimination for integral canonical intersection rows

The explicit Schur complement of a diagonal entry `-1` preserves strict
negative definiteness. If that vertex has genus zero, the canonical rows
are preserved by adding `choose(contact, 2)` to each remaining genus.
This statement allows arbitrary nonnegative integral contacts.

Pinned Mathlib's Schur-complement identities and the project's bordered
matrix/strict-positivity adapters were reviewed first. The short finite-sum
adapter here retains the original subtype labels and avoids a block reindex.
It reuses `Fintype.sum_eq_add_sum_subtype_ne` and `Nat.cast_choose_two`.
The Stieltjes maximum principle closes the branch with nonnegative rows.
-/

noncomputable section

open Matrix
open scoped BigOperators

universe u

namespace KltDP.LinearAlgebra.ExceptionalGenusElimination

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- Eliminate the coordinate `i` whose diagonal entry is `-1`. -/
def minusOneSchur (M : Matrix I I ℚ) (i : I) :
    Matrix {j : I // j ≠ i} {j : I // j ≠ i} ℚ :=
  fun j k => M j k + M j i * M i k

/-- Extend a remaining vector to the orthogonal complement of coordinate `i`. -/
def minusOneLift (M : Matrix I I ℚ) (i : I)
    (x : {j : I // j ≠ i} → ℚ) : I → ℚ :=
  fun j => if h : j = i then ∑ k : {k : I // k ≠ i}, M i k * x k else x ⟨j, h⟩

@[simp] theorem minusOneLift_pivot (M : Matrix I I ℚ) (i : I)
    (x : {j : I // j ≠ i} → ℚ) :
    minusOneLift M i x i = ∑ k : {k : I // k ≠ i}, M i k * x k := by
  simp [minusOneLift]

@[simp] theorem minusOneLift_remaining (M : Matrix I I ℚ) (i : I)
    (x : {j : I // j ≠ i} → ℚ) (j : {j : I // j ≠ i}) :
    minusOneLift M i x j = x j := by
  simp [minusOneLift, j.property]

/-- Gaussian elimination at `-1`, with the original remaining coordinates. -/
theorem minusOneSchur_mulVec (M : Matrix I I ℚ) (i : I)
    (hdiag : M i i = -1) (d : I → ℚ) (j : {j : I // j ≠ i}) :
    (minusOneSchur M i *ᵥ (fun k => d k)) j =
      (M *ᵥ d) j + M j i * (M *ᵥ d) i := by
  have hi := Fintype.sum_eq_add_sum_subtype_ne (fun k => M i k * d k) i
  have hj := Fintype.sum_eq_add_sum_subtype_ne (fun k => M j k * d k) i
  change (M *ᵥ d) i = M i i * d i + ∑ k : {k : I // k ≠ i}, M i k * d k at hi
  change (M *ᵥ d) j = M j i * d i + ∑ k : {k : I // k ≠ i}, M j k * d k at hj
  rw [hdiag] at hi
  rw [hi, hj]
  change (∑ k : {k : I // k ≠ i}, (M j k + M j i * M i k) * d k) = _
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem minusOneLift_mulVec_pivot (M : Matrix I I ℚ) (i : I)
    (hdiag : M i i = -1) (x : {j : I // j ≠ i} → ℚ) :
    (M *ᵥ minusOneLift M i x) i = 0 := by
  change (∑ j, M i j * minusOneLift M i x j) = 0
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
  simp only [minusOneLift_pivot, minusOneLift_remaining, hdiag, neg_one_mul,
    neg_add_cancel]

/-- The lifted vector has exactly the Schur-complement quadratic value. -/
theorem minusOneLift_quadratic (M : Matrix I I ℚ) (i : I)
    (hdiag : M i i = -1) (x : {j : I // j ≠ i} → ℚ) :
    dotProduct (minusOneLift M i x) (M *ᵥ minusOneLift M i x) =
      dotProduct x (minusOneSchur M i *ᵥ x) := by
  have hrestrict : (fun k : {k : I // k ≠ i} => minusOneLift M i x k) = x := by
    funext k
    exact minusOneLift_remaining M i x k
  have himage (j : {j : I // j ≠ i}) :
      (M *ᵥ minusOneLift M i x) j = (minusOneSchur M i *ᵥ x) j := by
    have h := minusOneSchur_mulVec M i hdiag (minusOneLift M i x) j
    rw [hrestrict, minusOneLift_mulVec_pivot M i hdiag, mul_zero, add_zero] at h
    exact h.symm
  change (∑ j, minusOneLift M i x j * (M *ᵥ minusOneLift M i x) j) = _
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i,
    minusOneLift_mulVec_pivot M i hdiag, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [minusOneLift_remaining, himage]

/-- Strict negative definiteness descends through a `-1` diagonal entry. -/
theorem minusOneSchur_negative (M : Matrix I I ℚ) (i : I)
    (hdiag : M i i = -1)
    (hnegative : ∀ x : I → ℚ, x ≠ 0 → dotProduct x (M *ᵥ x) < 0) :
    ∀ x : {j : I // j ≠ i} → ℚ, x ≠ 0 →
      dotProduct x (minusOneSchur M i *ᵥ x) < 0 := by
  intro x hx
  have hne : minusOneLift M i x ≠ 0 := by
    intro hzero
    apply hx
    funext j
    have h := congrFun hzero j
    simpa only [minusOneLift_remaining, Pi.zero_apply] using h
  simpa only [minusOneLift_quadratic M i hdiag] using hnegative _ hne

theorem minusOneSchur_symmetric (M : Matrix I I ℚ) (i : I)
    (hsymm : ∀ j k, M j k = M k j) :
    ∀ j k, minusOneSchur M i j k = minusOneSchur M i k j := by
  intro j k
  dsimp only [minusOneSchur]
  rw [hsymm j k, hsymm j i, hsymm i k]
  ring

theorem minusOneSchur_offDiagonal_nonnegative (M : Matrix I I ℚ) (i : I)
    (hoff : ∀ j k, j ≠ k → 0 ≤ M j k) :
    ∀ j k, j ≠ k → 0 ≤ minusOneSchur M i j k := by
  intro j k hjk
  exact add_nonneg (hoff j k (fun h => hjk (Subtype.ext h)))
    (mul_nonneg (hoff j i j.property) (hoff i k k.property.symm))

theorem minusOneSchur_integral (M : Matrix I I ℚ) (i : I)
    (hintegral : ∀ j k, ∃ z : ℤ, M j k = z) :
    ∀ j k, ∃ z : ℤ, minusOneSchur M i j k = z := by
  intro j k
  obtain ⟨a, ha⟩ := hintegral j k
  obtain ⟨b, hb⟩ := hintegral j i
  obtain ⟨c, hc⟩ := hintegral i k
  exact ⟨a + b * c, by simp [minusOneSchur, ha, hb, hc]⟩

/-- The literal canonical rows survive elimination after the natural genus
correction. The contact numbers may be larger than one. -/
theorem minusOneSchur_canonical_rows (M : Matrix I I ℚ) (i : I)
    (hsymm : ∀ j k, M j k = M k j) (hdiag : M i i = -1)
    (g : I → ℕ) (hgenus : g i = 0) (d : I → ℚ)
    (hrow : M *ᵥ d = fun j => 2 * (g j : ℚ) - 2 - M j j)
    (contact : {j : I // j ≠ i} → ℕ)
    (hcontact : ∀ j, (contact j : ℚ) = M j i) :
    minusOneSchur M i *ᵥ (fun j => d j) =
      fun j : {j : I // j ≠ i} => 2 * ((g j + (contact j).choose 2 : ℕ) : ℚ) - 2 -
        minusOneSchur M i j j := by
  funext j
  rw [minusOneSchur_mulVec M i hdiag]
  rw [hrow]
  simp only [hgenus, Nat.cast_zero, hdiag, Nat.cast_add, minusOneSchur,
    Nat.cast_choose_two]
  rw [hcontact, hsymm i j]
  ring

/-- A negative-definite matrix has strictly negative diagonal entries. -/
theorem diagonal_negative (M : Matrix I I ℚ) (hpos : (-M).PosDef) (i : I) :
    M i i < 0 := by
  have hne : (Pi.single i 1 : I → ℚ) ≠ 0 := by
    intro hzero
    have h := congrFun hzero i
    simpa using h
  have h := hpos.2 (Pi.single i 1) hne
  have hn : 0 < -M i i := by
    simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct,
      one_mul, Matrix.transpose_apply, Matrix.neg_apply] using h
  exact neg_pos.mp hn

/-- Nonnegative canonical rows force every natural genus to vanish. The
coefficient upper bound is obtained from the Stieltjes maximum principle. -/
theorem genus_zero_of_nonnegative_rows (M : Matrix I I ℚ) (hpos : (-M).PosDef)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (g : I → ℕ) (d : I → ℚ) (hlower : ∀ i, -1 < d i)
    (hrow : M *ᵥ d = fun i => 2 * (g i : ℚ) - 2 - M i i)
    (hrhs : ∀ i, 0 ≤ 2 * (g i : ℚ) - 2 - M i i) :
    ∀ i, g i = 0 := by
  have himage : ∀ i, 0 ≤ ((-M) *ᵥ (-d)) i := by
    simpa only [neg_mulVec, mulVec_neg, neg_neg, hrow] using hrhs
  have hnonneg := KltDP.LinearAlgebra.nonneg_of_mulVec_nonneg hpos
    (fun i j hij => neg_nonpos.mpr (hoff i j hij)) himage
  have hupper (i : I) : d i ≤ 0 := neg_nonneg.mp (hnonneg i)
  intro i
  have hsum : (∑ j : {j : I // j ≠ i}, M i j * d j) ≤ 0 :=
    Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hoff i j j.property.symm) (hupper j)
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne (fun j => M i j * d j) i
  change (M *ᵥ d) i = M i i * d i + ∑ j : {j : I // j ≠ i}, M i j * d j at hsplit
  rw [hrow] at hsplit
  change 2 * (g i : ℚ) - 2 - M i i =
    M i i * d i + ∑ j : {j : I // j ≠ i}, M i j * d j at hsplit
  have hleft : M i i * (1 + d i) < 0 :=
    mul_neg_of_neg_of_pos (diagonal_negative M hpos i) (by linarith only [hlower i])
  have heq : 2 * (g i : ℚ) - 2 =
      M i i * (1 + d i) + ∑ j : {j : I // j ≠ i}, M i j * d j := by
    calc
      2 * (g i : ℚ) - 2 = (2 * (g i : ℚ) - 2 - M i i) + M i i := by ring
      _ = (M i i * d i + ∑ j : {j : I // j ≠ i}, M i j * d j) + M i i := by
        rw [hsplit]
      _ = M i i * (1 + d i) + ∑ j : {j : I // j ≠ i}, M i j * d j := by ring
  have hgenusneg : 2 * (g i : ℚ) - 2 < 0 := by
    rw [heq]
    exact add_neg_of_neg_of_nonpos hleft hsum
  have hg : (g i : ℚ) < 1 := by linarith only [hgenusneg]
  have hgNat : g i < 1 := by exact_mod_cast hg
  omega

/-- Integrality singles out a genus-zero `-1` vertex whenever a canonical
right-hand side is negative. No minimality assumption enters this step. -/
theorem pivot_of_negative_row (M : Matrix I I ℚ) (hpos : (-M).PosDef)
    (g : I → ℕ) (i : I) (hintegral : ∃ z : ℤ, M i i = z)
    (hrow : 2 * (g i : ℚ) - 2 - M i i < 0) :
    g i = 0 ∧ M i i = -1 := by
  obtain ⟨z, hz⟩ := hintegral
  have hdiag := diagonal_negative M hpos i
  rw [hz] at hdiag hrow
  have hzneg : z < 0 := by exact_mod_cast hdiag
  have hrowInt : (2 : ℤ) * (g i : ℤ) - 2 - z < 0 := by exact_mod_cast hrow
  have hgenus : g i = 0 := by omega
  have hzvalue : z = -1 := by omega
  refine ⟨hgenus, ?_⟩
  rw [hz, hzvalue]
  norm_num

end KltDP.LinearAlgebra.ExceptionalGenusElimination

#print axioms KltDP.LinearAlgebra.ExceptionalGenusElimination.minusOneSchur_negative
#print axioms KltDP.LinearAlgebra.ExceptionalGenusElimination.minusOneSchur_canonical_rows
#print axioms KltDP.LinearAlgebra.ExceptionalGenusElimination.genus_zero_of_nonnegative_rows
#print axioms KltDP.LinearAlgebra.ExceptionalGenusElimination.pivot_of_negative_row
