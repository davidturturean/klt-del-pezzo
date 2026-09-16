import KltDP.Examples.FrobeniusPicard

/-!
# Integral two-divisibility of independently selected Frobenius node vectors

For arbitrary finite subsets `A,B ⊆ Fin n`, this module proves that
`Σ A Fᵢ + Σ B Uᵢ` is twice an integral vector if and only if `A = B` and
`A.card` is even. The ambient module and vectors are the explicit integral
ones in `FrobeniusPicard`; no pairing or divisibility conclusion is stored
as a data field.

This is the integer-coordinate argument in the proof of the manuscript's
Theorem 10.2. It is valid for every `n`, including zero. Identifying these
vectors with an actual Picard basis and identifying all isolated nodes
remain geometric tasks. At `n = 3`, allowing the extra graph node gives a
different, seven-node code; that code is not asserted to be classified here.
-/

namespace KltDP.Examples.FrobeniusEvenSets

open KltDP.Examples.FrobeniusPicard
open scoped BigOperators

section Coordinates

variable {ι κ : Type*}

/-- Projection of a finite integral-vector sum to the `a` coordinate. -/
@[simp] theorem aCoordinate_sum (S : Finset κ) (f : κ → BlowupLattice ι) :
    (∑ i ∈ S, f i).1 = ∑ i ∈ S, (f i).1 := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (f i).1 + (∑ j ∈ S, f j).1 = (f i).1 + ∑ j ∈ S, (f j).1
    rw [ih]

/-- Projection of a finite integral-vector sum to the `b` coordinate. -/
@[simp] theorem bCoordinate_sum (S : Finset κ) (f : κ → BlowupLattice ι) :
    (∑ i ∈ S, f i).2.1 = ∑ i ∈ S, (f i).2.1 := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (f i).2.1 + (∑ j ∈ S, f j).2.1 = (f i).2.1 + ∑ j ∈ S, (f j).2.1
    rw [ih]

/-- Projection of a finite integral-vector sum to any exceptional coordinate. -/
@[simp] theorem exceptionalCoordinate_sum (S : Finset κ) (f : κ → BlowupLattice ι)
    (k : ι) :
    (∑ i ∈ S, f i).2.2 k = ∑ i ∈ S, (f i).2.2 k := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (f i).2.2 k + (∑ j ∈ S, f j).2.2 k =
      (f i).2.2 k + ∑ j ∈ S, (f j).2.2 k
    rw [ih]

end Coordinates

/-- Independently selected strict-fiber and chain-component vectors. -/
def selectedNodes (n : ℕ) (A B : Finset (Fin n)) : PicardVector 2 n :=
  (∑ i ∈ A, fiberVector 2 n i) + ∑ i ∈ B, nodeVector n i

@[simp] theorem selectedNodes_a (n : ℕ) (A B : Finset (Fin n)) :
    (selectedNodes n A B).1 = 0 := by
  simp [selectedNodes, fiberVector, nodeVector, exceptionalDifference, exceptional]

@[simp] theorem selectedNodes_b (n : ℕ) (A B : Finset (Fin n)) :
    (selectedNodes n A B).2.1 = (A.card : ℤ) := by
  simp [selectedNodes, fiberVector, nodeVector, exceptionalDifference, exceptional]

/-- The first exceptional coordinate records the difference of the two selections. -/
@[simp] theorem selectedNodes_firstExceptional (n : ℕ) (A B : Finset (Fin n))
    (i : Fin n) :
    (selectedNodes n A B).2.2 (i, 0) =
      (if i ∈ A then -1 else 0) + (if i ∈ B then 1 else 0) := by
  simp [selectedNodes, fiberVector, nodeVector, exceptionalDifference, exceptional]

/-- The second exceptional coordinate records the negative sum of the selections. -/
@[simp] theorem selectedNodes_secondExceptional (n : ℕ) (A B : Finset (Fin n))
    (i : Fin n) :
    (selectedNodes n A B).2.2 (i, 1) =
      (if i ∈ A then -1 else 0) - (if i ∈ B then 1 else 0) := by
  simp [selectedNodes, fiberVector, nodeVector, exceptionalDifference, exceptional,
    sub_eq_add_neg]

theorem selectedNodes_self (n : ℕ) (A : Finset (Fin n)) :
    selectedNodes n A A = ∑ i ∈ A, (fiberVector 2 n i + nodeVector n i) := by
  simp [selectedNodes, Finset.sum_add_distrib]

/-- An unmatched selected node would give an odd exceptional coordinate. -/
theorem selections_eq_of_two_divisible (n : ℕ) (A B : Finset (Fin n))
    (h : ∃ M : PicardVector 2 n, (2 : ℤ) • M = selectedNodes n A B) : A = B := by
  obtain ⟨M, hM⟩ := h
  apply Finset.ext
  intro i
  have he := congrArg (fun x : PicardVector 2 n => x.2.2 (i, 0)) hM
  have hcoord : (2 : ℤ) * M.2.2 (i, 0) =
      (if i ∈ A then -1 else 0) + (if i ∈ B then 1 else 0) := by
    simpa [smul_eq_mul] using he
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    simp [hA, hB] at hcoord ⊢ <;> omega

/-- Projection to the integral `b` coordinate forces even selection cardinality. -/
theorem even_card_of_two_divisible (n : ℕ) (A B : Finset (Fin n))
    (h : ∃ M : PicardVector 2 n, (2 : ℤ) • M = selectedNodes n A B) : Even A.card := by
  obtain ⟨M, hM⟩ := h
  have hb := congrArg (fun x : PicardVector 2 n => x.2.1) hM
  have hcoord : (2 : ℤ) * M.2.1 = (A.card : ℤ) := by
    simpa [smul_eq_mul] using hb
  have heven : Even (A.card : ℤ) := ⟨M.2.1, by linarith⟩
  exact_mod_cast heven

/-- Full classification among independently selected subsets, in both directions. -/
theorem selectedNodes_two_divisible_iff (n : ℕ) (A B : Finset (Fin n)) :
    (∃ M : PicardVector 2 n, (2 : ℤ) • M = selectedNodes n A B) ↔
      A = B ∧ Even A.card := by
  constructor
  · intro h
    exact ⟨selections_eq_of_two_divisible n A B h, even_card_of_two_divisible n A B h⟩
  · rintro ⟨hAB, hA⟩
    obtain ⟨M, hM⟩ := paired_subset_half_sum n A hA
    refine ⟨M, ?_⟩
    rw [← hAB, selectedNodes_self]
    exact hM

/-- The explicit integral half-class corresponding to a witness `|A| = m + m`. -/
theorem selectedNodes_explicit_half (n : ℕ) (A : Finset (Fin n))
    (m : ℕ) (hm : A.card = m + m) :
    (2 : ℤ) • ((m : ℤ) • b - ∑ i ∈ A, lastVectorTwo n i) = selectedNodes n A A := by
  rw [selectedNodes_self, paired_subset_sum]
  simp only [hm, Nat.cast_add, add_smul, smul_sub, two_smul]

end KltDP.Examples.FrobeniusEvenSets
