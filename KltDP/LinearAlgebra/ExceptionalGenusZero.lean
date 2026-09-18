import KltDP.LinearAlgebra.ExceptionalGenusElimination
import Mathlib.Data.Fintype.Card

/-!
# Genus zero from integral negative canonical intersection rows

For an integral matrix with negative definite quadratic form and nonnegative
off-diagonal entries, canonical discrepancy rows with every discrepancy
strictly greater than `-1` force all natural genera to be zero.

The proof inducts on the actual finite cardinal. A negative canonical row
singles out a genus-zero `-1` diagonal entry; its Schur complement has the
same canonical rows after the proved natural binomial genus correction.
If all rows are nonnegative, the Stieltjes maximum principle closes the proof.
No discrepancy upper bound, minimal diagonal bound, graph condition, or
geometric contraction is assumed.
-/

noncomputable section

open Matrix
open scoped BigOperators

universe u

namespace KltDP.LinearAlgebra.ExceptionalGenusZero

open ExceptionalGenusElimination

private theorem genus_zero_by_card : ∀ n : ℕ,
    ∀ {I : Type u} [Fintype I] [DecidableEq I], Fintype.card I = n →
    ∀ (M : Matrix I I ℚ), (-M).PosDef →
    (∀ i j, ∃ z : ℤ, M i j = z) →
    (∀ i j, i ≠ j → 0 ≤ M i j) →
    ∀ (g : I → ℕ) (d : I → ℚ), (∀ i, -1 < d i) →
    M *ᵥ d = (fun i => 2 * (g i : ℚ) - 2 - M i i) →
    ∀ i, g i = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I instF instD hcard M hpos hintegral hoff g d hlower hrow
    by_cases hrhs : ∀ i, 0 ≤ 2 * (g i : ℚ) - 2 - M i i
    · exact genus_zero_of_nonnegative_rows M hpos hoff g d hlower hrow hrhs
    · push_neg at hrhs
      obtain ⟨i, hi⟩ := hrhs
      obtain ⟨hgenus, hdiag⟩ := pivot_of_negative_row M hpos g i (hintegral i i) hi
      let J := {j : I // j ≠ i}
      let S : Matrix J J ℚ := minusOneSchur M i
      have hsymm (j k : I) : M j k = M k j := by
        have h := (hpos.1.apply j k).symm
        simpa only [star_trivial, Matrix.neg_apply, neg_inj] using h
      have hnegative : ∀ x : I → ℚ, x ≠ 0 → dotProduct x (M *ᵥ x) < 0 := by
        intro x hx
        have h := hpos.2 x hx
        have hn : 0 < -dotProduct x (M *ᵥ x) := by
          simpa only [star_trivial, neg_mulVec, dotProduct_neg] using h
        exact neg_pos.mp hn
      have hposS : (-S).PosDef := by
        constructor
        · apply Matrix.IsHermitian.ext
          intro j k
          simp only [star_trivial, Matrix.neg_apply]
          exact congrArg Neg.neg (minusOneSchur_symmetric M i hsymm k j)
        · intro x hx
          have hn := minusOneSchur_negative M i hdiag hnegative x hx
          simpa only [star_trivial, neg_mulVec, dotProduct_neg] using neg_pos.mpr hn
      have hcontacts (j : J) : ∃ a : ℕ, (a : ℚ) = M j i := by
        obtain ⟨z, hz⟩ := hintegral j i
        have hnonneg := hoff j i j.property
        rw [hz] at hnonneg
        have hznonneg : 0 ≤ z := by exact_mod_cast hnonneg
        refine ⟨z.toNat, ?_⟩
        have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hznonneg
        calc
          (z.toNat : ℚ) = (z : ℚ) := by exact_mod_cast hcast
          _ = M j i := hz.symm
      choose contact hcontact using hcontacts
      let g' : J → ℕ := fun j => g j + (contact j).choose 2
      let d' : J → ℚ := fun j => d j
      have hrowS : S *ᵥ d' = fun j => 2 * (g' j : ℚ) - 2 - S j j :=
        minusOneSchur_canonical_rows M i hsymm hdiag g hgenus d hrow contact hcontact
      have hcardJ : Fintype.card J < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x := i) (by simp)
      have hind : ∀ j : J, g' j = 0 :=
        ih (Fintype.card J) hcardJ (I := J) rfl S hposS
          (minusOneSchur_integral M i hintegral)
          (minusOneSchur_offDiagonal_nonnegative M i hoff)
          g' d' (fun j => hlower j) hrowS
      intro j
      by_cases hj : j = i
      · simpa only [hj] using hgenus
      · have hz := hind ⟨j, hj⟩
        change g j + (contact ⟨j, hj⟩).choose 2 = 0 at hz
        omega

/-- Integral canonical intersection rows with strictly klt discrepancies
force every natural arithmetic genus to vanish. The symmetry is already
contained in the standard positive-definiteness hypothesis on `-M`. -/
theorem genus_zero {I : Type u} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℚ) (hpos : (-M).PosDef)
    (hintegral : ∀ i j, ∃ z : ℤ, M i j = z)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (g : I → ℕ) (d : I → ℚ) (hlower : ∀ i, -1 < d i)
    (hrow : M *ᵥ d = fun i => 2 * (g i : ℚ) - 2 - M i i) :
    ∀ i, g i = 0 :=
  genus_zero_by_card (Fintype.card I) rfl M hpos hintegral hoff g d hlower hrow

end KltDP.LinearAlgebra.ExceptionalGenusZero

#print axioms KltDP.LinearAlgebra.ExceptionalGenusZero.genus_zero
