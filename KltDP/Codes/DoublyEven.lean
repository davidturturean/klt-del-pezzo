import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# Doubly-even binary codes of short length

Words are actual finite vectors over `ZMod 2`, and codes are submodules of
that vector space. Weight is mathlib's `hammingNorm`, the number of nonzero
coordinates. A doubly-even code is required only to have weights divisible
by four; the short-length classifications and dimension bounds are proved.

These are the elementary coding-theoretic consequences used in the proof
of Lemma 5.3 of the frozen manuscript (lines 1395–1430). They do not construct
the Picard code or prove its dimension lower bound or Riemann--Roch parity.
-/

namespace KltDP.Codes

abbrev BinaryWord (ι : Type*) := ι → ZMod 2

/-- The vector having value one at every coordinate, including on an empty index type. -/
def ones (ι : Type*) : BinaryWord ι := fun _ => 1

/-- Divisibility of the actual Hamming weight by four. -/
def DoublyEvenWord {ι : Type*} [Fintype ι] (x : BinaryWord ι) : Prop :=
  4 ∣ hammingNorm x

/-- A binary linear code whose every word has Hamming weight divisible by four. -/
def DoublyEvenCode {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (BinaryWord ι)) : Prop :=
  ∀ x ∈ C, DoublyEvenWord x

/-- The short-length vanishing argument works over any alphabet with zero. -/
theorem eq_zero_of_four_dvd_weight_of_card_lt_four
    {ι α : Type*} [Fintype ι] [Zero α] [DecidableEq α]
    (x : ι → α) (hx : 4 ∣ hammingNorm x) (hι : Fintype.card ι < 4) : x = 0 := by
  apply hammingNorm_eq_zero.mp
  have hle : hammingNorm x ≤ Fintype.card ι := hammingNorm_le_card_fintype
  rcases hx with ⟨m, hm⟩
  omega

/-- No nonzero doubly-even word has length less than four. -/
theorem doublyEvenWord_eq_zero_of_card_lt_four
    {ι : Type*} [Fintype ι] (x : BinaryWord ι)
    (hx : DoublyEvenWord x) (hι : Fintype.card ι < 4) : x = 0 :=
  eq_zero_of_four_dvd_weight_of_card_lt_four x hx hι

theorem binary_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem binary_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (binary_eq_zero_or_one a).resolve_left ha

@[simp] theorem weight_ones {ι : Type*} [Fintype ι] :
    hammingNorm (ones ι) = Fintype.card ι := by
  simp [hammingNorm, ones]

/-- A binary word has maximal weight exactly when every coordinate is one. -/
theorem weight_eq_card_iff_eq_ones {ι : Type*} [Fintype ι] (x : BinaryWord ι) :
    hammingNorm x = Fintype.card ι ↔ x = ones ι := by
  constructor
  · intro hx
    have hfull : (Finset.univ.filter (fun i => x i ≠ 0)).card =
        (Finset.univ : Finset ι).card := by
      simpa only [hammingNorm, Finset.card_univ] using hx
    funext i
    exact binary_eq_one_of_ne_zero
      ((Finset.card_filter_eq_iff.mp hfull) i (Finset.mem_univ i))
  · rintro rfl
    exact weight_ones

/-- At length four the two possible doubly-even words are zero and all-ones. -/
theorem doublyEvenWord_iff_zero_or_ones_of_card_eq_four
    {ι : Type*} [Fintype ι] (x : BinaryWord ι) (hι : Fintype.card ι = 4) :
    DoublyEvenWord x ↔ x = 0 ∨ x = ones ι := by
  constructor
  · intro hx
    have hle : hammingNorm x ≤ Fintype.card ι := hammingNorm_le_card_fintype
    have hcases : hammingNorm x = 0 ∨ hammingNorm x = 4 := by
      rcases hx with ⟨m, hm⟩
      omega
    rcases hcases with hz | hfull
    · exact Or.inl (hammingNorm_eq_zero.mp hz)
    · exact Or.inr ((weight_eq_card_iff_eq_ones x).mp (hfull.trans hι.symm))
  · rintro (rfl | rfl)
    · simp [DoublyEvenWord]
    · simp [DoublyEvenWord, hι]

/-- A doubly-even code of length less than four is the zero subspace. -/
theorem doublyEvenCode_eq_bot_of_card_lt_four
    {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (BinaryWord ι))
    (hC : DoublyEvenCode C) (hι : Fintype.card ι < 4) : C = ⊥ := by
  apply C.eq_bot_iff.mpr
  intro x hx
  exact doublyEvenWord_eq_zero_of_card_lt_four x (hC x hx) hι

/-- In particular its dimension is zero, without any bound assumed on its dimension. -/
theorem doublyEvenCode_finrank_eq_zero_of_card_lt_four
    {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (BinaryWord ι))
    (hC : DoublyEvenCode C) (hι : Fintype.card ι < 4) :
    Module.finrank (ZMod 2) C = 0 := by
  rw [doublyEvenCode_eq_bot_of_card_lt_four C hC hι, finrank_bot]

/-- A length-four doubly-even code is contained in the all-ones line. -/
theorem doublyEvenCode_le_span_ones_of_card_eq_four
    {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (BinaryWord ι))
    (hC : DoublyEvenCode C) (hι : Fintype.card ι = 4) :
    C ≤ Submodule.span (ZMod 2) {ones ι} := by
  intro x hx
  rcases (doublyEvenWord_iff_zero_or_ones_of_card_eq_four x hι).mp
    (hC x hx) with rfl | rfl
  · exact Submodule.zero_mem _
  · exact Submodule.mem_span_singleton_self _

/-- The singleton-span bound yields dimension at most one. -/
theorem doublyEvenCode_finrank_le_one_of_card_eq_four
    {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (BinaryWord ι))
    (hC : DoublyEvenCode C) (hι : Fintype.card ι = 4) :
    Module.finrank (ZMod 2) C ≤ 1 := by
  classical
  calc
    Module.finrank (ZMod 2) C ≤
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {ones ι}) :=
      Submodule.finrank_mono (doublyEvenCode_le_span_ones_of_card_eq_four C hC hι)
    _ ≤ 1 := by
      simpa using (finrank_span_le_card (R := ZMod 2) ({ones ι} : Set (BinaryWord ι)))

/-- A positive dimension forces the actual all-ones word into the code. -/
theorem ones_mem_of_doublyEvenCode_of_card_eq_four_of_finrank_pos
    {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (BinaryWord ι))
    (hC : DoublyEvenCode C) (hι : Fintype.card ι = 4)
    (hpos : 0 < Module.finrank (ZMod 2) C) : ones ι ∈ C := by
  have hbot : C ≠ ⊥ := by
    rintro rfl
    simp at hpos
  obtain ⟨x, hx, hx0⟩ := C.ne_bot_iff.mp hbot
  rcases (doublyEvenWord_iff_zero_or_ones_of_card_eq_four x hι).mp
    (hC x hx) with hz | ho
  · exact (hx0 hz).elim
  · simpa only [ho] using hx

/-- The nonzero length-four code is exactly the all-ones line. -/
theorem doublyEvenCode_eq_span_ones_of_card_eq_four_of_finrank_pos
    {ι : Type*} [Fintype ι] (C : Submodule (ZMod 2) (BinaryWord ι))
    (hC : DoublyEvenCode C) (hι : Fintype.card ι = 4)
    (hpos : 0 < Module.finrank (ZMod 2) C) :
    C = Submodule.span (ZMod 2) {ones ι} := by
  apply le_antisymm (doublyEvenCode_le_span_ones_of_card_eq_four C hC hι)
  apply Submodule.span_le.mpr
  intro x hx
  have hx1 : x = ones ι := Set.mem_singleton_iff.mp hx
  rw [hx1]
  exact ones_mem_of_doublyEvenCode_of_card_eq_four_of_finrank_pos C hC hι hpos

theorem doublyEvenCode_finrank_three
    (C : Submodule (ZMod 2) (BinaryWord (Fin 3))) (hC : DoublyEvenCode C) :
    Module.finrank (ZMod 2) C = 0 :=
  doublyEvenCode_finrank_eq_zero_of_card_lt_four C hC (by decide)

theorem doublyEvenCode_finrank_four
    (C : Submodule (ZMod 2) (BinaryWord (Fin 4))) (hC : DoublyEvenCode C) :
    Module.finrank (ZMod 2) C ≤ 1 :=
  doublyEvenCode_finrank_le_one_of_card_eq_four C hC (by decide)

end KltDP.Codes
