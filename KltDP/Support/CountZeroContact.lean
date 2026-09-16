import Mathlib.Tactic

/-!
# Support obligation U-COUNT-ZERO-CONTACT: an isolated contracted `(-1)`-curve makes no singular point

Manuscript `source/manuscript.tex` lines 1099–1110 (end of the proof of Theorem 4.5
`thm:one-component-replacement`): "Deleting `C` replaces its exceptional connected
component by `s_C` pieces. With no retained contact, the isolated contracted `P`
gives a smooth point, so the singular count changes by `s_C - 1`. Otherwise its
blowdown joins precisely the `a` contacted pieces, changing that count by
`s_C - a`."

The integer bookkeeping is recorded here in `ℤ` (never by truncated natural
subtraction): removing the component of `C` (`-1`), adding its `s_C` pieces
(`+ s_C`), and, when `a ≥ 1` pieces are contacted by `P`, joining them into one
block (`-(a - 1)`); when `a = 0` the contracted `P` is an isolated `(-1)`-curve,
whose image is a smooth point and contributes no block. Both cases are
`s_C - max a 1`. The consequences used in Theorem 8.1 (`U-CORE-WEIGHTS`) are also
recorded: a negative change forces `s_C < max a 1`, so with `a = 0` the deleted
curve was isolated (`s_C = 0`), with `a = 1` again `s_C = 0`, and with `a = 2`
`s_C ≤ 1`.

Not proved here: that the blown-down surface is the minimal resolution of a
normal target, that each surviving block has a singular image, and that an
isolated contracted `(-1)`-curve yields a smooth point (F10, F16, F27).
-/

namespace KltDP.Support

/-- Change in the number of exceptional blocks (hence singular points, once F16
applies): `s_C` pieces replace the deleted block, and the `a ≥ 1` contacted pieces
are joined by the blowdown of `P`; for `a = 0` nothing is joined and `P` itself
disappears into a smooth point. -/
def countChange (sC a : ℕ) : ℤ := (sC : ℤ) - max (a : ℤ) 1

/-- No retained contact: the change is `s_C - 1`. -/
theorem countChange_zero (sC : ℕ) : countChange sC 0 = (sC : ℤ) - 1 := by
  simp [countChange]

/-- At least one contact: the change is `s_C - a`. -/
theorem countChange_pos (sC a : ℕ) (ha : 1 ≤ a) : countChange sC a = (sC : ℤ) - a := by
  have : (1 : ℤ) ≤ a := by exact_mod_cast ha
  simp [countChange, max_eq_left this]

/-- The bookkeeping identity: old count `n`, minus the deleted block, plus `s_C`
pieces, minus the `a - 1` joins (none when `a = 0`). -/
theorem newCount_eq (n sC a : ℕ) :
    (n : ℤ) - 1 + sC - (if a = 0 then 0 else (a : ℤ) - 1) = (n : ℤ) + countChange sC a := by
  unfold countChange
  split_ifs with h
  · subst h
    simp only [Nat.cast_zero, sub_zero]
    rw [max_eq_right (by norm_num : (0 : ℤ) ≤ 1)]
    ring
  · have : (1 : ℤ) ≤ a := by
      have : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h
      exact_mod_cast this
    rw [max_eq_left this]; ring

/-- A negative change means `s_C < max a 1`. -/
theorem countChange_neg_iff (sC a : ℕ) : countChange sC a < 0 ↔ (sC : ℤ) < max (a : ℤ) 1 := by
  unfold countChange; constructor <;> intro h <;> linarith

/-- **Consequences for the shortest-curve argument** (`U-CORE-WEIGHTS`): a negative
change with `j = 0` or `j = 1` higher-weight contacts forces `s_C = 0` (the deleted
weight-two curve was an isolated block), and with `j = 2` it forces `s_C ≤ 1` (a leaf). -/
theorem sC_of_countChange_neg (sC j : ℕ) (hneg : countChange sC j < 0) (hj : j ≤ 2) :
    (j ≤ 1 → sC = 0) ∧ (j = 2 → sC ≤ 1) := by
  rw [countChange_neg_iff] at hneg
  constructor
  · intro hj1
    have : (j : ℤ) ≤ 1 := by exact_mod_cast hj1
    rw [max_eq_right this] at hneg
    omega
  · intro hj2
    subst hj2
    norm_num at hneg
    omega

/-- **U-COUNT-ZERO-CONTACT**, arithmetic clause. -/
theorem u_count_zero_contact :
    (∀ sC : ℕ, countChange sC 0 = (sC : ℤ) - 1) ∧
    (∀ sC a : ℕ, 1 ≤ a → countChange sC a = (sC : ℤ) - a) ∧
    (∀ sC a : ℕ, countChange sC a < 0 ↔ (sC : ℤ) < max (a : ℤ) 1) :=
  ⟨countChange_zero, countChange_pos, countChange_neg_iff⟩

end KltDP.Support
