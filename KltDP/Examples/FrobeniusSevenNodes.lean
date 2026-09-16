import KltDP.Examples.FrobeniusEvenSets
import Mathlib.Data.Fintype.Powerset

/-!
# The seven-node integral parity calculation

At `p = 2, n = 3`, the graph vector must be included among the selectable
node vectors. Its inclusion changes the parity equations. This module
proves the full criterion on the actual integer-coordinate vectors and
checks every binary selection, including the graph coordinate.

There are exactly 128 ambient selections. The finite checks below take
place only after integral two-divisibility has been proved equivalent to
coordinate parity. Ordinary kernel-checked `decide` proves the complete
finite claims; no native evaluator or external certificate is used.

The eight divisible selections and their weights are arithmetic results.
They are not identified with an actual surface's Picard code here, and
their cardinality alone is not asserted to prove a binary-space dimension.
-/

namespace KltDP.Examples.FrobeniusSevenNodes

open KltDP.Examples.FrobeniusPicard
open KltDP.Examples.FrobeniusEvenSets
open scoped BigOperators

section IntegralCoordinates

variable {ι : Type*}

/-- Coordinatewise integer division; it is a half-vector when every coordinate is even. -/
def halfCoordinates (v : BlowupLattice ι) : BlowupLattice ι :=
  (v.1 / 2, v.2.1 / 2, fun i => v.2.2 i / 2)

/-- The explicit half-vector works for every even integral coordinate, including negative ones. -/
theorem two_smul_halfCoordinates (v : BlowupLattice ι)
    (ha : Even v.1) (hb : Even v.2.1) (he : ∀ i, Even (v.2.2 i)) :
    (2 : ℤ) • halfCoordinates v = v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simpa [halfCoordinates, smul_eq_mul] using Int.two_mul_ediv_two_of_even ha
  · simpa [halfCoordinates, smul_eq_mul] using Int.two_mul_ediv_two_of_even hb
  · funext i
    simpa [halfCoordinates, smul_eq_mul] using Int.two_mul_ediv_two_of_even (he i)

/-- Integral divisibility is equivalent to parity of every coordinate.

The exceptional index type need not be finite. This is a statement about
the actual integer module, with an explicit witness in the reverse direction.
-/
theorem two_divisible_iff_even_coordinates (v : BlowupLattice ι) :
    (∃ M : BlowupLattice ι, (2 : ℤ) • M = v) ↔
      Even v.1 ∧ Even v.2.1 ∧ ∀ i, Even (v.2.2 i) := by
  constructor
  · rintro ⟨M, rfl⟩
    refine ⟨⟨M.1, ?_⟩, ⟨M.2.1, ?_⟩, fun i => ⟨M.2.2 i, ?_⟩⟩ <;>
      simp [two_smul]
  · rintro ⟨ha, hb, he⟩
    exact ⟨halfCoordinates v, two_smul_halfCoordinates v ha hb he⟩

end IntegralCoordinates

section FiniteSelections

-- The 128-element enumeration builds nested finite `Decidable` terms.
-- These limits apply only to this finite section, not to the coordinate theorem.
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- A graph-selection bit and two independent subsets of the three branch indices. -/
abbrev Selection := Bool × Finset (Fin 3) × Finset (Fin 3)

def selectionVector (s : Selection) : PicardVector 2 3 :=
  (if s.1 then graphVector 2 3 else 0) + selectedNodes 3 s.2.1 s.2.2

/-- Number of selected node labels, counting the graph separately. -/
def selectionWeight (s : Selection) : ℕ :=
  (if s.1 then 1 else 0) + s.2.1.card + s.2.2.card

/-- The two source parity cases, kept separate from integral divisibility. -/
def parityConditions (s : Selection) : Prop :=
  if s.1 then s.2.2 = Finset.univ \ s.2.1 ∧ Odd s.2.1.card
  else s.2.1 = s.2.2 ∧ Even s.2.1.card

instance (s : Selection) : Decidable (parityConditions s) := by
  unfold parityConditions
  infer_instance

/-- All graph/fiber/chain selection data are allowed before imposing parity. -/
theorem selection_card : Fintype.card Selection = 128 := by decide

/-- Complete parity classification of the 128 binary selections.

With the graph absent the two subsets coincide and have even cardinality.
With the graph present they are complementary and the fiber subset has odd cardinality.
-/
theorem selection_two_divisible_iff (s : Selection) :
    (∃ M : PicardVector 2 3, (2 : ℤ) • M = selectionVector s) ↔ parityConditions s := by
  rw [two_divisible_iff_even_coordinates]
  revert s
  decide

/-- An explicit integral half-vector, rather than an existence assertion alone. -/
theorem selection_explicit_half (s : Selection) (hs : parityConditions s) :
    (2 : ℤ) • halfCoordinates (selectionVector s) = selectionVector s := by
  have hc := (two_divisible_iff_even_coordinates (selectionVector s)).mp
    ((selection_two_divisible_iff s).mpr hs)
  exact two_smul_halfCoordinates _ hc.1 hc.2.1 hc.2.2

def emptySelection : Selection := (false, ∅, ∅)

/-- Only the empty selection represents the zero integral vector. -/
theorem selectionVector_eq_zero_iff (s : Selection) :
    selectionVector s = 0 ↔ s = emptySelection := by
  revert s
  decide

theorem selectionWeight_eq_zero_iff (s : Selection) :
    selectionWeight s = 0 ↔ s = emptySelection := by
  revert s
  decide

/-- Every divisible selection is either empty or contains exactly four nodes. -/
theorem selectionWeight_eq_zero_or_four (s : Selection) (hs : parityConditions s) :
    selectionWeight s = 0 ∨ selectionWeight s = 4 := by
  revert s
  decide

/-- Every nonzero divisible integral selection has exactly four selected node labels. -/
theorem nonzero_divisible_selection_weight (s : Selection)
    (hs : ∃ M : PicardVector 2 3, (2 : ℤ) • M = selectionVector s)
    (hne : selectionVector s ≠ 0) : selectionWeight s = 4 := by
  have hp := (selection_two_divisible_iff s).mp hs
  rcases selectionWeight_eq_zero_or_four s hp with hz | hfour
  · have hempty := (selectionWeight_eq_zero_iff s).mp hz
    exact (hne ((selectionVector_eq_zero_iff s).mpr hempty)).elim
  · exact hfour

/-- A computed finite set whose membership is proved equivalent to actual integral divisibility. -/
def divisibleSelections : Finset Selection := Finset.univ.filter parityConditions

theorem mem_divisibleSelections_iff (s : Selection) :
    s ∈ divisibleSelections ↔
      ∃ M : PicardVector 2 3, (2 : ℤ) • M = selectionVector s := by
  simp only [divisibleSelections, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (selection_two_divisible_iff s).symm

theorem divisibleSelections_card : divisibleSelections.card = 8 := by decide

theorem nonempty_divisibleSelections_card :
    (divisibleSelections.erase emptySelection).card = 7 := by decide

end FiniteSelections

end KltDP.Examples.FrobeniusSevenNodes
