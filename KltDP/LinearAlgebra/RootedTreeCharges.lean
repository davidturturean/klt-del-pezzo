import KltDP.LinearAlgebra.RootedTreeShapes
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic

/-!
# Exact charge sums for the eight specified rooted matrices

This file evaluates the two-block charge sets in manuscript `lem:rooted-trees`.
The choices are the seven actual arm matrices and the actual leaf-rooted star,
all with root weight three. Each rational charge is identified with the root
entry of that matrix's inverse before the finite sets are calculated.

The finite arithmetic expands every choice and proves rational identities
with `norm_num`, carrying a proof of each set calculation. No theorem here asserts that an arbitrary admissible
weighted graph belongs to this eight-element family. That graph classification
is a separate obligation.
-/

namespace KltDP.LinearAlgebra

open Matrix

instance rootedArmShapeFintype : Fintype RootedArmShape :=
  ⟨{.point, .endEdge, .endTwo, .middleTwo, .endThree, .innerThree, .centerStar},
    by intro shape; cases shape <;> simp⟩

/-- The eight matrix constructions whose charges occur in the source table. -/
inductive RootedBlockChoice where
  | arms (shape : RootedArmShape)
  | leafStar
  deriving DecidableEq, Fintype

/-- Vertices of the chosen actual matrix. -/
def RootedBlockVertex : RootedBlockChoice → Type
  | .arms shape => Unit ⊕ ArmIndex (rootedArmLengths shape)
  | .leafStar => Unit ⊕ Fin 3

instance rootedBlockVertexFintype (choice : RootedBlockChoice) :
    Fintype (RootedBlockVertex choice) := by
  cases choice <;> dsimp [RootedBlockVertex] <;> infer_instance

instance rootedBlockVertexDecidableEq (choice : RootedBlockChoice) :
    DecidableEq (RootedBlockVertex choice) := by
  cases choice <;> dsimp [RootedBlockVertex] <;> infer_instance

/-- The distinguished root vertex. -/
def rootedBlockRoot : (choice : RootedBlockChoice) → RootedBlockVertex choice
  | .arms _ => Sum.inl ()
  | .leafStar => Sum.inl ()

/-- The chosen rational intersection matrix, with root weight three. -/
def rootedBlockMatrix : (choice : RootedBlockChoice) →
    Matrix (RootedBlockVertex choice) (RootedBlockVertex choice) ℚ
  | .arms shape => rootedArmMatrix shape 3
  | .leafStar => leafRootedStarMatrix 3

/-- Number of edges in the specified construction: each path arm of length
`r` supplies `r` edges, and the separate leaf-rooted star supplies three. -/
def rootedBlockEdges : RootedBlockChoice → ℕ
  | .arms shape => ∑ a, rootedArmLengths shape a
  | .leafStar => 3

/-- The count uses the actual vertex type; zero-length arms add no vertices. -/
theorem rootedBlock_vertex_count (choice : RootedBlockChoice) :
    Fintype.card (RootedBlockVertex choice) = rootedBlockEdges choice + 1 := by
  cases choice <;>
    simp [RootedBlockVertex, rootedBlockEdges, ArmIndex, Fintype.card_sigma, Nat.add_comm]

/-- The computable rational expression for the root inverse entry. -/
def rootedBlockCharge : RootedBlockChoice → ℚ
  | .arms shape =>
    (rootedArmGreenNumerator shape : ℚ) / rootedArmDenominator shape (3 : ℚ)
  | .leafStar => 1 / 2

/-- The same charge defined directly from the actual matrix inverse. -/
noncomputable def rootedBlockActualCharge (choice : RootedBlockChoice) : ℚ :=
  (rootedBlockMatrix choice)⁻¹ (rootedBlockRoot choice) (rootedBlockRoot choice)

/-- The arithmetic table is attached to actual matrices by the proved inverse
formulas, without assuming any of their inverse entries. -/
theorem rootedBlockActualCharge_eq (choice : RootedBlockChoice) :
    rootedBlockActualCharge choice = rootedBlockCharge choice := by
  cases choice with
  | arms shape =>
    change (rootedArmMatrix shape (3 : ℚ))⁻¹ (Sum.inl ()) (Sum.inl ()) = _
    exact rootedArmMatrix_inverse_root_of_three_le shape (le_refl 3)
  | leafStar =>
    change (leafRootedStarMatrix (3 : ℚ))⁻¹ (Sum.inl ()) (Sum.inl ()) = 1 / 2
    rw [leafRootedStarMatrix_inverse_root (3 : ℚ) (by norm_num)]
    norm_num

/-- Charges of all pairs from the specified family with a bounded total
number of construction edges. Ordering the pair does not affect this set. -/
def rootedPairCharges (budget : ℕ) : Finset ℚ :=
  (((Finset.univ : Finset RootedBlockChoice) ×ˢ Finset.univ).filter
    (fun pair => rootedBlockEdges pair.1 + rootedBlockEdges pair.2 ≤ budget)).image
      (fun pair => rootedBlockCharge pair.1 + rootedBlockCharge pair.2)

/-- Every member of the finite charge set, and only such a member, is a sum
of two actual inverse entries from the specified matrices at the edge budget. -/
theorem mem_rootedPairCharges_iff (budget : ℕ) (charge : ℚ) :
    charge ∈ rootedPairCharges budget ↔
      ∃ choiceA choiceB : RootedBlockChoice,
        rootedBlockEdges choiceA + rootedBlockEdges choiceB ≤ budget ∧
          rootedBlockActualCharge choiceA + rootedBlockActualCharge choiceB = charge := by
  constructor
  · intro h
    obtain ⟨⟨choiceA, choiceB⟩, hpair, hcharge⟩ := Finset.mem_image.mp h
    refine ⟨choiceA, choiceB, (Finset.mem_filter.mp hpair).2, ?_⟩
    simpa only [rootedBlockActualCharge_eq] using hcharge
  · rintro ⟨choiceA, choiceB, hbudget, hcharge⟩
    apply Finset.mem_image.mpr
    refine ⟨(choiceA, choiceB), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hbudget⟩
    · simpa only [rootedBlockActualCharge_eq] using hcharge

theorem exists_rootedBlockChoice (P : RootedBlockChoice → Prop) :
    (∃ choice, P choice) ↔
      P (.arms .point) ∨ P (.arms .endEdge) ∨ P (.arms .endTwo) ∨
      P (.arms .middleTwo) ∨ P (.arms .endThree) ∨ P (.arms .innerThree) ∨
      P (.arms .centerStar) ∨ P .leafStar := by
  constructor
  · rintro ⟨choice, h⟩
    cases choice with
    | arms shape => cases shape <;> simp_all
    | leafStar => simp_all
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨.arms .point, h⟩
    · exact ⟨.arms .endEdge, h⟩
    · exact ⟨.arms .endTwo, h⟩
    · exact ⟨.arms .middleTwo, h⟩
    · exact ⟨.arms .endThree, h⟩
    · exact ⟨.arms .innerThree, h⟩
    · exact ⟨.arms .centerStar, h⟩
    · exact ⟨.leafStar, h⟩

/-- The source's set `S₁`: at most one edge shared by two weight-three blocks. -/
theorem rootedPairCharges_one :
    rootedPairCharges 1 = {2 / 3, 11 / 15} := by
  ext charge
  rw [mem_rootedPairCharges_iff]
  simp only [exists_rootedBlockChoice, rootedBlockActualCharge_eq]
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockCharge, rootedArmGreenNumerator, rootedArmDenominator]; tauto

/-- The source's set `S₂`: at most two edges shared by the two blocks. -/
theorem rootedPairCharges_two :
    rootedPairCharges 2 = {2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5} := by
  ext charge
  rw [mem_rootedPairCharges_iff]
  simp only [exists_rootedBlockChoice, rootedBlockActualCharge_eq]
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockCharge, rootedArmGreenNumerator, rootedArmDenominator]; tauto

set_option maxHeartbeats 2000000 in
/-- All charge sums with at most three edges, including values outside the
interval used in the subsequent residue classification. -/
theorem rootedPairCharges_three :
    rootedPairCharges 3 =
      {2 / 3, 11 / 15, 16 / 21, 5 / 6, 4 / 5, 7 / 9, 29 / 33, 1, 29 / 35, 9 / 10} := by
  ext charge
  rw [mem_rootedPairCharges_iff]
  simp only [exists_rootedBlockChoice, rootedBlockActualCharge_eq]
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockCharge, rootedArmGreenNumerator, rootedArmDenominator]; tauto

/-- Exactly two values lie in the source's half-open interval. -/
theorem rootedPairCharges_three_interval :
    (rootedPairCharges 3).filter (fun charge => 13 / 15 < charge ∧ charge ≤ 14 / 15) =
      {29 / 33, 9 / 10} := by
  rw [rootedPairCharges_three]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

end KltDP.LinearAlgebra
