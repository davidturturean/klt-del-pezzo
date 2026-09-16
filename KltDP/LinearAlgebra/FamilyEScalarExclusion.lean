import KltDP.Manuscript.S09.RootedTrees
import Mathlib.Tactic

/-!
# Beta-four component charge restrictions

The finite arithmetic is first proved for all eight rooted choices. The
source-facing theorems then derive the choices and their inverse values from
actual rooted trees with the actual combined edge allowance. No shape or
table membership is an assumption about those trees.

This implements the one-extra exclusion and the initial two-extra core
restriction in the beta-four paragraph of manuscript Lemma 9.2.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- The four endpoint-rooted paths, including the isolated root. -/
def isEndpointRootedChoice (choice : RootedBlockChoice) : Prop :=
  choice = .arms .point ∨ choice = .arms .endEdge ∨
    choice = .arms .endTwo ∨ choice = .arms .endThree

/-- Source upper bound for x+4y at the combined core edge count. Only
arguments at most three occur in the theorems below. -/
def betaFourCoreUpper : ℕ → ℚ
  | 0 => 0
  | 1 => 1 / 7
  | 2 => 22 / 105
  | _ => 3 / 13

/-- Source upper bound for the remaining extra component's Green entry,
indexed by the number of edges already allocated to the two cores. -/
def betaFourExtraUpper : ℕ → ℚ
  | 0 => 2 / 3
  | 1 => 1 / 2
  | 2 => 2 / 5
  | _ => 1 / 3

set_option maxHeartbeats 1200000 in
/-- The complete finite core calculation. A positive length forces both
root placements to be endpoints, supplies their edge-count formulas and
bounds x+4y by the source's four-entry table. -/
theorem betaFour_core_choice_bounds (left right : RootedBlockChoice)
    (hbudget : rootedBlockEdges left + rootedBlockEdges right ≤ 3)
    (hlength : (rootedBlockGreen left 3 - 1 / 3) +
      2 * (rootedBlockGreen right 4 - 1 / 4) < 1 / 6) :
    isEndpointRootedChoice left ∧ isEndpointRootedChoice right ∧
      rootedBlockGreen left 3 - 1 / 3 =
        (rootedBlockEdges left : ℚ) / (3 * (2 * rootedBlockEdges left + 3)) ∧
      rootedBlockGreen right 4 - 1 / 4 =
        (rootedBlockEdges right : ℚ) / (4 * (3 * rootedBlockEdges right + 4)) ∧
      (rootedBlockGreen left 3 - 1 / 3) +
        4 * (rootedBlockGreen right 4 - 1 / 4) ≤
          betaFourCoreUpper (rootedBlockEdges left + rootedBlockEdges right) := by
  rcases (exists_rootedBlockChoice (fun choice => left = choice)).mp ⟨left, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (exists_rootedBlockChoice (fun choice => right = choice)).mp ⟨right, rfl⟩ with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [isEndpointRootedChoice, rootedBlockEdges, rootedArmLengths,
      Fin.sum_univ_succ, rootedBlockGreen, rootedArmGreenNumerator,
      rootedArmDenominator, betaFourCoreUpper] at *

set_option maxHeartbeats 600000 in
/-- The remaining extra's actual eight-choice Green entry satisfies the
second row of the source table at every admissible remaining edge count. -/
theorem betaFour_extra_choice_bound (extra : RootedBlockChoice) (d : ℕ)
    (hbudget : d + rootedBlockEdges extra ≤ 3) :
    rootedBlockGreen extra 3 ≤ betaFourExtraUpper d := by
  have hd : d ≤ 3 := by omega
  interval_cases d <;>
    rcases (exists_rootedBlockChoice (fun choice => extra = choice)).mp ⟨extra, rfl⟩ with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
      rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator,
      betaFourExtraUpper] at *

/-- Every column of the source table has total at most two-thirds. -/
theorem betaFour_column_sum (d : ℕ) (hd : d ≤ 3) :
    betaFourCoreUpper d + betaFourExtraUpper d ≤ 2 / 3 := by
  interval_cases d <;> norm_num [betaFourCoreUpper, betaFourExtraUpper]

/-- Combining the two separately checked finite bounds excludes positive
v in the beta-four one-extra case. -/
theorem betaFour_one_extra_choice_nonpositive
    (left right extra : RootedBlockChoice)
    (hbudget : rootedBlockEdges left + rootedBlockEdges right + rootedBlockEdges extra ≤ 3)
    (hlength : (rootedBlockGreen left 3 - 1 / 3) +
      2 * (rootedBlockGreen right 4 - 1 / 4) < 1 / 6) :
    -2 / 3 + (rootedBlockGreen left 3 - 1 / 3) +
      4 * (rootedBlockGreen right 4 - 1 / 4) + rootedBlockGreen extra 3 ≤ 0 := by
  have hcore := (betaFour_core_choice_bounds left right (by omega) hlength).2.2.2.2
  have hextra := betaFour_extra_choice_bound extra
    (rootedBlockEdges left + rootedBlockEdges right) hbudget
  have hsum := betaFour_column_sum (rootedBlockEdges left + rootedBlockEdges right) (by omega)
  linarith only [hcore, hextra, hsum]

set_option maxHeartbeats 1200000 in
/-- The beta-four two-extra cap permits only an isolated weight-four core
and an isolated or one-leaf weight-three core, among all eight choices. -/
theorem betaFour_two_extra_core_choices (left right : RootedBlockChoice)
    (hcap : 2 * (rootedBlockGreen left 3 - 1 / 3) +
      6 * (rootedBlockGreen right 4 - 1 / 4) ≤ 1 / 6) :
    right = .arms .point ∧ (left = .arms .point ∨ left = .arms .endEdge) := by
  rcases (exists_rootedBlockChoice (fun choice => left = choice)).mp ⟨left, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (exists_rootedBlockChoice (fun choice => right = choice)).mp ⟨right, rfl⟩ with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator] at *

/-- Every listed weight-three Green value has the source's lower bound. -/
theorem rootedBlockGreen_three_lower (choice : RootedBlockChoice) :
    1 / 3 ≤ rootedBlockGreen choice 3 := by
  rcases (exists_rootedBlockChoice (fun c => choice = c)).mp ⟨choice, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]

section ActualTrees

variable {V W Z : Type*} [Fintype V] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq W] [DecidableEq Z]

/-- The one-extra exclusion for three actual component trees. Their actual
edge counts have a combined allowance of three. Both endpoint formulas and
the nonpositive square are conclusions about actual inverse entries. -/
theorem betaFour_one_extra_trees_nonpositive
    (G : SimpleGraph V) (H : SimpleGraph W) (J : SimpleGraph Z)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj]
    (rootG : V) (rootH : W) (rootJ : Z)
    (hG : G.IsTree) (hH : H.IsTree) (hJ : J.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card + J.edgeFinset.card ≤ 3)
    (hlength : (rootedTreeGreen G rootG 3 - 1 / 3) +
      2 * (rootedTreeGreen H rootH 4 - 1 / 4) < 1 / 6) :
    rootedTreeGreen G rootG 3 - 1 / 3 =
        (G.edgeFinset.card : ℚ) / (3 * (2 * G.edgeFinset.card + 3)) ∧
      rootedTreeGreen H rootH 4 - 1 / 4 =
        (H.edgeFinset.card : ℚ) / (4 * (3 * H.edgeFinset.card + 4)) ∧
      -2 / 3 + (rootedTreeGreen G rootG 3 - 1 / 3) +
        4 * (rootedTreeGreen H rootH 4 - 1 / 4) + rootedTreeGreen J rootJ 3 ≤ 0 := by
  obtain ⟨left, hleft, hgreenG⟩ := smallRootedTree_inverse_root G rootG hG (by omega)
    (b := 3) (le_refl 3)
  obtain ⟨right, hright, hgreenH⟩ := smallRootedTree_inverse_root H rootH hH (by omega)
    (b := 4) (by norm_num)
  obtain ⟨extra, hextra, hgreenJ⟩ := smallRootedTree_inverse_root J rootJ hJ (by omega)
    (b := 3) (le_refl 3)
  change rootedTreeGreen G rootG 3 = rootedBlockGreen left 3 at hgreenG
  change rootedTreeGreen H rootH 4 = rootedBlockGreen right 4 at hgreenH
  change rootedTreeGreen J rootJ 3 = rootedBlockGreen extra 3 at hgreenJ
  have hlength' : (rootedBlockGreen left 3 - 1 / 3) +
      2 * (rootedBlockGreen right 4 - 1 / 4) < 1 / 6 := by
    simpa only [hgreenG, hgreenH] using hlength
  have hbudget' : rootedBlockEdges left + rootedBlockEdges right + rootedBlockEdges extra ≤ 3 := by
    simpa only [hleft, hright, hextra] using hbudget
  obtain ⟨_, _, hformulaG, hformulaH, _⟩ :=
    betaFour_core_choice_bounds left right (by omega) hlength'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hgreenG, hleft] using hformulaG
  · simpa only [hgreenH, hright] using hformulaH
  · simpa only [hgreenG, hgreenH, hgreenJ] using
      betaFour_one_extra_choice_nonpositive left right extra hbudget' hlength'

/-- For actual small core trees, the two-extra cap forces the weight-four
tree's edge set to be empty and the weight-three tree to be isolated or
root-isomorphic to the actual two-vertex edge. Shape membership is derived
by the graph classification and exact inverse formulas. -/
theorem betaFour_two_extra_core_tree_restriction
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (rootG : V) (rootH : W)
    (hG : G.IsTree) (hH : H.IsTree)
    (hedgesG : G.edgeFinset.card ≤ 3) (hedgesH : H.edgeFinset.card ≤ 3)
    (hcap : 2 * (rootedTreeGreen G rootG 3 - 1 / 3) +
      6 * (rootedTreeGreen H rootH 4 - 1 / 4) ≤ 1 / 6) :
    H.edgeFinset = ∅ ∧
      (G.edgeFinset = ∅ ∨
        ∃ e : G ≃g rootedBlockGraph (.arms .endEdge),
          e rootG = rootedBlockRoot (.arms .endEdge)) := by
  obtain ⟨left, eG, hrootG⟩ := smallRootedTree_classification hG hedgesG rootG
  obtain ⟨right, eH, hrootH⟩ := smallRootedTree_classification hH hedgesH rootH
  have hgreenG : rootedTreeGreen G rootG 3 = rootedBlockGreen left 3 := by
    change (rootedGraphMatrix G rootG (3 : ℚ))⁻¹ rootG rootG = _
    rw [rootedGraphMatrix_inverse_root_eq eG rootG (rootedBlockRoot left) hrootG (3 : ℚ),
      ← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root left (le_refl 3)]
  have hgreenH : rootedTreeGreen H rootH 4 = rootedBlockGreen right 4 := by
    change (rootedGraphMatrix H rootH (4 : ℚ))⁻¹ rootH rootH = _
    rw [rootedGraphMatrix_inverse_root_eq eH rootH (rootedBlockRoot right) hrootH (4 : ℚ),
      ← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root right (by norm_num)]
  rw [hgreenG, hgreenH] at hcap
  obtain ⟨hright, hleft⟩ := betaFour_two_extra_core_choices left right hcap
  subst right
  have hHcount : H.edgeFinset.card = 0 := by
    calc
      _ = rootedBlockEdges (.arms .point) := (rootedBlockEdges_eq_of_iso eH).symm
      _ = 0 := by norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ]
  refine ⟨Finset.card_eq_zero.mp hHcount, ?_⟩
  rcases hleft with hleft | hleft
  · subst left
    left
    have hGcount : G.edgeFinset.card = 0 := by
      calc
        _ = rootedBlockEdges (.arms .point) := (rootedBlockEdges_eq_of_iso eG).symm
        _ = 0 := by norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ]
    exact Finset.card_eq_zero.mp hGcount
  · subst left
    exact Or.inr ⟨eG, hrootG⟩

/-- The lower bound is about the actual inverse of any small rooted tree,
with shape selection supplied by the graph classification. -/
theorem rootedTreeGreen_three_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    (hG : G.IsTree) (hedges : G.edgeFinset.card ≤ 3) :
    1 / 3 ≤ rootedTreeGreen G root 3 := by
  obtain ⟨choice, _, hgreen⟩ := smallRootedTree_inverse_root G root hG hedges
    (b := 3) (le_refl 3)
  change rootedTreeGreen G root 3 = rootedBlockGreen choice 3 at hgreen
  rw [hgreen]
  exact rootedBlockGreen_three_lower choice

/-- The source's full two-extra cap implies the core restriction for four
actual rooted component trees. The lower bound on tau is proved from the
two actual extra inverses and is not a separate hypothesis. -/
theorem betaFour_two_extra_trees_core_restriction
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (G : SimpleGraph V) (H : SimpleGraph W) (J : SimpleGraph Z) (K : SimpleGraph Q)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj]
    (rootG : V) (rootH : W) (rootJ : Z) (rootK : Q)
    (hG : G.IsTree) (hH : H.IsTree) (hJ : J.IsTree) (hK : K.IsTree)
    (hbudget : G.edgeFinset.card + H.edgeFinset.card +
      J.edgeFinset.card + K.edgeFinset.card ≤ 3)
    (hcap : rootedTreeGreen J rootJ 3 + rootedTreeGreen K rootK 3 +
      2 * (rootedTreeGreen G rootG 3 - 1 / 3) +
      6 * (rootedTreeGreen H rootH 4 - 1 / 4) ≤ 5 / 6) :
    H.edgeFinset = ∅ ∧
      (G.edgeFinset = ∅ ∨
        ∃ e : G ≃g rootedBlockGraph (.arms .endEdge),
          e rootG = rootedBlockRoot (.arms .endEdge)) := by
  have hJlow := rootedTreeGreen_three_lower_bound J rootJ hJ (by omega)
  have hKlow := rootedTreeGreen_three_lower_bound K rootK hK (by omega)
  apply betaFour_two_extra_core_tree_restriction G H rootG rootH hG hH
    (by omega) (by omega)
  linarith only [hcap, hJlow, hKlow]

end ActualTrees

end KltDP.LinearAlgebra
