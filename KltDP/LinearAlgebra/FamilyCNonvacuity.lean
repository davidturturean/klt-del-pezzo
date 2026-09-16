import KltDP.LinearAlgebra.FamilyCGreenEnergy

/-!
# A concrete algebraic witness for family C

The vertex type is Fin 10. The marked vertices are C=0, B=1, D=3.
The edges are 1--2 and 3--4; the isolated extra weight-three vertex is 5.
All other vertices have weight two. Explicit full-vector solutions certify
the actual canonical source and marked-source equations.

This is an actual positive-definite weighted graph witness for the algebraic
classification branch. It does not construct a surface or a Picard-lattice
embedding and makes no geometric realization claim.
-/

namespace KltDP.LinearAlgebra.FamilyCNonvacuity

open Matrix SimpleGraph
open scoped BigOperators

def graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun i j => (i = 1 ∧ j = 2) ∨ (i = 3 ∧ j = 4))

instance graphDecidable : DecidableRel graph.Adj := by
  intro i j
  change Decidable (i ≠ j ∧
    (((i = 1 ∧ j = 2) ∨ (i = 3 ∧ j = 4)) ∨
      ((j = 1 ∧ i = 2) ∨ (j = 3 ∧ i = 4))))
  infer_instance

def heavyVertices : Finset (Fin 10) := {1, 3, 5}

def weight (i : Fin 10) : ℚ := if i ∈ heavyVertices then 3 else 2

def gram : Matrix (Fin 10) (Fin 10) ℚ := graphWeightMatrix graph weight

def marked : Fin 10 → ℚ := threeMarkedSource 0 1 3

def canonicalSource (i : Fin 10) : ℚ := weight i - 2

def canonicalCoeff (i : Fin 10) : ℚ :=
  if i = 1 ∨ i = 3 then 2 / 5 else
    if i = 2 ∨ i = 4 then 1 / 5 else if i = 5 then 1 / 3 else 0

def green (i : Fin 10) : ℚ :=
  if i = 0 then 1 / 2 else if i = 1 ∨ i = 3 then 2 / 5 else
    if i = 2 ∨ i = 4 then 1 / 5 else 0

theorem weight_values :
    weight 0 = 2 ∧ weight 1 = 3 ∧ weight 2 = 2 ∧
      weight 3 = 3 ∧ weight 4 = 2 ∧ weight 5 = 3 := by decide

theorem weight_other (i : Fin 10) (hiB : i ≠ 1) (hiD : i ≠ 3)
    (hiT : i ≠ 5) : weight i = 2 := by
  simp [weight, heavyVertices, hiB, hiD, hiT]

theorem first_adj : graph.Adj 1 2 := by simp [graph]

theorem second_adj : graph.Adj 3 4 := by simp [graph]

/-- A symbolic edge description, with the loop condition discharged once. -/
theorem graph_adj_iff (i j : Fin 10) : graph.Adj i j ↔
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by
  change (i ≠ j ∧
    (((i = 1 ∧ j = 2) ∨ (i = 3 ∧ j = 4)) ∨
      ((j = 1 ∧ i = 2) ∨ (j = 3 ∧ i = 4)))) ↔ _
  constructor
  · tauto
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    exact ⟨hne, by tauto⟩

theorem graph_edgeFinset : graph.edgeFinset = {s((1 : Fin 10), 2), s((3 : Fin 10), 4)} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro i j
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graph_adj_iff,
    Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  tauto

theorem edge_card : graph.edgeFinset.card = 2 := by
  rw [graph_edgeFinset]
  decide

/-- The remaining elementary graph premises of the source row hold for
the actual graph and weight function. -/
theorem local_graph_bounds :
    graph.degree 0 = 0 ∧ (∀ i, graph.degree i ≤ 1) ∧
      (∀ i, weight i = 2 ∨ weight i = 3) ∧ heavyVertices.card = 3 ∧
      ¬ graph.Adj 0 1 ∧ ¬ graph.Adj 0 3 ∧ ¬ graph.Adj 1 3 := by
  decide

theorem graph_isAcyclic : graph.IsAcyclic := by
  intro v walk hcycle
  have hlow := hcycle.three_le_length
  have hupp := hcycle.isTrail.length_le_card_edgeFinset
  rw [edge_card] at hupp
  omega

theorem first_neighbors : graph.neighborFinset 1 = {2} ∧ graph.neighborFinset 2 = {1} := by
  constructor <;> ext i <;>
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

theorem second_neighbors : graph.neighborFinset 3 = {4} ∧ graph.neighborFinset 4 = {3} := by
  constructor <;> ext i <;>
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

theorem zero_isolated : ∀ j, ¬ graph.Adj 0 j := by
  intro j
  simp only [graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  norm_num

theorem five_isolated : ∀ j, ¬ graph.Adj 5 j := by
  intro j
  simp only [graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  norm_num

private theorem reachable_iff_eq_of_isolated (root : Fin 10)
    (hisolated : ∀ j, ¬ graph.Adj root j) (v : Fin 10) :
    graph.Reachable root v ↔ v = root := by
  constructor
  · rintro ⟨walk⟩
    cases walk with
    | nil => rfl
    | cons hadj rest => exact (hisolated _ hadj).elim
  · intro h
    subst v
    exact SimpleGraph.Reachable.refl root

theorem component_zero (v : Fin 10) : graph.Reachable 0 v ↔ v = 0 :=
  reachable_iff_eq_of_isolated 0 zero_isolated v

theorem component_five (v : Fin 10) : graph.Reachable 5 v ↔ v = 5 :=
  reachable_iff_eq_of_isolated 5 five_isolated v

theorem component_one (v : Fin 10) : graph.Reachable 1 v ↔ v = 1 ∨ v = 2 :=
  reachable_iff_of_mutual_singleton_neighbors graph 1 2 first_adj
    first_neighbors.1 first_neighbors.2 v

theorem component_three (v : Fin 10) : graph.Reachable 3 v ↔ v = 3 ∨ v = 4 :=
  reachable_iff_of_mutual_singleton_neighbors graph 3 4 second_adj
    second_neighbors.1 second_neighbors.2 v

theorem components_separate : ∀ i j : Fin 4, i ≠ j →
    ¬ graph.Reachable (![(0 : Fin 10), 1, 3, 5] i) (![(0 : Fin 10), 1, 3, 5] j) := by
  have h01 : ¬ graph.Reachable 0 1 := by rw [component_zero]; decide
  have h03 : ¬ graph.Reachable 0 3 := by rw [component_zero]; decide
  have h05 : ¬ graph.Reachable 0 5 := by rw [component_zero]; decide
  have h13 : ¬ graph.Reachable 1 3 := by rw [component_one]; decide
  have h15 : ¬ graph.Reachable 1 5 := by rw [component_one]; decide
  have h35 : ¬ graph.Reachable 3 5 := by rw [component_three]; decide
  have h10 : ¬ graph.Reachable 1 0 := fun h => h01 h.symm
  have h30 : ¬ graph.Reachable 3 0 := fun h => h03 h.symm
  have h50 : ¬ graph.Reachable 5 0 := fun h => h05 h.symm
  have h31 : ¬ graph.Reachable 3 1 := fun h => h13 h.symm
  have h51 : ¬ graph.Reachable 5 1 := fun h => h15 h.symm
  have h53 : ¬ graph.Reachable 5 3 := fun h => h35 h.symm
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact h01
    | exact h03
    | exact h05
    | exact h10
    | exact h13
    | exact h15
    | exact h30
    | exact h31
    | exact h35
    | exact h50
    | exact h51
    | exact h53

theorem canonical_component (v : Fin 10) (hv : graph.Reachable 0 v) : weight v = 2 := by
  have heq := (component_zero v).mp hv
  subst v
  decide

theorem first_single_source (v : Fin 10) (hv : graph.Reachable 1 v)
    (hne : v ≠ 1) : weight v = 2 := by
  rcases (component_one v).mp hv with rfl | rfl
  · exact (hne rfl).elim
  · decide

theorem second_single_source (v : Fin 10) (hv : graph.Reachable 3 v)
    (hne : v ≠ 3) : weight v = 2 := by
  rcases (component_three v).mp hv with rfl | rfl
  · exact (hne rfl).elim
  · decide

theorem extra_single_source (v : Fin 10) (hv : graph.Reachable 5 v)
    (hne : v ≠ 5) : weight v = 2 := by
  exact (hne ((component_five v).mp hv)).elim

/-- The ten-by-ten determinant is obtained from the existing actual graph
block theorem rather than evaluated as a determinant expression. -/
private theorem det_eq_of_matrix_eq {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℚ) (hAB : A = B) (d : ℚ) (hB : B.det = d) : A.det = d :=
  (congrArg Matrix.det hAB).trans hB

/-- Instantiate the graph determinant theorem before specializing the
vertex type or matrix. The equality premise identifies the actual matrix
without comparing two concrete determinant expressions. -/
private theorem familyC_det_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℚ)
    (A : Matrix V V ℚ) (hA : A = graphWeightMatrix G w)
    (B L D M T : V) (hcard : Fintype.card V = 10)
    (hB : w B = 3) (hL : w L = 2) (hD : w D = 3)
    (hM : w M = 2) (hT : w T = 3)
    (hBD : B ≠ D) (hLM : L ≠ M) (hTB : T ≠ B) (hTD : T ≠ D)
    (hBL : G.Adj B L) (hDM : G.Adj D M)
    (hedges : G.edgeFinset = {s(B, L), s(D, M)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → w i = 2) :
    A.det = 2400 := by
  have hd := familyC_exceptional_det (𝕜 := ℚ) G w B L D M T hcard
    hB hL hD hM hT hBD hLM hTB hTD hBL hDM hedges hother
  exact det_eq_of_matrix_eq A (graphWeightMatrix G w) hA 2400 hd

theorem exceptional_det : gram.det = 2400 := by
  exact familyC_det_of_matrix_eq graph weight gram rfl 1 2 3 4 5 (by decide)
    weight_values.2.1 weight_values.2.2.1 weight_values.2.2.2.1
    weight_values.2.2.2.2.1 weight_values.2.2.2.2.2
    (by decide) (by decide) (by decide) (by decide)
    first_adj second_adj graph_edgeFinset weight_other

theorem gram_isUnit : IsUnit gram := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [exceptional_det]
  norm_num

set_option maxHeartbeats 2000000 in
theorem canonical_row : gram *ᵥ canonicalCoeff = canonicalSource := by
  ext i
  fin_cases i <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.sum_univ_zero, canonicalCoeff, canonicalSource,
      weight, heavyVertices, Finset.mem_insert, Finset.mem_singleton, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_succ, Fin.val_mk] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem green_row : gram *ᵥ green = marked := by
  ext i
  fin_cases i <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.sum_univ_zero, green, marked, threeMarkedSource,
      Pi.add_apply, Pi.single_apply, weight, heavyVertices, Finset.mem_insert,
      Finset.mem_singleton, graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
      Fin.val_succ, Fin.val_mk] <;> norm_num

theorem inverse_canonical : gram⁻¹ *ᵥ canonicalSource = canonicalCoeff := by
  letI : Invertible gram := gram_isUnit.invertible
  exact Matrix.inv_mulVec_eq_vec canonical_row.symm

theorem inverse_green : gram⁻¹ *ᵥ marked = green := by
  letI : Invertible gram := gram_isUnit.invertible
  exact Matrix.inv_mulVec_eq_vec green_row.symm

theorem canonical_bounds : ∀ i, 0 ≤ (gram⁻¹ *ᵥ canonicalSource) i ∧
    (gram⁻¹ *ᵥ canonicalSource) i < 1 := by
  rw [inverse_canonical]
  intro i
  dsimp only [canonicalCoeff]
  split_ifs <;> norm_num

theorem scalar_values :
    1 - dotProduct marked (gram⁻¹ *ᵥ canonicalSource) = 1 / 5 ∧
      -1 + dotProduct canonicalSource (gram⁻¹ *ᵥ canonicalSource) = 2 / 15 ∧
      dotProduct marked (gram⁻¹ *ᵥ marked) = 13 / 10 := by
  rw [inverse_canonical, inverse_green]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, marked,
    threeMarkedSource, Pi.add_apply, Pi.single_apply, canonicalCoeff,
    canonicalSource, green, weight, heavyVertices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_succ, Fin.val_mk] <;> norm_num

theorem positive_volume_budget :
    0 < -1 + dotProduct canonicalSource (gram⁻¹ *ᵥ canonicalSource) ∧
      -1 + dotProduct canonicalSource (gram⁻¹ *ᵥ canonicalSource) ≤
        1 - dotProduct marked (gram⁻¹ *ᵥ canonicalSource) := by
  rw [scalar_values.1, scalar_values.2.1]
  norm_num

theorem projection_identity :
    (-1 + dotProduct canonicalSource (gram⁻¹ *ᵥ canonicalSource)) *
        (dotProduct marked (gram⁻¹ *ᵥ marked) - 1) =
      (1 - dotProduct marked (gram⁻¹ *ᵥ canonicalSource)) ^ 2 := by
  rw [scalar_values.1, scalar_values.2.1, scalar_values.2.2]
  norm_num

private theorem ten_vertex_bordered_det_of_values
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℚ) (p : V → ℚ) (hcard : Fintype.card V = 10)
    (hA : IsUnit A) (hd : A.det = 2400)
    (hg : dotProduct p (A⁻¹ *ᵥ p) = 13 / 10) :
    (borderedGram A p (-1)).det = 720 := by
  apply (det_minusOne_borderedGram hA p).trans
  rw [hcard, hd, hg]
  norm_num

theorem bordered_det : (borderedGram gram marked (-1)).det = 720 := by
  have hunit := gram_isUnit
  have hdet := exceptional_det
  have hg := scalar_values.2.2
  generalize hmatrix : gram = A at hunit hdet hg ⊢
  generalize hvector : marked = p at hg ⊢
  exact ten_vertex_bordered_det_of_values A p (by decide) hunit hdet hg

private theorem gram_isHermitian : gram.IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  by_cases hij : i = j
  · subst j
    simp [gram, graphWeightMatrix_diagonal]
  · have hadj : graph.Adj j i ↔ graph.Adj i j := ⟨fun h => h.symm, fun h => h.symm⟩
    simp only [gram, graphWeightMatrix_apply, if_neg hij, if_neg (Ne.symm hij),
      star_trivial, hadj]

private theorem finTen_sum (f : Fin 10 → ℚ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 +
      (f 5 + (f 6 + (f 7 + (f 8 + f 9)))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl

set_option maxHeartbeats 2000000 in
private theorem gram_quadratic_form (x : Fin 10 → ℚ) :
    dotProduct x (gram *ᵥ x) =
      (∑ i : Fin 10, (x i)^2) + (x 1 - x 2)^2 + (x 3 - x 4)^2 +
        (x 0)^2 + (x 1)^2 + (x 3)^2 + 2 * (x 5)^2 +
        (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2 := by
  simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
    finTen_sum, weight, heavyVertices,
    Finset.mem_insert, Finset.mem_singleton, graph_adj_iff,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_succ, Fin.val_mk]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
/-- A sum-of-squares proof of positive definiteness for the actual matrix. -/
theorem gram_posDef : gram.PosDef := by
  refine ⟨gram_isHermitian, ?_⟩
  intro x hx
  have hpositive : 0 < ∑ i : Fin 10, (x i)^2 := by
    apply Finset.sum_pos'
    · intro i _
      exact sq_nonneg (x i)
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      refine ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero ?_⟩
      exact hi
  rw [show star x = x from star_trivial x, gram_quadratic_form]
  nlinarith [sq_nonneg (x 1 - x 2), sq_nonneg (x 3 - x 4),
    sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 3), sq_nonneg (x 5),
    sq_nonneg (x 6), sq_nonneg (x 7), sq_nonneg (x 8), sq_nonneg (x 9)]

/-- The source classifier's actual hypotheses hold simultaneously for the
constructed graph. Its displayed family-C conclusion is witnessed by the
two actual leaves and the proved graph, source and determinant identities.
No geometric realization is asserted. -/
theorem source_classification_witness :
    ∃ L M, weight L = 2 ∧ weight M = 2 ∧
      (∀ v, ¬ graph.Adj 0 v) ∧ (∀ v, ¬ graph.Adj 5 v) ∧
      graph.Adj 1 L ∧ graph.Adj 3 M ∧
      graph.neighborFinset 1 = {L} ∧ graph.neighborFinset L = {1} ∧
      graph.neighborFinset 3 = {M} ∧ graph.neighborFinset M = {3} ∧
      graph.edgeFinset = {s((1 : Fin 10), L), s((3 : Fin 10), M)} ∧
      (Finset.univ \ ({0, 1, L, 3, M, 5} : Finset (Fin 10))).card = 4 ∧
      (∀ v ∈ Finset.univ \ ({0, 1, L, 3, M, 5} : Finset (Fin 10)),
        weight v = 2 ∧ ∀ w, ¬ graph.Adj v w) ∧
      1 - dotProduct marked canonicalCoeff = 1 / 5 ∧
      -1 + dotProduct canonicalSource canonicalCoeff = 2 / 15 ∧
      dotProduct marked (gram⁻¹ *ᵥ marked) = 13 / 10 ∧
      gram.det = 2400 ∧ (borderedGram gram marked (-1)).det = 720 := by
  classical
  have hscalars : 1 - dotProduct marked canonicalCoeff = 1 / 5 ∧
      -1 + dotProduct canonicalSource canonicalCoeff = 2 / 15 ∧
      dotProduct marked (gram⁻¹ *ᵥ marked) = 13 / 10 := by
    simpa only [inverse_canonical] using scalar_values
  refine ⟨2, 4, weight_values.2.2.1, weight_values.2.2.2.2.1,
    zero_isolated, five_isolated, first_adj, second_adj,
    first_neighbors.1, first_neighbors.2, second_neighbors.1, second_neighbors.2,
    graph_edgeFinset, ?_, ?_, hscalars.1, hscalars.2.1, hscalars.2.2,
    exceptional_det, bordered_det⟩
  · decide
  · intro v hv
    have hnot : v ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) :=
      (Finset.mem_sdiff.mp hv).2
    have hne : v ≠ 0 ∧ v ≠ 1 ∧ v ≠ 2 ∧ v ≠ 3 ∧ v ≠ 4 ∧ v ≠ 5 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot
    refine ⟨weight_other v hne.2.1 hne.2.2.2.1 hne.2.2.2.2.2, ?_⟩
    intro w
    simp only [graph_adj_iff, hne.2.1, hne.2.2.1, hne.2.2.2.1,
      hne.2.2.2.2.1, false_and, or_self, not_false_eq_true]

end KltDP.LinearAlgebra.FamilyCNonvacuity
