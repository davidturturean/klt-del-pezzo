import KltDP.LinearAlgebra.TenForestClassification

/-!
# Actual algebraic witnesses for A1, A2 and B

C=0, B=1, D=2 and the additional weight-three vertex T=3 in Fin 10.
A1 has the edge 0--3; A2 also has 4--5. B has the path 0--4--3.
The actual graph, inverse source equations, positivity and every original
candidate-forest hypothesis are proved. No surface or Picard realization
is asserted.
-/

namespace KltDP.LinearAlgebra.ABNonvacuity

open Matrix SimpleGraph
open scoped BigOperators

inductive Row where
  | a1 | a2 | b
  deriving DecidableEq

def graph (row : Row) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun i j =>
    (row ≠ .b ∧ i = 0 ∧ j = 3) ∨ (row = .a2 ∧ i = 4 ∧ j = 5) ∨
      (row = .b ∧ ((i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 3))))

instance graphDecidable (row : Row) : DecidableRel (graph row).Adj := by
  intro i j
  change Decidable (i ≠ j ∧
    (((row ≠ .b ∧ i = 0 ∧ j = 3) ∨ (row = .a2 ∧ i = 4 ∧ j = 5) ∨
      (row = .b ∧ ((i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 3)))) ∨
     ((row ≠ .b ∧ j = 0 ∧ i = 3) ∨ (row = .a2 ∧ j = 4 ∧ i = 5) ∨
      (row = .b ∧ ((j = 0 ∧ i = 4) ∨ (j = 4 ∧ i = 3))))))
  infer_instance

def weight (i : Fin 10) : ℕ := if i = 1 ∨ i = 2 ∨ i = 3 then 3 else 2

def gram (row : Row) : Matrix (Fin 10) (Fin 10) ℚ :=
  graphWeightMatrix (graph row) (fun i => (weight i : ℚ))

def canonicalSource (i : Fin 10) : ℚ := (weight i : ℚ) - 2

def marked : Fin 10 → ℚ := threeMarkedSource 0 1 2

def canonicalCoeff (row : Row) (i : Fin 10) : ℚ :=
  if i = 1 ∨ i = 2 then 1 / 3 else
    if row = .b then
      if i = 0 then 1 / 7 else if i = 4 then 2 / 7 else if i = 3 then 3 / 7 else 0
    else if i = 0 then 1 / 5 else if i = 3 then 2 / 5 else 0

def green (row : Row) (i : Fin 10) : ℚ :=
  if i = 1 ∨ i = 2 then 1 / 3 else
    if row = .b then
      if i = 0 then 5 / 7 else if i = 4 then 3 / 7 else if i = 3 then 1 / 7 else 0
    else if i = 0 then 3 / 5 else if i = 3 then 1 / 5 else 0

def listedEdges : Row → Finset (Sym2 (Fin 10))
  | .a1 => {s(0, 3)}
  | .a2 => {s(0, 3), s(4, 5)}
  | .b => {s(0, 4), s(4, 3)}

def listedLength : Row → ℚ | .a1 | .a2 => 2 / 15 | .b => 4 / 21
def listedVolume : Row → ℚ | .a1 | .a2 => 1 / 15 | .b => 2 / 21
def listedGreen : Row → ℚ | .a1 | .a2 => 19 / 15 | .b => 29 / 21
def listedDet : Row → ℚ | .a1 => 2880 | .a2 => 2160 | .b => 2016
def listedBorder : Row → ℚ | .a1 | .b => 768 | .a2 => 576

theorem graph_adj_iff (row : Row) (i j : Fin 10) :
    (graph row).Adj i j ↔
      (row ≠ .b ∧ ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0))) ∨
      (row = .a2 ∧ ((i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4))) ∨
      (row = .b ∧ ((i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
        (i = 4 ∧ j = 3) ∨ (i = 3 ∧ j = 4))) := by
  change (i ≠ j ∧
    (((row ≠ .b ∧ i = 0 ∧ j = 3) ∨ (row = .a2 ∧ i = 4 ∧ j = 5) ∨
      (row = .b ∧ ((i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 3)))) ∨
     ((row ≠ .b ∧ j = 0 ∧ i = 3) ∨ (row = .a2 ∧ j = 4 ∧ i = 5) ∨
      (row = .b ∧ ((j = 0 ∧ i = 4) ∨ (j = 4 ∧ i = 3)))))) ↔ _
  constructor
  · rintro ⟨_, h⟩
    rcases h with h | h
    · rcases h with ⟨hr, hi, hj⟩ | ⟨hr, hi, hj⟩ | ⟨hr, h⟩
      · exact Or.inl ⟨hr, Or.inl ⟨hi, hj⟩⟩
      · exact Or.inr (Or.inl ⟨hr, Or.inl ⟨hi, hj⟩⟩)
      · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact Or.inr (Or.inr ⟨hr, Or.inl ⟨hi, hj⟩⟩)
        · exact Or.inr (Or.inr ⟨hr, Or.inr (Or.inr (Or.inl ⟨hi, hj⟩))⟩)
    · rcases h with ⟨hr, hj, hi⟩ | ⟨hr, hj, hi⟩ | ⟨hr, h⟩
      · exact Or.inl ⟨hr, Or.inr ⟨hi, hj⟩⟩
      · exact Or.inr (Or.inl ⟨hr, Or.inr ⟨hi, hj⟩⟩)
      · rcases h with ⟨hj, hi⟩ | ⟨hj, hi⟩
        · exact Or.inr (Or.inr ⟨hr, Or.inr (Or.inl ⟨hi, hj⟩)⟩)
        · exact Or.inr (Or.inr ⟨hr, Or.inr (Or.inr (Or.inr ⟨hi, hj⟩))⟩)
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    refine ⟨hne, ?_⟩
    rcases h with ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩
    · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact Or.inl (Or.inl ⟨hr, hi, hj⟩)
      · exact Or.inr (Or.inl ⟨hr, hj, hi⟩)
    · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact Or.inl (Or.inr (Or.inl ⟨hr, hi, hj⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hr, hj, hi⟩))
    · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact Or.inl (Or.inr (Or.inr ⟨hr, Or.inl ⟨hi, hj⟩⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hr, Or.inl ⟨hj, hi⟩⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨hr, Or.inr ⟨hi, hj⟩⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hr, Or.inr ⟨hj, hi⟩⟩))

theorem graph_edgeFinset (row : Row) : (graph row).edgeFinset = listedEdges row := by
  apply Finset.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro i j
  cases row <;>
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      graph_adj_iff, listedEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] <;> tauto

theorem edge_card_le_two (row : Row) : (graph row).edgeFinset.card ≤ 2 := by
  rw [graph_edgeFinset]
  cases row <;> decide

theorem graph_isAcyclic (row : Row) : (graph row).IsAcyclic := by
  intro v p hp
  have hlow := hp.three_le_length
  have hupp := hp.isTrail.length_le_card_edgeFinset
  have hb := edge_card_le_two row
  omega

theorem weight_values : weight 0 = 2 ∧ weight 1 = 3 ∧ weight 2 = 3 ∧
    weight 3 = 3 ∧ weight 4 = 2 ∧ weight 5 = 2 := by decide

theorem weight_other (i : Fin 10) (hiB : i ≠ 1) (hiD : i ≠ 2)
    (hiT : i ≠ 3) : weight i = 2 := by simp [weight, hiB, hiD, hiT]

theorem core_isolated (row : Row) :
    (∀ j, ¬ (graph row).Adj 1 j) ∧ (∀ j, ¬ (graph row).Adj 2 j) := by
  constructor <;> intro j <;>
    simp only [graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

private theorem reachable_eq_of_isolated {V : Type*} (G : SimpleGraph V)
    (root v : V) (hisolated : ∀ j, ¬ G.Adj root j) : G.Reachable root v ↔ v = root := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact (hisolated _ h).elim
  · intro h
    subst v
    exact .refl root

theorem cores_separate (row : Row) : ¬ (graph row).Reachable 1 2 := by
  rw [reachable_eq_of_isolated (graph row) 1 2 (core_isolated row).1]
  decide

theorem original_graph_hypotheses (row : Row) :
    (∀ i, weight i = 2 ∨ weight i = 3) ∧
    (candidateExtraVertices weight 0 1 2).card = 1 ∧
    ¬ (graph row).Adj 0 1 ∧ ¬ (graph row).Adj 0 2 ∧ ¬ (graph row).Adj 1 2 ∧
    (graph row).degree 0 ≤ 1 ∧ (∀ i, (graph row).degree i ≤ 3) ∧
    (∃ i, (graph row).Adj 0 i ∨ (graph row).Adj 1 i ∨ (graph row).Adj 2 i) := by
  cases row <;> decide

private theorem det_eq_of_matrix_eq {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℚ) (hAB : A = B) (d : ℚ) (hB : B.det = d) : A.det = d :=
  (congrArg Matrix.det hAB).trans hB

/-- Apply the graph determinant theorem and transport equality before
specializing the vertex type and the matrix. -/
private theorem familyA1_det_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ)
    (A : Matrix V V ℚ) (hA : A = graphWeightMatrix G (fun i => (w i : ℚ)))
    (C T B D : V) (hcard : Fintype.card V = 10)
    (hC : w C = 2) (hT : w T = 3) (hB : w B = 3) (hD : w D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) (hCT : G.Adj C T)
    (hedges : G.edgeFinset = {s(C, T)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → w i = 2) :
    A.det = 2880 := by
  have hd := familyA1_exceptional_det (𝕜 := ℚ) G w C T B D
    hcard hC hT hB hD hTB hTD hBD hCT hedges hother
  exact det_eq_of_matrix_eq A (graphWeightMatrix G (fun i => (w i : ℚ))) hA 2880 hd

private theorem familyA2_det_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ)
    (A : Matrix V V ℚ) (hA : A = graphWeightMatrix G (fun i => (w i : ℚ)))
    (C T B D u v : V) (hcard : Fintype.card V = 10)
    (hC : w C = 2) (hT : w T = 3) (hB : w B = 3) (hD : w D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) (hCT : G.Adj C T)
    (huv : u ≠ v) (hu : u ∉ ({C, T, B, D} : Finset V))
    (hv : v ∉ ({C, T, B, D} : Finset V)) (hu2 : w u = 2) (hv2 : w v = 2)
    (hedges : G.edgeFinset = {s(C, T), s(u, v)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → w i = 2) :
    A.det = 2160 := by
  have hd := familyA2_exceptional_det (𝕜 := ℚ) G w C T B D u v
    hcard hC hT hB hD hTB hTD hBD hCT huv hu hv hu2 hv2 hedges hother
  exact det_eq_of_matrix_eq A (graphWeightMatrix G (fun i => (w i : ℚ))) hA 2160 hd

private theorem familyB_det_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ)
    (A : Matrix V V ℚ) (hA : A = graphWeightMatrix G (fun i => (w i : ℚ)))
    (C M T B D : V) (hcard : Fintype.card V = 10)
    (hC : w C = 2) (hM : w M = 2) (hT : w T = 3) (hB : w B = 3) (hD : w D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hCM : G.Adj C M) (hMT : G.Adj M T)
    (hedges : G.edgeFinset = {s(C, M), s(M, T)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → w i = 2) :
    A.det = 2016 := by
  have hd := familyB_exceptional_det (𝕜 := ℚ) G w C M T B D
    hcard hC hM hT hB hD hTB hTD hBD hCM hMT hedges hother
  exact det_eq_of_matrix_eq A (graphWeightMatrix G (fun i => (w i : ℚ))) hA 2016 hd

/-- The large determinants are supplied by the actual graph block theorems. -/
theorem exceptional_det (row : Row) : (gram row).det = listedDet row := by
  cases row
  · exact familyA1_det_of_matrix_eq (graph .a1) weight (gram .a1) rfl 0 3 1 2 (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (graph_edgeFinset .a1) weight_other
  · exact familyA2_det_of_matrix_eq (graph .a2) weight (gram .a2) rfl 0 3 1 2 4 5 (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (graph_edgeFinset .a2) weight_other
  · exact familyB_det_of_matrix_eq (graph .b) weight (gram .b) rfl 0 4 3 1 2 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (graph_edgeFinset .b) weight_other

theorem gram_isUnit (row : Row) : IsUnit (gram row) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [exceptional_det]
  cases row <;> norm_num [listedDet]

private theorem finTen_sum (f : Fin 10 → ℚ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 +
      (f 5 + (f 6 + (f 7 + (f 8 + f 9)))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl

set_option maxHeartbeats 2000000 in
theorem canonical_row (row : Row) : gram row *ᵥ canonicalCoeff row = canonicalSource := by
  ext i
  fin_cases i <;> cases row <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct, finTen_sum,
      canonicalCoeff, canonicalSource, weight, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, reduceCtorEq] <;>
    norm_num [show Row.a1 ≠ Row.b by decide, show Row.a2 ≠ Row.b by decide]

set_option maxHeartbeats 2000000 in
theorem green_row (row : Row) : gram row *ᵥ green row = marked := by
  ext i
  fin_cases i <;> cases row <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct, finTen_sum,
      green, marked, threeMarkedSource, Pi.add_apply, Pi.single_apply, weight, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, reduceCtorEq] <;>
    norm_num [show Row.a1 ≠ Row.b by decide, show Row.a2 ≠ Row.b by decide]

theorem inverse_canonical (row : Row) : (gram row)⁻¹ *ᵥ canonicalSource = canonicalCoeff row := by
  letI : Invertible (gram row) := (gram_isUnit row).invertible
  exact Matrix.inv_mulVec_eq_vec (canonical_row row).symm

theorem inverse_green (row : Row) : (gram row)⁻¹ *ᵥ marked = green row := by
  letI : Invertible (gram row) := (gram_isUnit row).invertible
  exact Matrix.inv_mulVec_eq_vec (green_row row).symm

theorem canonical_bounds (row : Row) : ∀ i,
    0 ≤ ((gram row)⁻¹ *ᵥ canonicalSource) i ∧ ((gram row)⁻¹ *ᵥ canonicalSource) i < 1 := by
  rw [inverse_canonical]
  intro i
  dsimp only [canonicalCoeff]
  split_ifs <;> norm_num

theorem scalar_values (row : Row) :
    1 - dotProduct marked ((gram row)⁻¹ *ᵥ canonicalSource) = listedLength row ∧
    -1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource) = listedVolume row ∧
    dotProduct marked ((gram row)⁻¹ *ᵥ marked) = listedGreen row := by
  rw [inverse_canonical, inverse_green]
  cases row <;>
    simp only [dotProduct, finTen_sum, marked, threeMarkedSource, Pi.add_apply, Pi.single_apply,
      canonicalCoeff, canonicalSource, green, weight, listedLength, listedVolume, listedGreen,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, reduceCtorEq] <;> norm_num

theorem positive_volume_budget (row : Row) :
    0 < -1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource) ∧
    -1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource) ≤
      1 - dotProduct marked ((gram row)⁻¹ *ᵥ canonicalSource) := by
  rw [(scalar_values row).1, (scalar_values row).2.1]
  cases row <;> norm_num [listedLength, listedVolume]

theorem projection_identity (row : Row) :
    (-1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource)) *
      (dotProduct marked ((gram row)⁻¹ *ᵥ marked) - 1) =
      (1 - dotProduct marked ((gram row)⁻¹ *ᵥ canonicalSource))^2 := by
  rw [(scalar_values row).1, (scalar_values row).2.1, (scalar_values row).2.2]
  cases row <;> norm_num [listedLength, listedVolume, listedGreen]

private theorem ten_vertex_border_of_values {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℚ) (p : V → ℚ) (d g delta : ℚ)
    (hcard : Fintype.card V = 10) (hA : IsUnit A) (hd : A.det = d)
    (hg : dotProduct p (A⁻¹ *ᵥ p) = g) (hdelta : d * (g - 1) = delta) :
    (borderedGram A p (-1)).det = delta := by
  apply (det_minusOne_borderedGram hA p).trans
  rw [hcard, hd, hg, show (-1 : ℚ)^10 = 1 by norm_num, one_mul]
  exact hdelta

theorem bordered_det (row : Row) : (borderedGram (gram row) marked (-1)).det = listedBorder row := by
  have hunit := gram_isUnit row
  have hdet := exceptional_det row
  have hg := (scalar_values row).2.2
  generalize hmatrix : gram row = A at hunit hdet hg ⊢
  generalize hvector : marked = p at hg ⊢
  apply ten_vertex_border_of_values A p (listedDet row) (listedGreen row) (listedBorder row)
    (by decide) hunit hdet hg
  cases row <;> norm_num [listedDet, listedGreen, listedBorder]

private theorem gram_isHermitian (row : Row) : (gram row).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  by_cases hij : i = j
  · subst j
    simp [gram, graphWeightMatrix_diagonal]
  · have hadj : (graph row).Adj j i ↔ (graph row).Adj i j := ⟨fun h => h.symm, fun h => h.symm⟩
    simp only [gram, graphWeightMatrix_apply, if_neg hij, if_neg (Ne.symm hij), star_trivial, hadj]

def positiveFactor : Row → ℚ | .a1 | .a2 => 1 | .b => 1 / 2

def squareRemainder (row : Row) (x : Fin 10 → ℚ) : ℚ :=
  match row with
  | .a1 => (x 0 - x 3)^2 + 2*(x 1)^2 + 2*(x 2)^2 + (x 3)^2 +
      (x 4)^2 + (x 5)^2 + (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2
  | .a2 => (x 0 - x 3)^2 + 2*(x 1)^2 + 2*(x 2)^2 + (x 3)^2 +
      (x 4 - x 5)^2 + (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2
  | .b => (3/2)*(x 0 - 2*x 4/3)^2 + (5/6)*(x 4 - 6*x 3/5)^2 +
      (13/10)*(x 3)^2 + (5/2)*((x 1)^2 + (x 2)^2) +
      (3/2)*((x 5)^2 + (x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2)

set_option maxHeartbeats 2000000 in
private theorem quadratic_form (row : Row) (x : Fin 10 → ℚ) :
    dotProduct x (gram row *ᵥ x) =
      positiveFactor row * (∑ i, (x i)^2) + squareRemainder row x := by
  cases row <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct, finTen_sum,
      weight, graph_adj_iff, positiveFactor, squareRemainder,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk, reduceCtorEq] <;>
    norm_num [show Row.a1 ≠ Row.b by decide, show Row.a2 ≠ Row.b by decide] <;> ring

/-- Strict positivity is supplied by a positive multiple of all coordinate squares. -/
theorem gram_posDef (row : Row) : (gram row).PosDef := by
  refine ⟨gram_isHermitian row, ?_⟩
  intro x hx
  have hpositive : 0 < ∑ i : Fin 10, (x i)^2 := by
    apply Finset.sum_pos'
    · intro i _
      exact sq_nonneg (x i)
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hfactor : 0 < positiveFactor row := by cases row <;> norm_num [positiveFactor]
  have hrest : 0 ≤ squareRemainder row x := by cases row <;> dsimp only [squareRemainder] <;> positivity
  rw [show star x = x from star_trivial x, quadratic_form]
  exact add_pos_of_pos_of_nonneg (mul_pos hfactor hpositive) hrest

/-- Every original hypothesis of the candidate-forest lemma holds for each
of these three actual graphs and its actual inverse-defined coefficients. -/
theorem original_source_hypotheses (row : Row) :
    Fintype.card (Fin 10) = 3 + 7 ∧ (graph row).IsAcyclic ∧
    weight 0 = 2 ∧ weight 1 = 3 ∧ weight 2 = 3 ∧
    (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → weight i = 2 ∨ weight i = 3) ∧
    (candidateExtraVertices weight 0 1 2).card ≤ 2 ∧
    ¬ (graph row).Adj 0 1 ∧ ¬ (graph row).Adj 0 2 ∧ ¬ (graph row).Adj 1 2 ∧
    ¬ (graph row).Reachable 1 2 ∧ (graph row).degree 0 ≤ 1 ∧
    (∀ i, (graph row).degree i ≤ 3) ∧ (graph row).edgeFinset.card ≤ 3 - 1 ∧
    (∃ i, (graph row).Adj 0 i ∨ (graph row).Adj 1 i ∨ (graph row).Adj 2 i) ∧
    (gram row).PosDef ∧
    (∀ i, 0 ≤ ((gram row)⁻¹ *ᵥ canonicalSource) i ∧
      ((gram row)⁻¹ *ᵥ canonicalSource) i < 1) ∧
    0 < -1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource) ∧
    -1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource) ≤
      1 - dotProduct marked ((gram row)⁻¹ *ᵥ canonicalSource) ∧
    (-1 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource)) *
      (dotProduct marked ((gram row)⁻¹ *ᵥ marked) - 1) =
      (1 - dotProduct marked ((gram row)⁻¹ *ᵥ canonicalSource))^2 := by
  obtain ⟨hw, he, h01, h02, h12, hdeg0, hdeg, hboundary⟩ := original_graph_hypotheses row
  exact ⟨by decide, graph_isAcyclic row, weight_values.1, weight_values.2.1,
    weight_values.2.2.1, fun i _ _ _ => hw i, by omega,
    h01, h02, h12, cores_separate row, hdeg0, hdeg, edge_card_le_two row,
    hboundary, gram_posDef row, canonical_bounds row,
    (positive_volume_budget row).1, (positive_volume_budget row).2, projection_identity row⟩

/-- The explicit canonical vector has exactly the manuscript's inverse definition. -/
theorem canonical_definition (row : Row) :
    canonicalCoeff row = (gram row)⁻¹ *ᵥ canonicalSource :=
  (inverse_canonical row).symm

/-- The displayed row labels select their own actual entire edge set and
their actual canonical isolated remainder, rather than an independent list. -/
theorem row_graph_shape (row : Row) :
    match row with
    | .a1 => (graph row).edgeFinset = {s((0 : Fin 10), 3)} ∧
        (Finset.univ \ ({0, 3, 1, 2} : Finset (Fin 10))).card = 6 ∧
        (∀ i ∈ Finset.univ \ ({0, 3, 1, 2} : Finset (Fin 10)),
          weight i = 2 ∧ ∀ j, ¬ (graph row).Adj i j)
    | .a2 => (graph row).edgeFinset = {s((0 : Fin 10), 3), s((4 : Fin 10), 5)} ∧
        (Finset.univ \ ({4, 5, 0, 3, 1, 2} : Finset (Fin 10))).card = 4 ∧
        (∀ i ∈ Finset.univ \ ({4, 5, 0, 3, 1, 2} : Finset (Fin 10)),
          weight i = 2 ∧ ∀ j, ¬ (graph row).Adj i j)
    | .b => (graph row).edgeFinset = {s((0 : Fin 10), 4), s((4 : Fin 10), 3)} ∧
        (Finset.univ \ ({0, 4, 3, 1, 2} : Finset (Fin 10))).card = 5 ∧
        (∀ i ∈ Finset.univ \ ({0, 4, 3, 1, 2} : Finset (Fin 10)),
          weight i = 2 ∧ ∀ j, ¬ (graph row).Adj i j) := by
  cases row
  · exact ⟨graph_edgeFinset .a1, by decide, by decide⟩
  · exact ⟨graph_edgeFinset .a2, by decide, by decide⟩
  · exact ⟨graph_edgeFinset .b, by decide, by decide⟩

/-- Transport source aliases before specializing inverses and determinants. -/
private theorem matrix_source_aliases {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℚ) (p q : V → ℚ) (hAB : A = B) (hpq : p = q) :
    dotProduct p (A⁻¹ *ᵥ p) = dotProduct q (B⁻¹ *ᵥ q) ∧
      (borderedGram A p (-1)).det = (borderedGram B q (-1)).det := by
  subst B
  subst q
  exact ⟨rfl, rfl⟩

/-- Each concrete input satisfies the entire A/B source-row conclusion.
The witnesses in the A2 and B branches are the actual vertices 4,5 and 4. -/
theorem source_row_witness (row : Row) :
    ABForestRows (graph row) weight (canonicalCoeff row) 0 1 2 3 := by
  have hvalues := scalar_values row
  rw [inverse_canonical] at hvalues
  have hdet := exceptional_det row
  have hborder := bordered_det row
  have hshape := row_graph_shape row
  have hiso := core_isolated row
  have halias := matrix_source_aliases
    (graphWeightMatrix (graph row) (fun i => (weight i : ℚ))) (gram row)
    (threeMarkedSource 0 1 2) marked rfl rfl
  have hrawGreen := halias.1.trans hvalues.2.2
  have hrawBorder := halias.2.trans hborder
  have hrawDet := det_eq_of_matrix_eq
    (graphWeightMatrix (graph row) (fun i => (weight i : ℚ))) (gram row)
    rfl (listedDet row) hdet
  cases row
  · exact ⟨hiso.1, hiso.2, Or.inl
      ⟨hshape.1, hshape.2.1, hshape.2.2, hvalues.1, hvalues.2.1, hrawGreen,
        hrawDet, hrawBorder⟩⟩
  · exact ⟨hiso.1, hiso.2, Or.inr (Or.inl
      ⟨4, 5, by decide, by decide, by decide, by decide, by decide,
        hshape.1, hshape.2.1, hshape.2.2, hvalues.1, hvalues.2.1, hrawGreen,
        hrawDet, hrawBorder⟩)⟩
  · exact ⟨hiso.1, hiso.2, Or.inr (Or.inr
      ⟨4, by decide, by decide, by decide, hshape.1, hshape.2.1, hshape.2.2,
        hvalues.1, hvalues.2.1, hrawGreen, hrawDet, hrawBorder⟩)⟩

end KltDP.LinearAlgebra.ABNonvacuity
