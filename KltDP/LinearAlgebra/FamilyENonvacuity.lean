import KltDP.LinearAlgebra.FamilyEAllocation

/-!
# Four actual positive-definite graph witnesses for family E

The vertex type is Fin 11. The fixed vertices C,B,M,D,T,U are 0,1,2,3,4,5.
The only fixed edge is 1--2. Rows 0,1,2,3 give respectively no remaining
edge, 6--7, the path 6--7--8, and the disjoint edges 6--7 and 8--9.

Positive definiteness is proved by a rational sum-of-squares identity for
the actual graph matrix. Explicit row solutions are then identified with
actual inverse images. These are algebraic forest witnesses, with no claim
of a surface or a Picard-lattice realization.
-/

namespace KltDP.LinearAlgebra.FamilyENonvacuity

open Matrix SimpleGraph
open scoped BigOperators

/-- Actual graphs for E1--E4, in the source's order. -/
def graph (row : Fin 4) : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel (fun i j => (i = 1 ∧ j = 2) ∨
    (row ≠ 0 ∧ i = 6 ∧ j = 7) ∨ (row = 2 ∧ i = 7 ∧ j = 8) ∨
    (row = 3 ∧ i = 8 ∧ j = 9))

instance graphDecidable (row : Fin 4) : DecidableRel (graph row).Adj := by
  intro i j
  change Decidable (i ≠ j ∧
    (((i = 1 ∧ j = 2) ∨ (row ≠ 0 ∧ i = 6 ∧ j = 7) ∨
      (row = 2 ∧ i = 7 ∧ j = 8) ∨ (row = 3 ∧ i = 8 ∧ j = 9)) ∨
     ((j = 1 ∧ i = 2) ∨ (row ≠ 0 ∧ j = 6 ∧ i = 7) ∨
      (row = 2 ∧ j = 7 ∧ i = 8) ∨ (row = 3 ∧ j = 8 ∧ i = 9))))
  infer_instance

def weight (i : Fin 11) : ℚ :=
  if i = 1 ∨ i = 4 ∨ i = 5 then 3 else if i = 3 then 4 else 2

def gram (row : Fin 4) : Matrix (Fin 11) (Fin 11) ℚ := graphWeightMatrix (graph row) weight

def canonicalSource (i : Fin 11) : ℚ := weight i - 2

def marked : Fin 11 → ℚ := threeMarkedSource 0 1 3

def canonicalCoeff (i : Fin 11) : ℚ :=
  if i = 1 then 2 / 5 else if i = 2 then 1 / 5 else if i = 3 then 1 / 2 else
    if i = 4 ∨ i = 5 then 1 / 3 else 0

def green (i : Fin 11) : ℚ :=
  if i = 0 then 1 / 2 else if i = 1 then 2 / 5 else if i = 2 then 1 / 5 else
    if i = 3 then 1 / 4 else 0

def listedEdges (row : Fin 4) : Finset (Sym2 (Fin 11)) :=
  if row = 0 then {s(1, 2)} else if row = 1 then {s(1, 2), s(6, 7)} else
    if row = 2 then {s(1, 2), s(6, 7), s(7, 8)} else {s(1, 2), s(6, 7), s(8, 9)}

/-- The loop guard is discharged symbolically from the distinct endpoints,
so subsequent checks need not expand every pair of finite vertices. -/
theorem graph_adj_iff (row : Fin 4) (i j : Fin 11) :
    (graph row).Adj i j ↔
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (row ≠ 0 ∧ ((i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6))) ∨
      (row = 2 ∧ ((i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7))) ∨
      (row = 3 ∧ ((i = 8 ∧ j = 9) ∨ (i = 9 ∧ j = 8))) := by
  change (i ≠ j ∧
    (((i = 1 ∧ j = 2) ∨ (row ≠ 0 ∧ i = 6 ∧ j = 7) ∨
      (row = 2 ∧ i = 7 ∧ j = 8) ∨ (row = 3 ∧ i = 8 ∧ j = 9)) ∨
     ((j = 1 ∧ i = 2) ∨ (row ≠ 0 ∧ j = 6 ∧ i = 7) ∨
      (row = 2 ∧ j = 7 ∧ i = 8) ∨ (row = 3 ∧ j = 8 ∧ i = 9)))) ↔ _
  constructor
  · rintro ⟨_, h⟩
    rcases h with h | h
    · rcases h with h | ⟨hr, hi, hj⟩ | ⟨hr, hi, hj⟩ | ⟨hr, hi, hj⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl ⟨hr, Or.inl ⟨hi, hj⟩⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, Or.inl ⟨hi, hj⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, Or.inl ⟨hi, hj⟩⟩)))
    · rcases h with ⟨hj, hi⟩ | ⟨hr, hj, hi⟩ | ⟨hr, hj, hi⟩ | ⟨hr, hj, hi⟩
      · exact Or.inr (Or.inl ⟨hi, hj⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hr, Or.inr ⟨hi, hj⟩⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, Or.inr ⟨hi, hj⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, Or.inr ⟨hi, hj⟩⟩)))
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · decide
      · decide
      all_goals rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    refine ⟨hne, ?_⟩
    rcases h with h | ⟨hi, hj⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl ⟨hj, hi⟩)
    · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact Or.inl (Or.inr (Or.inl ⟨hr, hi, hj⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hr, hj, hi⟩))
    · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hr, hi, hj⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, hj, hi⟩)))
    · rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hr, hi, hj⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, hj, hi⟩)))

set_option maxHeartbeats 4000000 in
theorem graph_edgeFinset (row : Fin 4) : (graph row).edgeFinset = listedEdges row := by
  have hcases : row = 0 ∨ row = 1 ∨ row = 2 ∨ row = 3 := by omega
  rcases hcases with hrow | hrow | hrow | hrow
  all_goals
    have h0 : row = 0 ∨ row ≠ 0 := eq_or_ne row 0
    have h1 : row = 1 ∨ row ≠ 1 := eq_or_ne row 1
    have h2 : row = 2 ∨ row ≠ 2 := eq_or_ne row 2
    have h3 : row = 3 ∨ row ≠ 3 := eq_or_ne row 3
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> try omega
    apply Finset.ext
    intro e
    refine Sym2.inductionOn e ?_
    intro i j
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graph_adj_iff,
      listedEdges, h0, h1, h2, h3, Sym2.eq_iff] <;> tauto

theorem edge_card_le_three (row : Fin 4) : (graph row).edgeFinset.card ≤ 3 := by
  rw [graph_edgeFinset]
  unfold listedEdges
  split_ifs
  · simp
  · exact Finset.card_le_two.trans (by decide)
  · exact Finset.card_le_three
  · exact Finset.card_le_three

set_option maxHeartbeats 2000000 in
theorem triangle_free (row : Fin 4) :
    ∀ i j k, ¬ ((graph row).Adj i j ∧ (graph row).Adj j k ∧ (graph row).Adj k i) := by
  fin_cases row <;> decide

/-- A cycle would have exactly three edges and hence give an actual
triangle, contradicting the verified adjacency predicate. -/
theorem graph_isAcyclic (row : Fin 4) : (graph row).IsAcyclic := by
  intro v walk hcycle
  have hlow := hcycle.three_le_length
  have hupp := hcycle.isTrail.length_le_card_edgeFinset
  have hedge := edge_card_le_three row
  have hlength : walk.length = 3 := by omega
  have h01 := walk.adj_getVert_succ (i := 0) (by omega)
  have h12 := walk.adj_getVert_succ (i := 1) (by omega)
  have h23 := walk.adj_getVert_succ (i := 2) (by omega)
  have hend : walk.getVert 3 = v := by rw [← hlength]; exact walk.getVert_length
  have h20 : (graph row).Adj (walk.getVert 2) (walk.getVert 0) := by
    simpa only [show 2 + 1 = 3 from rfl, hend, SimpleGraph.Walk.getVert_zero] using h23
  exact triangle_free row _ _ _ ⟨h01, h12, h20⟩

/-- Nonnegative residual form of the canonical five-vertex block after
subtracting one half of the squared Euclidean norm. -/
def canonicalRemainder (row : Fin 4) (x : Fin 11 → ℚ) : ℚ :=
  if row = 0 then (3 / 2) * ((x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2 + (x 10)^2)
  else if row = 1 then (x 6 - x 7)^2 + (1 / 2) * ((x 6)^2 + (x 7)^2) +
    (3 / 2) * ((x 8)^2 + (x 9)^2 + (x 10)^2)
  else if row = 2 then
    (3 / 2) * (x 6 - (2 / 3) * x 7)^2 + (3 / 2) * (x 8 - (2 / 3) * x 7)^2 +
      (1 / 6) * (x 7)^2 + (3 / 2) * ((x 9)^2 + (x 10)^2)
  else (x 6 - x 7)^2 + (x 8 - x 9)^2 +
    (1 / 2) * ((x 6)^2 + (x 7)^2 + (x 8)^2 + (x 9)^2) + (3 / 2) * (x 10)^2

theorem canonicalRemainder_nonneg (row : Fin 4) (x : Fin 11 → ℚ) :
    0 ≤ canonicalRemainder row x := by
  fin_cases row <;> norm_num only [canonicalRemainder] <;> positivity

private theorem finEleven_sum (f : Fin 11 → ℚ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 +
      (f 6 + (f 7 + (f 8 + (f 9 + f 10))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl

set_option maxHeartbeats 4000000 in
/-- Positive definiteness of each actual graph matrix, proved by an
explicit sum of nonnegative squares with a positive norm term. -/
theorem gram_posDef (row : Fin 4) : (gram row).PosDef := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext_iff.mpr
    intro i j
    by_cases hij : i = j
    · subst j
      simp [gram, graphWeightMatrix_diagonal]
    · have hadj : (graph row).Adj j i ↔ (graph row).Adj i j :=
        ⟨fun h => h.symm, fun h => h.symm⟩
      simp only [gram, graphWeightMatrix_apply, if_neg hij, if_neg (Ne.symm hij),
        star_trivial, hadj]
  · intro x hx
    have hpositive : 0 < ∑ i : Fin 11, (x i)^2 := by
      apply Finset.sum_pos'
      · intro i _
        exact sq_nonneg (x i)
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
        exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hformula : dotProduct (star x) (gram row *ᵥ x) =
        (1 / 2) * (∑ i : Fin 11, (x i)^2) + (x 1 - x 2)^2 +
        (3 / 2) * (x 0)^2 + (3 / 2) * (x 1)^2 + (1 / 2) * (x 2)^2 +
        (7 / 2) * (x 3)^2 + (5 / 2) * (x 4)^2 + (5 / 2) * (x 5)^2 +
        canonicalRemainder row x := by
      fin_cases row <;>
        simp only [star_trivial, gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
          finEleven_sum, weight, graph_adj_iff, canonicalRemainder,
          Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk] <;> norm_num <;> ring
    have hR := canonicalRemainder_nonneg row x
    have hrest : 0 ≤ (x 1 - x 2)^2 +
        (3 / 2) * (x 0)^2 + (3 / 2) * (x 1)^2 + (1 / 2) * (x 2)^2 +
        (7 / 2) * (x 3)^2 + (5 / 2) * (x 4)^2 + (5 / 2) * (x 5)^2 +
        canonicalRemainder row x := by positivity
    rw [hformula]
    linarith only [hpositive, hrest]

theorem gram_isUnit (row : Fin 4) : IsUnit (gram row) := isUnit_of_posDef (gram_posDef row)

set_option maxHeartbeats 4000000 in
theorem canonical_row (row : Fin 4) : gram row *ᵥ canonicalCoeff = canonicalSource := by
  ext i
  fin_cases row <;> fin_cases i <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct, finEleven_sum,
      canonicalCoeff, canonicalSource, weight, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk] <;> norm_num

set_option maxHeartbeats 4000000 in
theorem green_row (row : Fin 4) : gram row *ᵥ green = marked := by
  ext i
  fin_cases row <;> fin_cases i <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct, finEleven_sum,
      green, marked, threeMarkedSource, Pi.single_apply, Pi.add_apply, weight, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk] <;> norm_num

theorem inverse_canonical (row : Fin 4) : (gram row)⁻¹ *ᵥ canonicalSource = canonicalCoeff := by
  letI : Invertible (gram row) := (gram_isUnit row).invertible
  exact Matrix.inv_mulVec_eq_vec (canonical_row row).symm

theorem inverse_green (row : Fin 4) : (gram row)⁻¹ *ᵥ marked = green := by
  letI : Invertible (gram row) := (gram_isUnit row).invertible
  exact Matrix.inv_mulVec_eq_vec (green_row row).symm

theorem scalar_values (row : Fin 4) :
    1 - dotProduct marked ((gram row)⁻¹ *ᵥ canonicalSource) = 1 / 10 ∧
      -2 + dotProduct canonicalSource ((gram row)⁻¹ *ᵥ canonicalSource) = 1 / 15 ∧
      dotProduct marked ((gram row)⁻¹ *ᵥ marked) = 23 / 20 := by
  rw [inverse_canonical, inverse_green]
  simp only [dotProduct, finEleven_sum, marked, threeMarkedSource, Pi.single_apply,
    Pi.add_apply, canonicalCoeff, canonicalSource, green, weight,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk]
  norm_num

theorem positive_volume_budget (row : Fin 4) :
    0 < -2 + dotProduct canonicalSource canonicalCoeff ∧
      -2 + dotProduct canonicalSource canonicalCoeff ≤ 1 - dotProduct marked canonicalCoeff := by
  obtain ⟨hl, hv, _⟩ := scalar_values row
  rw [inverse_canonical] at hl hv
  rw [hl, hv]
  norm_num

theorem canonical_bounds : ∀ i, 0 ≤ canonicalCoeff i ∧ canonicalCoeff i < 1 := by
  intro i
  fin_cases i <;>
    simp only [canonicalCoeff, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk] <;> norm_num

theorem projection_identity (row : Fin 4) :
    (-2 + dotProduct canonicalSource canonicalCoeff) *
        (dotProduct marked ((gram row)⁻¹ *ᵥ marked) - 1) =
      (1 - dotProduct marked canonicalCoeff)^2 := by
  obtain ⟨hl, hv, hg⟩ := scalar_values row
  rw [inverse_canonical] at hl hv
  rw [hl, hv, hg]
  norm_num

theorem weight_other (i : Fin 11) (hiB : i ≠ 1) (hiD : i ≠ 3)
    (hiT : i ≠ 4) (hiU : i ≠ 5) : weight i = 2 := by
  simp [weight, hiB, hiD, hiT, hiU]

theorem core_adj (row : Fin 4) : (graph row).Adj 1 2 :=
  (graph_adj_iff row 1 2).mpr (Or.inl ⟨rfl, rfl⟩)

theorem core_neighbors (row : Fin 4) :
    (graph row).neighborFinset 1 = {2} ∧ (graph row).neighborFinset 2 = {1} := by
  constructor <;> ext i <;>
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton,
      graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

theorem fixed_isolated (row : Fin 4) (i : Fin 11)
    (hi : i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 5) : ∀ j, ¬ (graph row).Adj i j := by
  intro j
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

private theorem reachable_iff_eq_of_isolated (row : Fin 4) (root : Fin 11)
    (hisolated : ∀ j, ¬ (graph row).Adj root j) (v : Fin 11) :
    (graph row).Reachable root v ↔ v = root := by
  constructor
  · rintro ⟨walk⟩
    cases walk with
    | nil => rfl
    | cons hadj rest => exact (hisolated _ hadj).elim
  · intro h
    subst v
    exact SimpleGraph.Reachable.refl root

theorem component_core (row : Fin 4) (v : Fin 11) :
    (graph row).Reachable 1 v ↔ v = 1 ∨ v = 2 :=
  reachable_iff_of_mutual_singleton_neighbors (graph row) 1 2 (core_adj row)
    (core_neighbors row).1 (core_neighbors row).2 v

theorem canonical_component (row : Fin 4) (v : Fin 11)
    (hv : (graph row).Reachable 0 v) : weight v = 2 := by
  have heq := (reachable_iff_eq_of_isolated row 0 (fixed_isolated row 0 (by simp)) v).mp hv
  subst v
  simp only [weight, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  norm_num

theorem core_single_source (row : Fin 4) (v : Fin 11)
    (hv : (graph row).Reachable 1 v) (hne : v ≠ 1) : weight v = 2 := by
  rcases (component_core row v).mp hv with hv | hv
  · exact (hne hv).elim
  · subst v
    simp only [weight, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    norm_num

theorem isolated_single_source (row : Fin 4) (root : Fin 11)
    (hroot : root = 3 ∨ root = 4 ∨ root = 5)
    (v : Fin 11) (hv : (graph row).Reachable root v) (hne : v ≠ root) : weight v = 2 := by
  have hiso := fixed_isolated row root (Or.inr hroot)
  exact (hne ((reachable_iff_eq_of_isolated row root hiso v).mp hv)).elim

set_option maxHeartbeats 2000000 in
/-- The remaining finite local hypotheses of the source graph statement. -/
theorem local_graph_bounds (row : Fin 4) :
    (graph row).degree 0 = 0 ∧ (∀ i, (graph row).degree i ≤ 2) ∧
      ¬ (graph row).Adj 0 1 ∧ ¬ (graph row).Adj 0 3 ∧ ¬ (graph row).Adj 1 3 := by
  fin_cases row <;> decide

/-- Keep the actual matrix and both source vectors abstract while applying
the full classifier and identifying its returned neighbor. This avoids
reducing a concrete inverse matrix during expected-type comparison. -/
private theorem complete_forest_remaining_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (w a : V → ℚ) (C B M₀ D T U : V)
    (A : Matrix V V ℚ) (q p : V → ℚ)
    (hAeq : A = graphWeightMatrix G w)
    (hq : q = fun i => w i - 2) (hp : p = threeMarkedSource C B D)
    (hcard : Fintype.card V = 11) (hA : IsUnit A) (hG : G.IsAcyclic)
    (hrow : A *ᵥ a = q) (hedges : G.edgeFinset.card ≤ 3)
    (hB : w B = 3) (hD : w D = 4) (hT : w T = 3) (hU : w U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hcanonical : ∀ v, G.Reachable C v → w v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → w v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → w v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → w v = 2)
    (hUsingle : ∀ v, G.Reachable U v → v ≠ U → w v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → w v = 2)
    (hvolume : 0 < -2 + dotProduct q a)
    (hbudget : -2 + dotProduct q a ≤ 1 - dotProduct p a)
    (hprojection : (-2 + dotProduct q a) * (dotProduct p (A⁻¹ *ᵥ p) - 1) =
      (1 - dotProduct p a)^2)
    (hneighbors : G.neighborFinset B = {M₀}) :
    let fixed : Finset V := {C, B, M₀, D, T, U}
    let Z := G.induce {v | v ∉ fixed}
    fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
      (∀ v : {v | v ∉ fixed}, w v.val = 2) ∧
      Z.edgeFinset.card = G.edgeFinset.card - 1 ∧ FiveVertexForestShape Z := by
  subst A
  subst q
  subst p
  obtain ⟨M, _, hBM, _, _, _, _, _, _, _, _, _, _, hremaining⟩ :=
    familyE_complete_forest G w a C B D T U hcard hA hG hrow hedges
      hB hD hT hU hTB hTD hUB hUD hTU hcanonical hBsingle hDsingle hTsingle hUsingle
      hother hvolume hbudget hprojection
  have hM : M = M₀ := by
    have hm := (G.mem_neighborFinset B M).mpr hBM
    rwa [hneighbors, Finset.mem_singleton] at hm
  subst M
  exact hremaining

/-- Each actual graph instantiates the complete ambient family-E theorem,
including all source row, positivity, projection, separation and cardinality
hypotheses. The resulting leftover classification concerns its actual induced
five-vertex complement. -/
theorem source_classification_witness (row : Fin 4) :
    let fixed : Finset (Fin 11) := {0, 1, 2, 3, 4, 5}
    let Z := (graph row).induce {v | v ∉ fixed}
    fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
      (∀ v : {v | v ∉ fixed}, weight v.val = 2) ∧
      Z.edgeFinset.card = (graph row).edgeFinset.card - 1 ∧ FiveVertexForestShape Z := by
  classical
  exact complete_forest_remaining_of_matrix_eq
      (graph row) weight canonicalCoeff 0 1 2 3 4 5
      (gram row) canonicalSource marked rfl rfl rfl
      (by decide) (gram_isUnit row) (graph_isAcyclic row) (canonical_row row)
      (edge_card_le_three row)
      (by simp only [weight, Fin.ext_iff, Fin.coe_ofNat_eq_mod]; norm_num)
      (by simp only [weight, Fin.ext_iff, Fin.coe_ofNat_eq_mod]; norm_num)
      (by simp only [weight, Fin.ext_iff, Fin.coe_ofNat_eq_mod]; norm_num)
      (by simp only [weight, Fin.ext_iff, Fin.coe_ofNat_eq_mod]; norm_num)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (canonical_component row) (core_single_source row)
      (isolated_single_source row 3 (by simp))
      (isolated_single_source row 4 (by simp))
      (isolated_single_source row 5 (by simp))
      weight_other (positive_volume_budget row).1 (positive_volume_budget row).2
      (projection_identity row) (core_neighbors row).1

end KltDP.LinearAlgebra.FamilyENonvacuity
