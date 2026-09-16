import KltDP.LinearAlgebra.FamilyDAllocation
import KltDP.LinearAlgebra.FamilyDDeterminants

/-!
# Concrete algebraic witnesses for the two family-D completions

Both graphs have vertex type `Fin 10`. The closed canonical edge is 0--1,
the four isolated weight-three vertices are 2, 3, 4, 5, and the optional
second canonical edge is 6--7. The marked vertices are 0, 2, 3.

The exceptional determinants are instantiated from the actual graph theorems,
and their nonvanishing proves invertibility. Explicit vector solutions of
the full row equations are identified with the actual inverse images.
The allocation theorem is instantiated as well, so these are witnesses for
its hypotheses, not merely numeric determinant checks.

Scope: this file supplies graph, weight, unit and inverse-data nonvacuity
for the family-D algebraic adapters. It does not construct a surface or a
Picard-lattice embedding, and it does not claim a full geometric occurrence
or a positive-definiteness/nonvacuity audit for the entire manuscript theorem.

Reuse: pinned and current Mathlib's graph construction and nonsingular-inverse
APIs were checked. `SimpleGraph.fromRel` constructs the actual graph and
`Matrix.inv_mulVec_eq_vec` identifies the already checked row solutions;
`bordered_det_of_ten_vertices` supplies the sign-free Schur formula. The
determinant adapters use equality transport with an abstract vertex type;
no additional foundational result or source port is needed.
-/

namespace KltDP.LinearAlgebra.FamilyDNonvacuity

open Matrix SimpleGraph
open scoped BigOperators

/-- `false` is D1; `true` adds the second canonical edge and gives D2. -/
def graph (secondEdge : Bool) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun i j =>
    (i = 0 ∧ j = 1) ∨ (secondEdge = true ∧ i = 6 ∧ j = 7))

instance graphDecidable (secondEdge : Bool) : DecidableRel (graph secondEdge).Adj := by
  intro i j
  change Decidable (i ≠ j ∧
    (((i = 0 ∧ j = 1) ∨ (secondEdge = true ∧ i = 6 ∧ j = 7)) ∨
      ((j = 0 ∧ i = 1) ∨ (secondEdge = true ∧ j = 6 ∧ i = 7))))
  infer_instance

/-- The actual four higher-weight vertices. -/
def heavyVertices : Finset (Fin 10) := {2, 3, 4, 5}

/-- Every vertex outside the four specified indices has weight two. -/
def weight (i : Fin 10) : ℕ := if i ∈ heavyVertices then 3 else 2

/-- The actual rational exceptional matrix of the constructed graph. -/
def gram (secondEdge : Bool) : Matrix (Fin 10) (Fin 10) ℚ :=
  graphWeightMatrix (graph secondEdge) (fun i => (weight i : ℚ))

/-- The actual marked source, at C=0, B=2 and D=3. -/
def marked : Fin 10 → ℚ := threeMarkedSource 0 2 3

/-- The actual diagonal-minus-two source. -/
def canonicalSource (i : Fin 10) : ℚ := (weight i : ℚ) - 2

/-- An explicit solution for the canonical source. -/
def canonicalCoeff (i : Fin 10) : ℚ := if i ∈ heavyVertices then 1 / 3 else 0

/-- An explicit solution for the marked source. -/
def green (i : Fin 10) : ℚ :=
  if i = 0 then 2 / 3 else if i = 1 ∨ i = 2 ∨ i = 3 then 1 / 3 else 0

theorem weight_values :
    weight 0 = 2 ∧ weight 1 = 2 ∧ weight 2 = 3 ∧ weight 3 = 3 ∧
      weight 4 = 3 ∧ weight 5 = 3 := by
  decide

theorem weight_other (i : Fin 10) (hiB : i ≠ 2) (hiD : i ≠ 3)
    (hiT : i ≠ 4) (hiU : i ≠ 5) : weight i = 2 := by
  simp [weight, heavyVertices, hiB, hiD, hiT, hiU]

theorem canonical_adj (secondEdge : Bool) : (graph secondEdge).Adj 0 1 := by
  simp [graph]

/-- A symbolic adjacency description with the loop guard discharged by
actual distinct coordinates. This keeps subsequent finite checks small. -/
theorem graph_adj_iff (secondEdge : Bool) (i j : Fin 10) :
    (graph secondEdge).Adj i j ↔
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (secondEdge = true ∧ ((i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6))) := by
  change (i ≠ j ∧
    (((i = 0 ∧ j = 1) ∨ (secondEdge = true ∧ i = 6 ∧ j = 7)) ∨
      ((j = 0 ∧ i = 1) ∨ (secondEdge = true ∧ j = 6 ∧ i = 7)))) ↔ _
  constructor
  · tauto
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, h⟩
      · decide
      · decide
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    exact ⟨hne, by tauto⟩

theorem graph_edgeFinset (secondEdge : Bool) :
    (graph secondEdge).edgeFinset =
      if secondEdge then {s((0 : Fin 10), 1), s((6 : Fin 10), 7)} else {s((0 : Fin 10), 1)} := by
  cases secondEdge <;> apply Finset.ext
  all_goals
    intro e
    refine Sym2.inductionOn e ?_
    intro i j
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graph_adj_iff,
      Sym2.eq_iff] <;> tauto

theorem edge_card_le_two (secondEdge : Bool) : (graph secondEdge).edgeFinset.card ≤ 2 := by
  rw [graph_edgeFinset]
  cases secondEdge
  · simp
  · exact Finset.card_le_two

theorem canonical_neighbors (secondEdge : Bool) :
    (graph secondEdge).neighborFinset 0 = {1} ∧
      (graph secondEdge).neighborFinset 1 = {0} := by
  constructor <;> ext i <;>
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton,
      graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

theorem heavy_isolated (secondEdge : Bool) (i : Fin 10) (hi : i ∈ heavyVertices) :
    ∀ j, ¬ (graph secondEdge).Adj i j := by
  intro j
  simp only [heavyVertices, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp only [graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod] <;> norm_num

/-- Transport a determinant along matrix equality before specializing the
index type, keeping the kernel comparison outside the determinant. -/
private theorem det_eq_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℚ) (hAB : A = B) (d : ℚ) (hB : B.det = d) : A.det = d :=
  (congrArg Matrix.det hAB).trans hB

/-- Keep both the graph determinant application and its equality transport
abstract until the completed determinant theorem is specialized. -/
private theorem familyD1_det_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ)
    (A : Matrix V V ℚ) (hA : A = graphWeightMatrix G (fun i => (weight i : ℚ)))
    (C M B D T U : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hedges : G.edgeFinset = {s(C, M)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2) :
    A.det = 3888 := by
  have hd := familyD1_exceptional_det (𝕜 := ℚ) G weight C M B D T U
    hcard hC hM hB hD hT hU hBD hTB hTD hUB hUD hTU hCM hedges hother
  exact det_eq_of_matrix_eq A (graphWeightMatrix G (fun i => (weight i : ℚ))) hA 3888 hd

/-- Keep both the graph determinant application and its equality transport
abstract until the completed determinant theorem is specialized. -/
private theorem familyD2_det_of_matrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ)
    (A : Matrix V V ℚ) (hA : A = graphWeightMatrix G (fun i => (weight i : ℚ)))
    (C M B D T U x y : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hxy : x ≠ y)
    (hx : x ∉ ({C, M, B, D, T, U} : Finset V))
    (hy : y ∉ ({C, M, B, D, T, U} : Finset V))
    (hx2 : weight x = 2) (hy2 : weight y = 2)
    (hedges : G.edgeFinset = {s(C, M), s(x, y)})
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2) :
    A.det = 2916 := by
  have hd := familyD2_exceptional_det (𝕜 := ℚ) G weight C M B D T U x y
    hcard hC hM hB hD hT hU hBD hTB hTD hUB hUD hTU
    hCM hxy hx hy hx2 hy2 hedges hother
  exact det_eq_of_matrix_eq A (graphWeightMatrix G (fun i => (weight i : ℚ))) hA 2916 hd

/-- The exceptional determinants follow from the frozen graph determinant
theorems, without evaluating a ten-by-ten determinant by enumeration. -/
theorem exceptional_det (secondEdge : Bool) :
    (gram secondEdge).det = if secondEdge then 2916 else 3888 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := weight_values
  cases secondEdge
  · exact familyD1_det_of_matrix_eq (graph false) weight (gram false) rfl 0 1 2 3 4 5
      (by decide) h0 h1 h2 h3 h4 h5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (canonical_adj false) (graph_edgeFinset false) weight_other
  · exact familyD2_det_of_matrix_eq (graph true) weight (gram true) rfl 0 1 2 3 4 5 6 7
      (by decide) h0 h1 h2 h3 h4 h5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (canonical_adj true) (by decide) (by decide) (by decide) (by decide) (by decide)
      (graph_edgeFinset true) weight_other

/-- Actual matrix invertibility, derived from the preceding determinant. -/
theorem gram_isUnit (secondEdge : Bool) : IsUnit (gram secondEdge) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [exceptional_det]
  cases secondEdge <;> norm_num

set_option maxHeartbeats 2000000 in
theorem canonical_row (secondEdge : Bool) :
    gram secondEdge *ᵥ canonicalCoeff = canonicalSource := by
  ext i
  fin_cases i <;> cases secondEdge <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.sum_univ_zero, canonicalCoeff, canonicalSource,
      weight, heavyVertices, Finset.mem_insert, Finset.mem_singleton, graph_adj_iff,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_succ, Fin.val_mk, Nat.cast_ofNat] <;> norm_num

set_option maxHeartbeats 2000000 in
theorem green_row (secondEdge : Bool) : gram secondEdge *ᵥ green = marked := by
  ext i
  fin_cases i <;> cases secondEdge <;>
    simp only [gram, graphWeightMatrix_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.sum_univ_zero, green, marked, threeMarkedSource,
      Pi.add_apply, Pi.single_apply, weight, heavyVertices, Finset.mem_insert,
      Finset.mem_singleton, graph_adj_iff, Fin.ext_iff, Fin.coe_ofNat_eq_mod,
      Fin.val_succ, Fin.val_mk, Nat.cast_ofNat] <;> norm_num

theorem inverse_canonical (secondEdge : Bool) :
    (gram secondEdge)⁻¹ *ᵥ canonicalSource = canonicalCoeff := by
  letI : Invertible (gram secondEdge) := (gram_isUnit secondEdge).invertible
  exact Matrix.inv_mulVec_eq_vec (canonical_row secondEdge).symm

theorem inverse_green (secondEdge : Bool) : (gram secondEdge)⁻¹ *ᵥ marked = green := by
  letI : Invertible (gram secondEdge) := (gram_isUnit secondEdge).invertible
  exact Matrix.inv_mulVec_eq_vec (green_row secondEdge).symm

theorem canonical_bounds (secondEdge : Bool) :
    ∀ i, 0 ≤ ((gram secondEdge)⁻¹ *ᵥ canonicalSource) i ∧
      ((gram secondEdge)⁻¹ *ᵥ canonicalSource) i < 1 := by
  simp only [inverse_canonical]
  intro i
  by_cases hi : i ∈ heavyVertices <;> norm_num [canonicalCoeff, hi]

/-- Exact values of the actual inverse-defined length, square and energy. -/
theorem scalar_values (secondEdge : Bool) :
    1 - dotProduct marked ((gram secondEdge)⁻¹ *ᵥ canonicalSource) = 1 / 3 ∧
      -1 + dotProduct canonicalSource ((gram secondEdge)⁻¹ *ᵥ canonicalSource) = 1 / 3 ∧
      dotProduct marked ((gram secondEdge)⁻¹ *ᵥ marked) = 4 / 3 := by
  simp only [inverse_canonical, inverse_green]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    marked, threeMarkedSource, Pi.add_apply, Pi.single_apply, canonicalCoeff,
    canonicalSource, green, weight, heavyVertices, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_succ, Fin.val_mk, Nat.cast_ofNat] <;> norm_num

theorem projection_identity (secondEdge : Bool) :
    (-1 + dotProduct canonicalSource ((gram secondEdge)⁻¹ *ᵥ canonicalSource)) *
        (dotProduct marked ((gram secondEdge)⁻¹ *ᵥ marked) - 1) =
      (1 - dotProduct marked ((gram secondEdge)⁻¹ *ᵥ canonicalSource)) ^ 2 := by
  obtain ⟨hl, hv, hg⟩ := scalar_values secondEdge
  rw [hl, hv, hg]
  norm_num

/-- Keep the finite-dimensional Schur calculation abstract, so its proof
does not unfold the explicit graph or its nonsingular inverse. -/
private theorem ten_bordered_det_of_values
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℚ) (p : V → ℚ) (hA : IsUnit A) (hcard : Fintype.card V = 10)
    (d : ℚ) (hdet : A.det = d) (hg : dotProduct p (A⁻¹ *ᵥ p) = 4 / 3) :
    (borderedGram A p (-1)).det = d * (1 / 3) := by
  refine (bordered_det_of_ten_vertices A p hA hcard).trans ?_
  rw [hdet, hg]
  norm_num

/-- The full bordered determinants for these actual inverse-data witnesses. -/
theorem bordered_det (secondEdge : Bool) :
    (borderedGram (gram secondEdge) marked (-1)).det = if secondEdge then 972 else 1296 := by
  refine (ten_bordered_det_of_values (gram secondEdge) marked (gram_isUnit secondEdge)
    (by decide) (if secondEdge then 2916 else 3888)
    (exceptional_det secondEdge) (scalar_values secondEdge).2.2).trans ?_
  cases secondEdge <;> norm_num

/-- Direct instantiation of the frozen allocation theorem at the two actual
graphs, including weights and isolation of every leftover vertex. -/
theorem allocation (secondEdge : Bool) :
    ((graph secondEdge).edgeFinset = {s((0 : Fin 10), 1)} ∧
      (Finset.univ \ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10))).card = 4 ∧
      ∀ v ∈ Finset.univ \ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)),
        weight v = 2 ∧ ∀ w, ¬ (graph secondEdge).Adj v w) ∨
    (∃ x y, (graph secondEdge).Adj x y ∧
      x ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) ∧
      y ∉ ({0, 1, 2, 3, 4, 5} : Finset (Fin 10)) ∧ weight x = 2 ∧ weight y = 2 ∧
      (graph secondEdge).edgeFinset = {s((0 : Fin 10), 1), s(x, y)} ∧
      (Finset.univ \ ({x, y, 0, 1, 2, 3, 4, 5} : Finset (Fin 10))).card = 2 ∧
      ∀ v ∈ Finset.univ \ ({x, y, 0, 1, 2, 3, 4, 5} : Finset (Fin 10)),
        weight v = 2 ∧ ∀ w, ¬ (graph secondEdge).Adj v w) := by
  apply familyD_remaining_vertices (graph secondEdge) weight 0 1 2 3 4 5
  all_goals first
    | exact canonical_adj secondEdge
    | exact (canonical_neighbors secondEdge).1
    | exact (canonical_neighbors secondEdge).2
    | exact heavy_isolated secondEdge 2 (by decide)
    | exact heavy_isolated secondEdge 3 (by decide)
    | exact heavy_isolated secondEdge 4 (by decide)
    | exact heavy_isolated secondEdge 5 (by decide)
    | exact edge_card_le_two secondEdge
    | exact weight_other
    | decide

end KltDP.LinearAlgebra.FamilyDNonvacuity
