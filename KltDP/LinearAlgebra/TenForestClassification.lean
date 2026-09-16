import KltDP.LinearAlgebra.CandidateForestSeparation
import KltDP.LinearAlgebra.ABSourceReduction
import KltDP.LinearAlgebra.FamilyCGreenEnergy
import KltDP.LinearAlgebra.FamilyDSourceShapes
import KltDP.LinearAlgebra.FamilyESourceRows
import KltDP.LinearAlgebra.NoExtraSourceExclusion
import KltDP.LinearAlgebra.BetaFiveComponentReduction

/-!
# The actual candidate-forest case split

The additional weight-three vertices are extracted from the actual finite
vertex set. No extra vertices, component types or candidate rows are given
as an assumed exhaustive list. The source length and volume exclude an
empty extra set, and its actual cardinality bound leaves one or two extras.

Reuse: pinned Mathlib Finset cardinality and membership theorems, the
existing actual-graph family reductions and inverse-source separation.
The current official graph connectivity API and the independently inspected
PositiveDefiniteTreeLattice sources require no port for this composition.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual extra weight-three vertices, excluding the three marked
vertices exactly as in the manuscript's cardinality hypothesis. -/
def candidateExtraVertices (weight : V → ℕ) (C B D : V) : Finset V :=
  Finset.univ.filter (fun v => v ≠ C ∧ v ≠ B ∧ v ≠ D ∧ weight v = 3)

@[simp]
theorem mem_candidateExtraVertices (weight : V → ℕ) (C B D v : V) :
    v ∈ candidateExtraVertices weight C B D ↔
      v ≠ C ∧ v ≠ B ∧ v ≠ D ∧ weight v = 3 := by
  simp [candidateExtraVertices]

/-- The actual cardinality bound gives an exhaustive empty/singleton/pair
description of the extra set, including distinctness of the two vertices. -/
theorem candidate_extra_vertices_cases (weight : V → ℕ) (C B D : V)
    (hcard : (candidateExtraVertices weight C B D).card ≤ 2) :
    candidateExtraVertices weight C B D = ∅ ∨
    (∃ T, T ≠ C ∧ T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
      candidateExtraVertices weight C B D = {T}) ∨
    (∃ T U, T ≠ C ∧ T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
      U ≠ C ∧ U ≠ B ∧ U ≠ D ∧ weight U = 3 ∧ T ≠ U ∧
      candidateExtraVertices weight C B D = {T, U}) := by
  rcases (candidateExtraVertices weight C B D).eq_empty_or_nonempty with hempty | ⟨T, hT⟩
  · exact Or.inl hempty
  obtain ⟨hTC, hTB, hTD, hTweight⟩ := (mem_candidateExtraVertices weight C B D T).mp hT
  rcases eq_singleton_or_pair_of_mem_card_le_two
      (candidateExtraVertices weight C B D) T hT hcard with hsingle | ⟨U, hUT, hpair⟩
  · exact Or.inr (Or.inl ⟨T, hTC, hTB, hTD, hTweight, hsingle⟩)
  · have hU : U ∈ candidateExtraVertices weight C B D := by rw [hpair]; simp
    obtain ⟨hUC, hUB, hUD, hUweight⟩ := (mem_candidateExtraVertices weight C B D U).mp hU
    exact Or.inr (Or.inr
      ⟨T, U, hTC, hTB, hTD, hTweight, hUC, hUB, hUD, hUweight, Ne.symm hUT, hpair⟩)

/-- A vertex outside the two core sources and the actual extra set has
weight two. C is handled by its specified weight, rather than by placing
it among the unmarked vertices. -/
theorem candidate_weight_two_off_extras (weight : V → ℕ) (C B D : V)
    (hC : weight C = 2)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (v : V) (hvB : v ≠ B) (hvD : v ≠ D)
    (hvextra : v ∉ candidateExtraVertices weight C B D) : weight v = 2 := by
  by_cases hvC : v = C
  · simpa only [hvC] using hC
  rcases hother v hvC hvB hvD with hv | hv
  · exact hv
  · exact (hvextra ((mem_candidateExtraVertices weight C B D v).mpr
      ⟨hvC, hvB, hvD, hv⟩)).elim

/-- Positive actual source length and volume rule out the empty branch.
The one/two-extra descriptions and all canonical complementary weights are
derived from the actual extra-set cardinality, not supplied as premises. -/
theorem candidate_positive_extra_cases (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ) (hβ : 3 ≤ β)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β) (hBD : B ≠ D)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hcard : (candidateExtraVertices weight C B D).card ≤ 2)
    (hcoeff : ∀ v, 0 ≤ coeff v)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) :
    (∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
      candidateExtraVertices weight C B D = {T} ∧
      ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2) ∨
    (∃ T U, T ≠ B ∧ T ≠ D ∧ U ≠ B ∧ U ≠ D ∧ T ≠ U ∧
      weight T = 3 ∧ weight U = 3 ∧
      candidateExtraVertices weight C B D = {T, U} ∧
      ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2) := by
  rcases candidate_extra_vertices_cases weight C B D hcard with
    hempty | ⟨T, _, hTB, hTD, hT, hsingle⟩ |
      ⟨T, U, _, hTB, hTD, hT, _, hUB, hUD, hU, hTU, hpair⟩
  · have hcanonical : ∀ v, v ≠ B → v ≠ D → (weight v : ℚ) = 2 := by
      intro v hvB hvD
      have hw := candidate_weight_two_off_extras weight C B D hC hother v hvB hvD
        (by rw [hempty]; exact Finset.not_mem_empty v)
      exact_mod_cast hw
    exact (no_extra_source_impossible (fun v => (weight v : ℚ)) coeff C B D (β : ℚ)
      (by exact_mod_cast hβ)
      (by change (weight B : ℚ) = 3; simp only [hB, Nat.cast_ofNat])
      (by change (weight D : ℚ) = (β : ℚ); rw [hD])
      hBD hcanonical hcoeff hlength hvolume).elim
  · refine Or.inl ⟨T, hTB, hTD, hT, hsingle, ?_⟩
    intro v hvB hvD hvT
    exact candidate_weight_two_off_extras weight C B D hC hother v hvB hvD
      (by rw [hsingle]; simpa only [Finset.mem_singleton] using hvT)
  · refine Or.inr ⟨T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, hpair, ?_⟩
    intro v hvB hvD hvT hvU
    exact candidate_weight_two_off_extras weight C B D hC hother v hvB hvD
      (by rw [hpair]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or];
          exact ⟨hvT, hvU⟩)


/-- Conclusion-only actual graph and invariant data, matching the source branch. -/
def ABForestRows (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D T : V) : Prop :=
  let A := graphWeightMatrix G (fun i => (weight i : ℚ))
  let p := threeMarkedSource C B D
  let ell := 1 - dotProduct p coeff
  let vol := -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff
  let green := dotProduct p (A⁻¹ *ᵥ p)
  (∀ u, ¬ G.Adj B u) ∧ (∀ u, ¬ G.Adj D u) ∧
  ((G.edgeFinset = {s(C, T)} ∧
    (Finset.univ \ ({C, T, B, D} : Finset V)).card = 6 ∧
    (∀ v ∈ Finset.univ \ ({C, T, B, D} : Finset V),
      weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
    ell = 2 / 15 ∧ vol = 1 / 15 ∧ green = 19 / 15 ∧
    A.det = 2880 ∧ (borderedGram A p (-1)).det = 768) ∨
  (∃ u v, u ≠ v ∧ u ∉ ({C, T, B, D} : Finset V) ∧
    v ∉ ({C, T, B, D} : Finset V) ∧ weight u = 2 ∧ weight v = 2 ∧
    G.edgeFinset = {s(C, T), s(u, v)} ∧
    (Finset.univ \ ({u, v, C, T, B, D} : Finset V)).card = 4 ∧
    (∀ w ∈ Finset.univ \ ({u, v, C, T, B, D} : Finset V),
      weight w = 2 ∧ ∀ z, ¬ G.Adj w z) ∧
    ell = 2 / 15 ∧ vol = 1 / 15 ∧ green = 19 / 15 ∧
    A.det = 2160 ∧ (borderedGram A p (-1)).det = 576) ∨
  (∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
    G.edgeFinset = {s(C, M), s(M, T)} ∧
    (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
    (∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
      weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
    ell = 4 / 21 ∧ vol = 2 / 21 ∧ green = 29 / 21 ∧
    A.det = 2016 ∧ (borderedGram A p (-1)).det = 768))


/-- Conclusion-only actual graph and invariant data, matching the source branch. -/
def CForestRow (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → ℚ) (C B D T : V) : Prop :=
  ∃ L M, weight L = 2 ∧ weight M = 2 ∧
    (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj T v) ∧
    G.Adj B L ∧ G.Adj D M ∧
    G.neighborFinset B = {L} ∧ G.neighborFinset L = {B} ∧
    G.neighborFinset D = {M} ∧ G.neighborFinset M = {D} ∧
    G.edgeFinset = {s(B, L), s(D, M)} ∧
    (Finset.univ \ ({C, B, L, D, M, T} : Finset V)).card = 4 ∧
    (∀ v ∈ Finset.univ \ ({C, B, L, D, M, T} : Finset V),
      weight v = 2 ∧ ∀ w, ¬ G.Adj v w) ∧
    1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 5 ∧
    -1 + dotProduct (fun i => weight i - 2) coeff = 2 / 15 ∧
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 13 / 10 ∧
    (graphWeightMatrix G weight).det = 2400 ∧
    (borderedGram (graphWeightMatrix G weight)
      (threeMarkedSource C B D) (-1)).det = 720


/-- Conclusion-only actual graph and invariant data, matching the source branch. -/
def DForestRows (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D T U : V) : Prop :=
  ∃ M, G.Adj C M ∧ weight C = 2 ∧ weight M = 2 ∧
    G.neighborFinset C = {M} ∧ G.neighborFinset M = {C} ∧
    (∀ i, G.Reachable C i ↔ i = C ∨ i = M) ∧
    (∀ i, ¬ G.Adj B i) ∧ (∀ i, ¬ G.Adj D i) ∧
    (∀ i, ¬ G.Adj T i) ∧ (∀ i, ¬ G.Adj U i) ∧
    1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 3 ∧
    -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff = 1 / 3 ∧
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
        threeMarkedSource C B D) = 4 / 3 ∧
    ((G.edgeFinset = {s(C, M)} ∧
      (Finset.univ \ ({C, M, B, D, T, U} : Finset V)).card = 4 ∧
      (∀ i ∈ Finset.univ \ ({C, M, B, D, T, U} : Finset V),
        weight i = 2 ∧ ∀ j, ¬ G.Adj i j) ∧
      (graphWeightMatrix G (fun i => (weight i : ℚ))).det = 3888 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
        (threeMarkedSource C B D) (-1)).det = 1296) ∨
    (∃ x y, G.Adj x y ∧ x ∉ ({C, M, B, D, T, U} : Finset V) ∧
      y ∉ ({C, M, B, D, T, U} : Finset V) ∧ weight x = 2 ∧ weight y = 2 ∧
      G.edgeFinset = {s(C, M), s(x, y)} ∧
      (Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V)).card = 2 ∧
      (∀ i ∈ Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V),
        weight i = 2 ∧ ∀ j, ¬ G.Adj i j) ∧
      (graphWeightMatrix G (fun i => (weight i : ℚ))).det = 2916 ∧
      (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
        (threeMarkedSource C B D) (-1)).det = 972))


/-- Conclusion-only actual graph and invariant data, matching the source branch. -/
def EForestRows (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight coeff : V → ℚ) (C B D T U : V) : Prop :=
  ∃ M, weight M = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
    G.neighborFinset M = {B} ∧
    (∀ v, G.Reachable B v ↔ v = B ∨ v = M) ∧
    (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj D v) ∧
    (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
    1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 10 ∧
    -2 + dotProduct (fun i => weight i - 2) coeff = 1 / 15 ∧
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 23 / 20 ∧
    (let fixed : Finset V := {C, B, M, D, T, U}
     let Z := G.induce {v | v ∉ fixed}
     fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
       (∀ v : {v | v ∉ fixed}, weight v.val = 2) ∧
       Z.edgeFinset.card = G.edgeFinset.card - 1 ∧ FiveVertexForestShapeDet Z
         (graphWeightMatrix G weight).det
         (borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1)).det)


/-- The ten actual graph rows, grouped as A1/A2/B, C, D1/D2 and E1--E4.
Every nested branch retains its graph witnesses, canonical isolated
leftovers, source scalar values and its own signed determinant pair.
This is solely an output predicate; it is not a source hypothesis. -/
def TenForestRows (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D : V) (β : ℕ) : Prop :=
  (β = 3 ∧ ∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
    ABForestRows G weight coeff C B D T) ∨
  (β = 3 ∧ ∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧
    CForestRow G (fun v => (weight v : ℚ)) coeff C B D T) ∨
  (β = 3 ∧ ∃ T U, T ≠ B ∧ T ≠ D ∧ U ≠ B ∧ U ≠ D ∧ T ≠ U ∧
    weight T = 3 ∧ weight U = 3 ∧ DForestRows G weight coeff C B D T U) ∨
  (β = 4 ∧ ∃ T U, T ≠ B ∧ T ≠ D ∧ U ≠ B ∧ U ≠ D ∧ T ≠ U ∧
    weight T = 3 ∧ weight U = 3 ∧
      EForestRows G (fun v => (weight v : ℚ)) coeff C B D T U)

/-- A bounded four-vertex specialization check, kept separate from the
source's full matrix and coefficient context. -/
private theorem finFour_pairwise_not_reachable
    (G : SimpleGraph V) (C B D T : V)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hCT : ¬ G.Reachable C T) (hBD : ¬ G.Reachable B D)
    (hBT : ¬ G.Reachable B T) (hDT : ¬ G.Reachable D T) :
    ∀ i j : Fin 4, i ≠ j →
      ¬ G.Reachable (![C, B, D, T] i) (![C, B, D, T] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
    first
    | exact (hij rfl).elim
    | exact hCB
    | exact hCD
    | exact hCT
    | exact hBD
    | exact hBT
    | exact hDT
    | exact fun h => hCB h.symm
    | exact fun h => hCD h.symm
    | exact fun h => hCT h.symm
    | exact fun h => hBD h.symm
    | exact fun h => hBT h.symm
    | exact fun h => hDT h.symm

set_option maxHeartbeats 2000000 in
/-- The ten candidate weighted forests from the original manuscript data.
The coefficient equality is exactly the manuscript's inverse definition;
the actual extra set is counted and split inside the proof. All component
conditions and graph rows are conclusions. The source's unused degree and
coefficient upper bounds are retained at this final entry point. -/
theorem ten_forest_classification
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5) (hcard : Fintype.card V = β + 7)
    (hG : G.IsAcyclic)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hextraCard : (candidateExtraVertices weight C B D).card ≤ 2)
    (hnadjCB : ¬ G.Adj C B) (hnadjCD : ¬ G.Adj C D) (_hnadjBD : ¬ G.Adj B D)
    (hseparate : ¬ G.Reachable B D)
    (_hdegreeC : G.degree C ≤ 1) (_hdegree : ∀ v, G.degree v ≤ 3)
    (hedges : G.edgeFinset.card ≤ β - 1)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2))
    (hcoeffBounds : ∀ v, 0 ≤ coeff v ∧ coeff v < 1)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff)
    (hbudget : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    TenForestRows G weight coeff C B D β := by
  classical
  let w : V → ℚ := fun v => weight v
  have hβlower : 3 ≤ β := by rcases hβ with h | h | h <;> omega
  have hweight : ∀ v, 2 ≤ weight v := by
    intro v
    by_cases hvC : v = C
    · simpa only [hvC, hC] using (le_refl (2 : ℕ))
    by_cases hvB : v = B
    · rw [hvB, hB]
      omega
    by_cases hvD : v = D
    · rw [hvD, hD]
      omega
    rcases hother v hvC hvB hvD with h | h <;> omega
  have hcoeff : ∀ v, 0 ≤ coeff v := fun v => (hcoeffBounds v).1
  have hBD : B ≠ D := by intro h; subst D; exact hseparate (.refl B)
  have hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff :=
    lt_of_lt_of_le hvolume hbudget
  have hrow := candidate_graph_source_row G weight coeff hA hsolve
  have hunit := isUnit_of_posDef hA
  obtain ⟨hsingle, hCB, hCD, _, htwo, hCcases⟩ :=
    candidate_forest_component_separation G weight coeff C B D β hβ hC hB hD hother
      hnadjCB hnadjCD hseparate hedges hA hsolve hcoeff hvolume hbudget hprojection
  have hBsingle := hsingle B (by omega)
  have hDsingle := hsingle D (by omega)
  have hsingleQ (root : V) (hr : 3 ≤ weight root) :
      ∀ v, G.Reachable root v → v ≠ root → w v = 2 := by
    intro v hv hne
    dsimp only [w]
    exact_mod_cast hsingle root hr v hv hne
  have hBsingleQ := hsingleQ B (by omega)
  have hDsingleQ := hsingleQ D (by omega)
  have hBq : w B = 3 := by dsimp only [w]; exact_mod_cast hB
  have hDq : w D = β := by dsimp only [w]; exact_mod_cast hD
  rcases candidate_positive_extra_cases weight coeff C B D β hβlower hC hB hD hBD
      hother hextraCard hcoeff hlength hvolume with
      ⟨T, hTB, hTD, hT, _, hrest⟩ |
      ⟨T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, _, hrest⟩
  · have hTsingle := hsingle T (by omega)
    have hTsingleQ := hsingleQ T (by omega)
    have hTq : w T = 3 := by dsimp only [w]; exact_mod_cast hT
    have hrestQ : ∀ v, v ≠ B → v ≠ D → v ≠ T → w v = 2 := by
      intro v hvB hvD hvT
      dsimp only [w]
      exact_mod_cast hrest v hvB hvD hvT
    by_cases hcanonical : ∀ v, G.Reachable C v → weight v = 2
    · have hcanonicalQ : ∀ v, G.Reachable C v → w v = 2 := by
        intro v hv
        dsimp only [w]
        exact_mod_cast hcanonical v hv
      rcases hβ with h3 | h4 | h5
      · have hCT : ¬ G.Reachable C T := by
          intro h
          have := hcanonical T h
          omega
        have hBT : ¬ G.Reachable B T := by
          intro h
          have := hBsingle T h hTB
          omega
        have hDT : ¬ G.Reachable D T := by
          intro h
          have := hDsingle T h hTD
          omega
        have hseparated : ∀ i j : Fin 4, i ≠ j →
            ¬ G.Reachable (![C, B, D, T] i) (![C, B, D, T] j) :=
          finFour_pairwise_not_reachable G C B D T hCB hCD hCT hseparate hBT hDT
        have hp3 :
            (-1 + dotProduct (fun v => w v - 2) coeff) *
              (dotProduct (threeMarkedSource C B D)
                ((graphWeightMatrix G w)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
              (1 - dotProduct (threeMarkedSource C B D) coeff)^2 := by
          simpa only [w, h3, Nat.cast_ofNat, show (2 : ℚ) - 3 = -1 by norm_num]
            using hprojection
        have hCrow : CForestRow G w coeff C B D T :=
          beta_three_one_extra_source_familyC G w coeff C B D T
            (by simpa only [h3] using hcard) hunit hG hrow hcanonicalQ hBq
            (by simpa only [h3, Nat.cast_ofNat] using hDq) hTq
            hBsingleQ hDsingleQ hTsingleQ hrestQ hseparated
            (by simpa only [h3] using hedges) hp3
        exact Or.inr (Or.inl ⟨h3, T, hTB, hTD, hT, hCrow⟩)
      · exact (beta_four_one_extra_forest_impossible G w coeff C B D T hunit hG hrow
          (by simpa only [h4] using hedges) hBq
          (by simpa only [h4, Nat.cast_ofNat] using hDq) hTq hTB hTD
          hcanonicalQ hBsingleQ hDsingleQ hTsingleQ hrestQ hlength
          (by simpa only [w, h4, Nat.cast_ofNat, show (2 : ℚ) - 4 = -2 by norm_num]
              using hvolume)).elim
      · exact (beta_five_one_extra_forest_impossible G w coeff C B D T hunit hG hrow
          hcoeff (by simpa only [h5] using hedges) hBq
          (by simpa only [h5, Nat.cast_ofNat] using hDq) hTq hTB hTD
          hcanonicalQ hBsingleQ hDsingleQ hTsingleQ hrestQ hlength
          (by simpa only [w, h5, Nat.cast_ofNat, show (2 : ℚ) - 5 = -3 by norm_num]
              using hvolume) hboundary).elim
    · rcases hCcases with hcan | ⟨h3, T', hT'B, hT'D, hT', hCT', _⟩
      · exact (hcanonical hcan).elim
      · have hT'T : T' = T := by
          by_contra hne
          have hw := hrest T' hT'B hT'D hne
          omega
        subst T'
        have hAB : ABForestRows G weight coeff C B D T :=
          beta_three_reachable_extra_source_rows G weight coeff C B D T
            (by simpa only [h3] using hcard) hweight hC hB
            (by simpa only [h3] using hD) hT hTB hTD hrest hseparate hCT'
            (by simpa only [h3] using hedges) hA hrow hcoeff hlength
            (by simpa only [h3, Nat.cast_ofNat, show (2 : ℚ) - 3 = -1 by norm_num]
                using hbudget)
        exact Or.inl ⟨h3, T, hTB, hTD, hT, hAB⟩
  · have hcanonical := htwo ⟨T, U, hTU, hTB, hTD, hUB, hUD, hT, hU⟩
    have hcanonicalQ : ∀ v, G.Reachable C v → w v = 2 := by
      intro v hv
      dsimp only [w]
      exact_mod_cast hcanonical v hv
    have hTsingle := hsingle T (by omega)
    have hUsingle := hsingle U (by omega)
    have hTsingleQ := hsingleQ T (by omega)
    have hUsingleQ := hsingleQ U (by omega)
    have hTq : w T = 3 := by dsimp only [w]; exact_mod_cast hT
    have hUq : w U = 3 := by dsimp only [w]; exact_mod_cast hU
    have hrestQ : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → w v = 2 := by
      intro v hvB hvD hvT hvU
      dsimp only [w]
      exact_mod_cast hrest v hvB hvD hvT hvU
    rcases hβ with h3 | h4 | h5
    · have hDrow : DForestRows G weight coeff C B D T U :=
        familyD_source_rows G weight coeff C B D T U
          (by simpa only [h3] using hcard) hG (by simpa only [h3] using hedges)
          hA hrow hB (by simpa only [h3] using hD) hT hU hTB hTD hUB hUD hTU
          hCB hCD hseparate hcanonical hBsingle hDsingle hTsingle hUsingle hrest
          (by simpa only [h3, Nat.cast_ofNat, show (2 : ℚ) - 3 = -1 by norm_num]
              using hbudget)
          (by simpa only [h3, Nat.cast_ofNat, show (2 : ℚ) - 3 = -1 by norm_num]
              using hprojection)
      exact Or.inr (Or.inr (Or.inl ⟨h3, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, hDrow⟩))
    · have hErow : EForestRows G w coeff C B D T U :=
        familyE_source_rows G w coeff C B D T U
          (by simpa only [h4] using hcard) hunit hG hrow
          (by simpa only [h4] using hedges) hBq
          (by simpa only [h4, Nat.cast_ofNat] using hDq) hTq hUq hTB hTD hUB hUD hTU
          hcanonicalQ hBsingleQ hDsingleQ hTsingleQ hUsingleQ hrestQ
          (by simpa only [w, h4, Nat.cast_ofNat, show (2 : ℚ) - 4 = -2 by norm_num]
              using hvolume)
          (by simpa only [w, h4, Nat.cast_ofNat, show (2 : ℚ) - 4 = -2 by norm_num]
              using hbudget)
          (by simpa only [w, h4, Nat.cast_ofNat, show (2 : ℚ) - 4 = -2 by norm_num]
              using hprojection)
      exact Or.inr (Or.inr (Or.inr ⟨h4, T, U, hTB, hTD, hUB, hUD, hTU, hT, hU, hErow⟩))
    · exact (beta_five_two_extra_forest_impossible G w coeff C B D T U hunit hG hrow
        hcoeff (by simpa only [h5] using hedges) hBq
        (by simpa only [h5, Nat.cast_ofNat] using hDq) hTq hUq hTB hTD hUB hUD hTU
        hcanonicalQ hBsingleQ hDsingleQ hTsingleQ hUsingleQ hrestQ hlength
        (by simpa only [w, h5, Nat.cast_ofNat, show (2 : ℚ) - 5 = -3 by norm_num]
            using hvolume) hboundary
        (by simpa only [w, h5, Nat.cast_ofNat, show (2 : ℚ) - 5 = -3 by norm_num]
            using hprojection)).elim

end KltDP.LinearAlgebra
