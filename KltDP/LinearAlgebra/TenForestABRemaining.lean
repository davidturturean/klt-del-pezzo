import KltDP.Manuscript.S09.TenForests
import KltDP.LinearAlgebra.TenForestFixedBlocks
import KltDP.LinearAlgebra.TenForestRowUniqueness

/-!
# Actual remaining matrices for the labelled A1, A2 and B rows

Each adapter consumes one actual row produced by the forest classifier.
The A1 and B complements use their proved cardinality and ambient isolation.
For A2 the full edge set and its disjoint second edge prove the closed first
edge; the actual fixed-block factor then determines the complement matrix.
The B conclusion retains the very same middle vertex and all its graph
shape fields alongside the determinant of that vertex's actual complement.

Reuse: `canonical_empty_det` and `familyA_fixed_det_factor`
provide all determinant calculations. Pinned/current official Mathlib's
finite-set membership, induced graph and symmetric edge-pair APIs are used
only for the local closed-edge adapter. These are the same Apache-2.0 APIs
inspected for `TenForestFixedBlocks` and `TenRowNodeSelections`; no new
foundation, library port, dependency update or resource option is needed.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem isolated_complement_det_nat
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (fixed : Finset V) (n : ℕ)
    (hcard : (Finset.univ \ fixed).card = n)
    (hremaining : ∀ v ∈ Finset.univ \ fixed, weight v = 2 ∧ ∀ u, ¬ G.Adj v u) :
    (graphWeightMatrix (G.induce {v | v ∉ fixed})
      (fun v => (weight v.val : ℚ))).det = 2 ^ n := by
  classical
  let S : Finset V := Finset.univ \ fixed
  have hr : ∀ v : {v | v ∉ fixed},
      (weight v.val : ℚ) = 2 ∧ ∀ u, ¬ G.Adj v.val u := by
    intro v
    obtain ⟨hw, hi⟩ := hremaining v.val
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v.val, v.property⟩)
    exact ⟨by simp only [hw, Nat.cast_ofNat], hi⟩
  have hweights : (fun v : {v | v ∉ fixed} => (weight v.val : ℚ)) =
      fun _ => (2 : ℚ) := funext (fun v => (hr v).1)
  have hgraph : G.induce {v | v ∉ fixed} = ⊥ := by
    ext v u
    change G.Adj v.val u.val ↔ False
    exact iff_false_intro ((hr v).2 u.val)
  have hedges : (G.induce {v | v ∉ fixed}).edgeFinset = ∅ :=
    (SimpleGraph.edgeFinset_inj.mpr hgraph).trans SimpleGraph.edgeFinset_bot
  have hcount : Fintype.card {v | v ∉ fixed} = n := by
    let e : {v | v ∉ fixed} ≃ (S : Set V) :=
      Equiv.subtypeEquivRight (fun v => by simp [S])
    exact (Fintype.card_congr e).trans ((Fintype.card_coe S).trans hcard)
  rw [hweights]
  exact (canonical_empty_det (G.induce {v | v ∉ fixed}) hedges).trans
    (congrArg (fun m : ℕ => (2 : ℚ) ^ m) hcount)

/-- The actual six isolated remaining vertices in A1 give determinant 64. -/
theorem tenForest_a1_remaining_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D T : V) (hcase : TenForestABCase .a1 G weight coeff C B D T) :
    (graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
      (fun v => (weight v.val : ℚ))).det = 64 := by
  obtain ⟨_, hc, hr, _, _, _, _, _⟩ := hcase
  exact (isolated_complement_det_nat G weight {C, T, B, D} 6 hc hr).trans (by norm_num)

/-- The actual closed first edge of A2 contributes 45; the full actual
determinant 2160 therefore gives remaining determinant 48. -/
theorem tenForest_a2_remaining_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D T : V)
    (hC : weight C = 2) (hT : weight T = 3)
    (hB : weight B = 3) (hD : weight D = 3) (hBD : B ≠ D)
    (hBiso : ∀ v, ¬ G.Adj B v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hcase : TenForestABCase .a2 G weight coeff C B D T) :
    (graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
      (fun v => (weight v.val : ℚ))).det = 48 := by
  classical
  obtain ⟨u, v, _, hu, hv, _, _, he, _, _, _, _, _, ha, _⟩ := hcase
  have hu' : u ≠ C ∧ u ≠ T ∧ u ≠ B ∧ u ≠ D := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hu
  have hv' : v ≠ C ∧ v ≠ T ∧ v ≠ B ∧ v ≠ D := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hv
  have hadj (x y : V) : G.Adj x y ↔
      ((x = C ∧ y = T) ∨ (x = T ∧ y = C)) ∨
      ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
    calc
      G.Adj x y ↔ s(x, y) ∈ G.edgeFinset := by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      _ ↔ _ := by rw [he]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  have hCT : G.Adj C T := (hadj C T).mpr (Or.inl (Or.inl ⟨rfl, rfl⟩))
  have hnC : G.neighborFinset C = {T} := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, hadj, hCT.ne,
      Ne.symm hu'.1, Ne.symm hv'.1]
  have hnT : G.neighborFinset T = {C} := by
    ext x
    simp [SimpleGraph.mem_neighborFinset, hadj, Ne.symm hCT.ne,
      Ne.symm hu'.2.1, Ne.symm hv'.2.1]
  have hf := familyA_fixed_det_factor G weight C T B D hC hT hB hD hBD
    hCT hnC hnT hBiso hDiso
  change (graphWeightMatrix G (fun i => (weight i : ℚ))).det = 2160 at ha
  linarith only [hf, ha]

/-- B retains the same actual middle vertex, full edge set and isolated
complement from its row, and that complement's actual determinant is 32. -/
theorem tenForest_b_remaining_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D T : V) (hcase : TenForestABCase .b G weight coeff C B D T) :
    ∃ M, weight M = 2 ∧ G.Adj C M ∧ G.Adj M T ∧
      G.edgeFinset = {s(C, M), s(M, T)} ∧
      (Finset.univ \ ({C, M, T, B, D} : Finset V)).card = 5 ∧
      (∀ v ∈ Finset.univ \ ({C, M, T, B, D} : Finset V),
        weight v = 2 ∧ ∀ u, ¬ G.Adj v u) ∧
      (graphWeightMatrix (G.induce {v | v ∉ ({C, M, T, B, D} : Finset V)})
        (fun v => (weight v.val : ℚ))).det = 32 := by
  obtain ⟨M, hM, hCM, hMT, he, hc, hr, _, _, _, _, _⟩ := hcase
  refine ⟨M, hM, hCM, hMT, he, hc, hr, ?_⟩
  exact (isolated_complement_det_nat G weight {C, M, T, B, D} 5 hc hr).trans (by norm_num)

end KltDP.LinearAlgebra
