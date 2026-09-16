import KltDP.LinearAlgebra.FamilyEDeterminants

/-!
# Actual fixed blocks for the A and D forest families

The closed weighted edge and actual isolated higher-weight vertices form
an injectively indexed principal block. Its determinant is computed from
the entries and multiplied by the determinant of the actual induced
complement. The factors are 45 for A and 243 for D. Neither a block
determinant nor a description of the complement is an input.

Reuse: the proof follows `familyE_fixed_det_factor` and invokes its existing
`graph_det_eq_principal_mul_induced_complement` adapter. Pinned Mathlib's
`det_fromBlocks_zero₂₁`, `det_diagonal`, `det_fin_two`, and `Fin.prod_univ_succ`
supply all determinant arithmetic. Current official Apache-2.0 Mathlib
`LinearAlgebra/Matrix/Block.lean` and `Determinant/Basic.lean` were inspected
on 2026-09-06; the newer Lean 4.34.0-rc2 toolchain is not imported into the
Lean 4.19.0 project. No newer-library or graph-library port is needed.
The remaining local work is the actual vertex injection, closedness, and
entrywise identification of the two displayed small blocks.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual closed weight-two/weight-three edge and two distinct
isolated weight-three vertices contribute the factor 45. -/
theorem familyA_fixed_det_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (C T B D : V)
    (hC : weight C = 2) (hT : weight T = 3)
    (hB : weight B = 3) (hD : weight D = 3) (hBD : B ≠ D)
    (hCT : G.Adj C T) (hnC : G.neighborFinset C = {T})
    (hnT : G.neighborFinset T = {C})
    (hBiso : ∀ v, ¬ G.Adj B v) (hDiso : ∀ v, ¬ G.Adj D v) :
    (graphWeightMatrix G (fun v => (weight v : ℚ))).det = 45 *
      (graphWeightMatrix (G.induce {v | v ∉ ({C, T, B, D} : Finset V)})
        (fun v => (weight v.val : ℚ))).det := by
  classical
  have hCB : C ≠ B := by
    intro h
    have hw := congrArg weight h
    omega
  have hCD : C ≠ D := by
    intro h
    have hw := congrArg weight h
    omega
  have hTB : T ≠ B := by intro h; subst B; exact hBiso C hCT.symm
  have hTD : T ≠ D := by intro h; subst D; exact hDiso C hCT.symm
  let f : Fin 2 ⊕ Fin 2 → V := Sum.elim ![C, T] ![B, D]
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j
    all_goals
      simp only [f, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] at h
      first
      | rfl
      | exact (hCT.ne h).elim
      | exact (hCT.ne h.symm).elim
      | exact (hCB h).elim
      | exact (hCB h.symm).elim
      | exact (hCD h).elim
      | exact (hCD h.symm).elim
      | exact (hTB h).elim
      | exact (hTB h.symm).elim
      | exact (hTD h).elim
      | exact (hTD h.symm).elim
      | exact (hBD h).elim
      | exact (hBD h.symm).elim
  let e : (Fin 2 ⊕ Fin 2) ↪ V := ⟨f, hf⟩
  let fixed : Finset V := {C, T, B, D}
  have hrange (v : V) : v ∈ Set.range e ↔ v ∈ fixed := by
    simp [Set.mem_range, e, f, fixed, Sum.exists, Fin.exists_fin_succ, eq_comm] <;> tauto
  have hclosed : ∀ v ∈ fixed, ∀ w ∉ fixed, ¬ G.Adj v w := by
    intro v hv w hw hadj
    simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv | hv <;> subst v
    · have hm := (G.mem_neighborFinset C w).mpr hadj
      rw [hnC, Finset.mem_singleton] at hm
      exact hw (by simp [fixed, hm])
    · have hm := (G.mem_neighborFinset T w).mpr hadj
      rw [hnT, Finset.mem_singleton] at hm
      exact hw (by simp [fixed, hm])
    · exact hBiso w hadj
    · exact hDiso w hadj
  have hnoB (v : V) : ¬ G.Adj v B := fun h => hBiso v h.symm
  have hnoD (v : V) : ¬ G.Adj v D := fun h => hDiso v h.symm
  have hblock : (graphWeightMatrix G (fun v => (weight v : ℚ))).submatrix e e =
      Matrix.fromBlocks !![(2 : ℚ), -1; -1, 3] 0 0
        (Matrix.diagonal ![(3 : ℚ), 3]) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.diagonal, e, f,
        graphWeightMatrix_apply, hC, hT, hB, hD, hCT, hCT.symm,
        hBiso, hDiso, hnoB, hnoD, hCT.ne, hCB, hCD, hTB, hTD, hBD,
        Ne.symm hCT.ne, Ne.symm hCB, Ne.symm hCD, Ne.symm hTB,
        Ne.symm hTD, Ne.symm hBD]
  have hdet : ((graphWeightMatrix G (fun v => (weight v : ℚ))).submatrix e e).det = 45 := by
    rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_succ]
  exact (graph_det_eq_principal_mul_induced_complement G
    (fun v => (weight v : ℚ)) e fixed hrange hclosed).trans (by rw [hdet])

/-- The actual closed canonical edge and four distinct isolated
weight-three vertices contribute the factor 243. -/
theorem familyD_fixed_det_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (C M B D T U : V)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hnC : G.neighborFinset C = {M})
    (hnM : G.neighborFinset M = {C})
    (hBiso : ∀ v, ¬ G.Adj B v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v) :
    (graphWeightMatrix G (fun v => (weight v : ℚ))).det = 243 *
      (graphWeightMatrix (G.induce {v | v ∉ ({C, M, B, D, T, U} : Finset V)})
        (fun v => (weight v.val : ℚ))).det := by
  classical
  have hCB : C ≠ B := by intro h; have hw := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have hw := congrArg weight h; omega
  have hCT : C ≠ T := by intro h; have hw := congrArg weight h; omega
  have hCU : C ≠ U := by intro h; have hw := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have hw := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have hw := congrArg weight h; omega
  have hMT : M ≠ T := by intro h; have hw := congrArg weight h; omega
  have hMU : M ≠ U := by intro h; have hw := congrArg weight h; omega
  let f : Fin 2 ⊕ Fin 4 → V := Sum.elim ![C, M] ![B, D, T, U]
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j
    all_goals
      simp only [f, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] at h
      first
      | rfl
      | exact (hCM.ne h).elim
      | exact (hCM.ne h.symm).elim
      | exact (hCB h).elim
      | exact (hCB h.symm).elim
      | exact (hCD h).elim
      | exact (hCD h.symm).elim
      | exact (hCT h).elim
      | exact (hCT h.symm).elim
      | exact (hCU h).elim
      | exact (hCU h.symm).elim
      | exact (hMB h).elim
      | exact (hMB h.symm).elim
      | exact (hMD h).elim
      | exact (hMD h.symm).elim
      | exact (hMT h).elim
      | exact (hMT h.symm).elim
      | exact (hMU h).elim
      | exact (hMU h.symm).elim
      | exact (hBD h).elim
      | exact (hBD h.symm).elim
      | exact (hTB h).elim
      | exact (hTB h.symm).elim
      | exact (hTD h).elim
      | exact (hTD h.symm).elim
      | exact (hUB h).elim
      | exact (hUB h.symm).elim
      | exact (hUD h).elim
      | exact (hUD h.symm).elim
      | exact (hTU h).elim
      | exact (hTU h.symm).elim
  let e : (Fin 2 ⊕ Fin 4) ↪ V := ⟨f, hf⟩
  let fixed : Finset V := {C, M, B, D, T, U}
  have hrange (v : V) : v ∈ Set.range e ↔ v ∈ fixed := by
    simp [Set.mem_range, e, f, fixed, Sum.exists, Fin.exists_fin_succ, eq_comm] <;> tauto
  have hclosed : ∀ v ∈ fixed, ∀ w ∉ fixed, ¬ G.Adj v w := by
    intro v hv w hw hadj
    simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv | hv | hv | hv <;> subst v
    · have hm := (G.mem_neighborFinset C w).mpr hadj
      rw [hnC, Finset.mem_singleton] at hm
      exact hw (by simp [fixed, hm])
    · have hm := (G.mem_neighborFinset M w).mpr hadj
      rw [hnM, Finset.mem_singleton] at hm
      exact hw (by simp [fixed, hm])
    · exact hBiso w hadj
    · exact hDiso w hadj
    · exact hTiso w hadj
    · exact hUiso w hadj
  have hnoB (v : V) : ¬ G.Adj v B := fun h => hBiso v h.symm
  have hnoD (v : V) : ¬ G.Adj v D := fun h => hDiso v h.symm
  have hnoT (v : V) : ¬ G.Adj v T := fun h => hTiso v h.symm
  have hnoU (v : V) : ¬ G.Adj v U := fun h => hUiso v h.symm
  have hblock : (graphWeightMatrix G (fun v => (weight v : ℚ))).submatrix e e =
      Matrix.fromBlocks !![(2 : ℚ), -1; -1, 2] 0 0
        (Matrix.diagonal ![(3 : ℚ), 3, 3, 3]) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.diagonal, e, f,
        graphWeightMatrix_apply, hC, hM, hB, hD, hT, hU, hCM, hCM.symm,
        hBiso, hDiso, hTiso, hUiso, hnoB, hnoD, hnoT, hnoU,
        hCM.ne, hCB, hCD, hCT, hCU, hMB, hMD, hMT, hMU,
        hBD, hTB, hTD, hUB, hUD, hTU,
        Ne.symm hCM.ne, Ne.symm hCB, Ne.symm hCD, Ne.symm hCT, Ne.symm hCU,
        Ne.symm hMB, Ne.symm hMD, Ne.symm hMT, Ne.symm hMU,
        Ne.symm hBD, Ne.symm hTB, Ne.symm hTD, Ne.symm hUB, Ne.symm hUD, Ne.symm hTU]
  have hdet : ((graphWeightMatrix G (fun v => (weight v : ℚ))).submatrix e e).det = 243 := by
    rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_succ]
  exact (graph_det_eq_principal_mul_induced_complement G
    (fun v => (weight v : ℚ)) e fixed hrange hclosed).trans (by rw [hdet])

end KltDP.LinearAlgebra
