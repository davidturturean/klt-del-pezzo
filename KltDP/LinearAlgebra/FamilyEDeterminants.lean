import KltDP.LinearAlgebra.FamilyEAllocation
import KltDP.LinearAlgebra.GraphDeterminantDecomposition
import KltDP.LinearAlgebra.SchurComplement

/-!
# Actual determinants of the four family-E forests

The actual six fixed vertices form a closed block of determinant 360.
The induced five-vertex complement has determinants 32, 24, 16 and 18 in
its four derived edge cases. The ambient row equation and projection
identity supply the Green value; it is not an extra input to the final
source theorem. Eleven exceptional vertices give negative signed bordered
determinants. Their absolute values are the manuscript's positive Delta.

Reuse: pinned Mathlib `twoBlockTriangular_det`, `det_submatrix_equiv_self`,
`det_fin_two`, `det_fin_three`, and `det_fromBlocks_zero₂₁`, also checked in
the current official Apache-2.0 sources. Existing graph principal-block and
Schur adapters suffice; no library port or geometric realization is used.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A closed set of actual vertices splits the determinant into its
injectively indexed principal block and its actual induced complement. -/
theorem graph_det_eq_principal_mul_induced_complement
    {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (e : I ↪ V) (fixed : Finset V)
    (hrange : ∀ v, v ∈ Set.range e ↔ v ∈ fixed)
    (hclosed : ∀ v ∈ fixed, ∀ w ∉ fixed, ¬ G.Adj v w) :
    (graphWeightMatrix G weight).det =
      ((graphWeightMatrix G weight).submatrix e e).det *
        (graphWeightMatrix (G.induce {v | v ∉ fixed}) (fun v => weight v.val)).det := by
  classical
  letI : Fintype {v // v ∈ Set.range e} :=
    Subtype.fintype (fun v => v ∈ Set.range e)
  -- Match the generic subtype enumeration used by the block determinant API.
  -- The specialized Finset subtype instance is propositionally, not definitionally, equal.
  letI : Fintype {v // v ∈ fixed} := Subtype.fintype (fun v => v ∈ fixed)
  let A := graphWeightMatrix G weight
  let E := Equiv.ofInjective e e.injective
  have hcross : ∀ i, i ∉ fixed → ∀ j, j ∈ fixed → A i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := by intro h; subst j; exact hi hj
    change graphWeightMatrix G weight i j = 0
    rw [graphWeightMatrix_apply, if_neg hij,
      if_neg (fun h => hclosed j hj i hi h.symm)]
  have hblock : (A.toSquareBlockProp (fun v => v ∈ fixed)).det =
      (A.submatrix e e).det := by
    rw [Matrix.equiv_block_det A hrange]
    have he : (A.toSquareBlockProp (fun v => v ∈ Set.range e)).submatrix E E =
        A.submatrix e e := by ext i j; rfl
    rw [← he, Matrix.det_submatrix_equiv_self]
  let inclusion : G.induce {v | v ∉ fixed} ↪g G :=
    { toEmbedding := ⟨Subtype.val, Subtype.val_injective⟩
      map_rel_iff' := Iff.rfl }
  have hrest : A.toSquareBlockProp (fun v => v ∉ fixed) =
      graphWeightMatrix (G.induce {v | v ∉ fixed}) (fun v => weight v.val) :=
    graphWeightMatrix_submatrix inclusion weight
  exact (Matrix.twoBlockTriangular_det A (fun v => v ∈ fixed) hcross).trans
    (congrArg₂ (fun x y : ℚ => x * y) hblock (congrArg Matrix.det hrest))

/-- The actual weight-two graph with no edges has determinant two to its vertex count. -/
theorem canonical_empty_det (G : SimpleGraph V) [DecidableRel G.Adj]
    (he : G.edgeFinset = ∅) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 2 ^ Fintype.card V := by
  have hno (v w : V) : ¬ G.Adj v w := by
    intro h
    have hm : s(v, w) ∈ G.edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using h
    rw [he] at hm
    exact Finset.not_mem_empty _ hm
  have hd : graphWeightMatrix G (fun _ => (2 : ℚ)) = Matrix.diagonal (fun _ => 2) := by
    ext v w
    by_cases h : v = w <;> simp [graphWeightMatrix_apply, Matrix.diagonal, h, hno]
  rw [hd, Matrix.det_diagonal]
  simp

/-- The actual one-edge canonical graph has an A2 block and an isolated complement. -/
theorem canonical_single_edge_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (hxy : x ≠ y)
    (he : G.edgeFinset = {s(x, y)}) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 3 * 2 ^ (Fintype.card V - 2) := by
  classical
  let f : Fin 2 → V := fun i => if i = 0 then x else y
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, hxy, Ne.symm hxy]
  let e : Fin 2 ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = x ∨ v = y := by
    simp [Set.mem_range, e, f, Fin.exists_fin_succ, eq_comm]
  have hpair : G.edgeFinset = {s(x, y), s(x, y)} := by simpa using he
  have hiso : ∀ v, v ∉ Set.range e → ∀ w, ¬ G.Adj v w := by
    intro v hv
    have hn : v ≠ x ∧ v ≠ y := by simpa only [hrange, not_or] using hv
    exact no_adj_outside_pair_edges G x y x y hpair v hn.1 hn.2 hn.1 hn.2
  have hadj : G.Adj x y := by
    have hm : s(x, y) ∈ G.edgeFinset := by rw [he]; simp
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hm
  have hdet : ((graphWeightMatrix G (fun _ => (2 : ℚ))).submatrix e e).det = 3 := by
    rw [Matrix.det_fin_two]
    norm_num [Matrix.submatrix_apply, e, f, graphWeightMatrix_apply,
      hxy, Ne.symm hxy, hadj, hadj.symm]
  rw [graph_det_eq_principal_mul_complement G (fun _ => (2 : ℚ)) e hiso, hdet]
  simp [card_outsideRange]

/-- The actual two-edge path has an A3 block and an isolated complement. -/
theorem canonical_two_path_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (he : G.edgeFinset = {s(x, y), s(y, z)}) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 4 * 2 ^ (Fintype.card V - 3) := by
  classical
  let f : Fin 3 → V := ![x, y, z]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  let e : Fin 3 ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = x ∨ v = y ∨ v = z := by
    simp [Set.mem_range, e, f, Fin.exists_fin_succ, eq_comm, or_comm, or_left_comm, or_assoc]
  have hiso : ∀ v, v ∉ Set.range e → ∀ w, ¬ G.Adj v w := by
    intro v hv
    have hn : v ≠ x ∧ v ≠ y ∧ v ≠ z := by simpa only [hrange, not_or] using hv
    exact no_adj_outside_pair_edges G x y y z he v hn.1 hn.2.1 hn.2.1 hn.2.2
  have hadj (v w : V) : G.Adj v w ↔
      ((v = x ∧ w = y) ∨ (v = y ∧ w = x)) ∨
      ((v = y ∧ w = z) ∨ (v = z ∧ w = y)) := by
    calc
      G.Adj v w ↔ s(v, w) ∈ G.edgeFinset := by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      _ ↔ _ := by rw [he]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  have he0 : e 0 = x := rfl
  have he1 : e 1 = y := rfl
  have he2 : e 2 = z := rfl
  have hdet : ((graphWeightMatrix G (fun _ => (2 : ℚ))).submatrix e e).det = 4 := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.submatrix_apply, he0, he1, he2]
    norm_num [graphWeightMatrix_apply, hadj, hxy, hxz, hyz,
      Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  rw [graph_det_eq_principal_mul_complement G (fun _ => (2 : ℚ)) e hiso, hdet]
  simp [card_outsideRange]

/-- Two disjoint actual canonical edges give two A2 blocks and an isolated complement. -/
theorem canonical_disjoint_edges_det
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z w : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (he : G.edgeFinset = {s(x, y), s(z, w)}) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 9 * 2 ^ (Fintype.card V - 4) := by
  classical
  let f : Fin 2 ⊕ Fin 2 → V := Sum.elim
    (fun i => if i = 0 then x else y) (fun i => if i = 0 then z else w)
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j <;> simp_all [f]
  let e : (Fin 2 ⊕ Fin 2) ↪ V := ⟨f, hf⟩
  have hrange (v : V) : v ∈ Set.range e ↔ v = x ∨ v = y ∨ v = z ∨ v = w := by
    simp [Set.mem_range, e, f, Sum.exists, Fin.exists_fin_succ, eq_comm, or_assoc]
  have hiso : ∀ v, v ∉ Set.range e → ∀ u, ¬ G.Adj v u := by
    intro v hv
    have hn : v ≠ x ∧ v ≠ y ∧ v ≠ z ∧ v ≠ w := by
      simpa only [hrange, not_or] using hv
    exact no_adj_outside_pair_edges G x y z w he v hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
  have hadj (v u : V) : G.Adj v u ↔
      ((v = x ∧ u = y) ∨ (v = y ∧ u = x)) ∨
      ((v = z ∧ u = w) ∨ (v = w ∧ u = z)) := by
    calc
      G.Adj v u ↔ s(v, u) ∈ G.edgeFinset := by
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      _ ↔ _ := by rw [he]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
  have hblock : (graphWeightMatrix G (fun _ => (2 : ℚ))).submatrix e e =
      Matrix.fromBlocks !![(2 : ℚ), -1; -1, 2] 0 0 !![(2 : ℚ), -1; -1, 2] := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, e, f,
        graphWeightMatrix_apply, hadj, hxy, hxz, hxw, hyz, hyw, hzw,
        Ne.symm hxy, Ne.symm hxz, Ne.symm hxw, Ne.symm hyz, Ne.symm hyw, Ne.symm hzw]
  rw [graph_det_eq_principal_mul_complement G (fun _ => (2 : ℚ)) e hiso,
    hblock, Matrix.det_fromBlocks_zero₂₁]
  norm_num [card_outsideRange]

/-- The four actual canonical complement determinants. Each branch is
computed from the corresponding actual edge set in the derived shape. -/
theorem five_vertex_forest_det_cases
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 5)
    (hshape : FiveVertexForestShape G) :
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 32 ∨
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 24 ∨
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 16 ∨
    (graphWeightMatrix G (fun _ => (2 : ℚ))).det = 18 := by
  rcases hshape with he | ⟨x, y, hxy, he, _, _⟩ |
    ⟨x, y, z, hxy, hxz, hyz, he, _, _⟩ |
    ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he, _, _⟩
  · exact Or.inl (by simpa [hcard] using canonical_empty_det G he)
  · have hdet := canonical_single_edge_det G x y hxy he
    norm_num [hcard] at hdet
    exact Or.inr (Or.inl hdet)
  · have hdet := canonical_two_path_det G x y z hxy hxz hyz he
    norm_num [hcard] at hdet
    exact Or.inr (Or.inr (Or.inl hdet))
  · have hdet := canonical_disjoint_edges_det G x y z w hxy hxz hxw hyz hyw hzw he
    norm_num [hcard] at hdet
    exact Or.inr (Or.inr (Or.inr hdet))

/-- The six actual fixed family-E vertices contribute determinant 360.
The complement is the actual induced graph; no block determinant is assumed. -/
theorem familyE_fixed_det_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B M D T U : V)
    (hC : weight C = 2) (hB : weight B = 3) (hM : weight M = 2)
    (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hUB : U ≠ B) (hTU : T ≠ U)
    (hBM : G.Adj B M) (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hCiso : ∀ v, ¬ G.Adj C v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v) :
    (graphWeightMatrix G weight).det = 360 *
      (graphWeightMatrix (G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)})
        (fun v => weight v.val)).det := by
  classical
  have hCB : C ≠ B := by intro h; have hw := congrArg weight h; rw [hC, hB] at hw; norm_num at hw
  have hCM : C ≠ M := by intro h; subst M; exact hCiso B hBM.symm
  have hCD : C ≠ D := by intro h; have hw := congrArg weight h; rw [hC, hD] at hw; norm_num at hw
  have hCT : C ≠ T := by intro h; have hw := congrArg weight h; rw [hC, hT] at hw; norm_num at hw
  have hCU : C ≠ U := by intro h; have hw := congrArg weight h; rw [hC, hU] at hw; norm_num at hw
  have hBD : B ≠ D := by intro h; have hw := congrArg weight h; rw [hB, hD] at hw; norm_num at hw
  have hMD : M ≠ D := by intro h; have hw := congrArg weight h; rw [hM, hD] at hw; norm_num at hw
  have hMT : M ≠ T := by intro h; have hw := congrArg weight h; rw [hM, hT] at hw; norm_num at hw
  have hMU : M ≠ U := by intro h; have hw := congrArg weight h; rw [hM, hU] at hw; norm_num at hw
  have hTD : T ≠ D := by intro h; have hw := congrArg weight h; rw [hT, hD] at hw; norm_num at hw
  have hUD : U ≠ D := by intro h; have hw := congrArg weight h; rw [hU, hD] at hw; norm_num at hw
  let f : Fin 2 ⊕ Fin 4 → V := Sum.elim ![B, M] ![C, D, T, U]
  have hf : Function.Injective f := by
    rintro (i | i) (j | j) h
    all_goals fin_cases i <;> fin_cases j
    all_goals
      simp only [f, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero', Matrix.cons_val_succ'] at h
      first
      | rfl
      | exact (hCB h).elim
      | exact (hCB h.symm).elim
      | exact (hCM h).elim
      | exact (hCM h.symm).elim
      | exact (hCD h).elim
      | exact (hCD h.symm).elim
      | exact (hCT h).elim
      | exact (hCT h.symm).elim
      | exact (hCU h).elim
      | exact (hCU h.symm).elim
      | exact (hBM.ne h).elim
      | exact (hBM.ne h.symm).elim
      | exact (hBD h).elim
      | exact (hBD h.symm).elim
      | exact (hTB h).elim
      | exact (hTB h.symm).elim
      | exact (hUB h).elim
      | exact (hUB h.symm).elim
      | exact (hMD h).elim
      | exact (hMD h.symm).elim
      | exact (hMT h).elim
      | exact (hMT h.symm).elim
      | exact (hMU h).elim
      | exact (hMU h.symm).elim
      | exact (hTD h).elim
      | exact (hTD h.symm).elim
      | exact (hUD h).elim
      | exact (hUD h.symm).elim
      | exact (hTU h).elim
      | exact (hTU h.symm).elim
  let e : (Fin 2 ⊕ Fin 4) ↪ V := ⟨f, hf⟩
  let fixed : Finset V := {C, B, M, D, T, U}
  have hrange (v : V) : v ∈ Set.range e ↔ v ∈ fixed := by
    simp [Set.mem_range, e, f, fixed, Sum.exists, Fin.exists_fin_succ, eq_comm] <;> tauto
  have hclosed : ∀ v ∈ fixed, ∀ w ∉ fixed, ¬ G.Adj v w := by
    intro v hv w hw hadj
    simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv | hv | hv | hv <;> subst v
    · exact hCiso w hadj
    · have hm := (G.mem_neighborFinset B w).mpr hadj
      rw [hnB, Finset.mem_singleton] at hm
      exact hw (by simp [fixed, hm])
    · have hm := (G.mem_neighborFinset M w).mpr hadj
      rw [hnM, Finset.mem_singleton] at hm
      exact hw (by simp [fixed, hm])
    · exact hDiso w hadj
    · exact hTiso w hadj
    · exact hUiso w hadj
  have hnoC (v : V) : ¬ G.Adj v C := fun h => hCiso v h.symm
  have hnoD (v : V) : ¬ G.Adj v D := fun h => hDiso v h.symm
  have hnoT (v : V) : ¬ G.Adj v T := fun h => hTiso v h.symm
  have hnoU (v : V) : ¬ G.Adj v U := fun h => hUiso v h.symm
  have hblock : (graphWeightMatrix G weight).submatrix e e =
      Matrix.fromBlocks !![(3 : ℚ), -1; -1, 2] 0 0
        (Matrix.diagonal ![(2 : ℚ), 4, 3, 3]) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.diagonal, e, f,
        graphWeightMatrix_apply, hC, hB, hM, hD, hT, hU, hBM, hBM.symm,
        hCiso, hDiso, hTiso, hUiso, hnoC, hnoD, hnoT, hnoU,
        hCB, hCM, hCD, hCT, hCU, hBM.ne, hBD, hTB, hUB, hMD, hMT, hMU, hTD, hUD, hTU,
        Ne.symm hCB, Ne.symm hCM, Ne.symm hCD, Ne.symm hCT, Ne.symm hCU,
        Ne.symm hBM.ne, Ne.symm hBD, Ne.symm hTB, Ne.symm hUB, Ne.symm hMD,
        Ne.symm hMT, Ne.symm hMU, Ne.symm hTD, Ne.symm hUD, Ne.symm hTU]
  have hdet : ((graphWeightMatrix G weight).submatrix e e).det = 360 := by
    rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
    norm_num [Fin.prod_univ_succ]
  exact (graph_det_eq_principal_mul_induced_complement G weight e fixed hrange hclosed).trans
    (by rw [hdet])

/-- The four exceptional and signed bordered determinant pairs. This is
an output relation on actual determinants; the source theorem derives it. -/
def FamilyEDeterminantValues (exceptional bordered : ℚ) : Prop :=
  (exceptional = 11520 ∧ bordered = -1728) ∨
  (exceptional = 8640 ∧ bordered = -1296) ∨
  (exceptional = 5760 ∧ bordered = -864) ∨
  (exceptional = 6480 ∧ bordered = -972)

/-- Source hypotheses for family E determine all four determinant pairs.
The actual Green energy, fixed components and leftover shape are conclusions
of the imported classification, and are not supplied as hypotheses here. -/
theorem familyE_source_determinants
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T U : V)
    (hcard : Fintype.card V = 11)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hedges : G.edgeFinset.card ≤ 3)
    (hB : weight B = 3) (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hUsingle : ∀ v, G.Reachable U v → v ≠ U → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2)
    (hvolume : 0 < -2 + dotProduct (fun i => weight i - 2) coeff)
    (hbudget : -2 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-2 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 10 ∧
    -2 + dotProduct (fun i => weight i - 2) coeff = 1 / 15 ∧
    dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 23 / 20 ∧
    FamilyEDeterminantValues (graphWeightMatrix G weight).det
      (borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1)).det := by
  classical
  obtain ⟨M, hM, hBM, hnB, hnM, _, hCiso, hDiso, hTiso, hUiso, hell, hvol, hg,
      hremaining⟩ := familyE_complete_forest G weight coeff C B D T U hcard hA hG hrow
    hedges hB hD hT hU hTB hTD hUB hUD hTU hcanonical hBsingle hDsingle hTsingle
    hUsingle hother hvolume hbudget hprojection
  let fixed : Finset V := {C, B, M, D, T, U}
  let Z := G.induce {v | v ∉ fixed}
  obtain ⟨_, hZcard, hZweights, _, hZshape⟩ := hremaining
  have hfactor := familyE_fixed_det_factor G weight C B M D T U
    (hcanonical C (.refl C)) hB hM hD hT hU hTB hUB hTU hBM hnB hnM
    hCiso hDiso hTiso hUiso
  have hweights : (fun v : {v | v ∉ fixed} => weight v.val) = fun _ => (2 : ℚ) :=
    funext hZweights
  change (graphWeightMatrix G weight).det = 360 *
    (graphWeightMatrix Z (fun v => weight v.val)).det at hfactor
  rw [hweights] at hfactor
  have hb := det_minusOne_borderedGram hA (threeMarkedSource C B D)
  rw [hcard, hg] at hb
  norm_num at hb
  refine ⟨hell, hvol, hg, ?_⟩
  rcases five_vertex_forest_det_cases Z hZcard hZshape with hz | hz | hz | hz
  · rw [hz] at hfactor
    exact Or.inl ⟨by linarith only [hfactor], by linarith only [hfactor, hb]⟩
  · rw [hz] at hfactor
    exact Or.inr (Or.inl ⟨by linarith only [hfactor], by linarith only [hfactor, hb]⟩)
  · rw [hz] at hfactor
    exact Or.inr (Or.inr (Or.inl ⟨by linarith only [hfactor], by linarith only [hfactor, hb]⟩))
  · rw [hz] at hfactor
    exact Or.inr (Or.inr (Or.inr ⟨by linarith only [hfactor], by linarith only [hfactor, hb]⟩))

/-- The positive full-lattice determinant values are absolute values of
these actual signed bordered determinants. -/
theorem familyE_absolute_determinants {exceptional bordered : ℚ}
    (h : FamilyEDeterminantValues exceptional bordered) :
    (exceptional = 11520 ∧ |bordered| = 1728) ∨
    (exceptional = 8640 ∧ |bordered| = 1296) ∨
    (exceptional = 5760 ∧ |bordered| = 864) ∨
    (exceptional = 6480 ∧ |bordered| = 972) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

end KltDP.LinearAlgebra
