import KltDP.Lattices.SmallADEForestLattice
import KltDP.LinearAlgebra.SchurComplement
import KltDP.LinearAlgebra.WeightedPathTransport

/-!
# Integral lattice exclusions for the ten-row determinant endgame

These are the lattice deductions in manuscript `thm:forest-exclusion`,
lines 2822--2840. The full family consists of actual integral vectors in a
module with a finite basis and a unimodular bilinear form. Its actual span,
independence, finite index and index-square equation are derived.

Seven rows have one of five nonsquare determinant values. At determinant
1296, three or four actual orthogonal node rows contradict characteristic
parity. At determinant 576, four actual node rows force the full integral
half-sum, its square minus two, and its zero canonical pairing.

The final graph adapters use an equality between the entrywise rational
cast of the actual integral Gram matrix and the actual bordered graph
matrix. Node rows are derived from isolation, weight two and zero contact.
No index, code dimension, even-pairing bound or no-even-node theorem is an
input. The geometric Picard/intersection/characteristic identifications,
and exclusion of the forced half-sum in odd positive characteristic,
remain separate obligations; this is not `thm:forest-exclusion` itself.

Reuse: the compiled project index/Gram and integral-code theorems are used
directly. Pinned and current official Apache-2.0 Mathlib determinant casts,
full-rank integral quotient and factorization APIs were checked. No newer
source port is necessary.
-/

namespace KltDP.Lattices.TenRowPicardExclusions

open Matrix SimpleGraph KltDP.Codes KltDP.LinearAlgebra
open SmallADEForestLattice IndexDeterminant IntegralNodeObstruction
open scoped BigOperators

variable {M ι ν : Type*} [AddCommGroup M]
variable [Fintype ι] [DecidableEq ι]

/-- A nonzero actual Gram determinant gives independence and computes the
square of the actual span index in the original unimodular module. -/
theorem span_index_sq_of_gram_det
    (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (v : ι → M) {d : ℕ} (hd : d ≠ 0)
    (hdet : (familyGram B v).det.natAbs = d) :
    LinearIndependent ℤ v ∧
      (Submodule.span ℤ (Set.range v)).toAddSubgroup.index ^ 2 = d := by
  have hn : (familyGram B v).det ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hdet
    exact hd hdet.symm
  have hv := linearIndependent_of_familyGram_det_ne_zero B v hn
  exact ⟨hv, (familyGram_natAbs_det_eq_span_index_sq b B hB v hv).symm.trans hdet⟩

private theorem bounded_nonsquare_values : ∀ I : Fin 42,
    ¬ ((I : ℕ)^2 = 768 ∨ (I : ℕ)^2 = 720 ∨ (I : ℕ)^2 = 972 ∨
      (I : ℕ)^2 = 1728 ∨ (I : ℕ)^2 = 864) := by decide

/-- The five distinct nonsquare values account for seven source rows.
A finite natural bound is proved before the kernel-checked finite test. -/
theorem no_square_among_nonsquare_row_values (I : ℕ)
    (h : I^2 = 768 ∨ I^2 = 720 ∨ I^2 = 972 ∨ I^2 = 1728 ∨ I^2 = 864) : False := by
  have hu : I^2 ≤ 1728 := by rcases h with h | h | h | h | h <;> omega
  have hI : I < 42 := by
    by_contra hn
    have h42 : 42 ≤ I := by omega
    have hp := Nat.pow_le_pow_left h42 2
    norm_num at hp
    omega
  exact bounded_nonsquare_values ⟨I, hI⟩ h

/-- No actual full-rank family in an integral unimodular module can have
any of the seven nonsquare-row determinants. -/
theorem nonsquare_rows_impossible
    (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) (v : ι → M)
    (hdet : (familyGram B v).det.natAbs = 768 ∨
      (familyGram B v).det.natAbs = 720 ∨ (familyGram B v).det.natAbs = 972 ∨
      (familyGram B v).det.natAbs = 1728 ∨ (familyGram B v).det.natAbs = 864) : False := by
  have hn : (familyGram B v).det.natAbs ≠ 0 := by
    rcases hdet with h | h | h | h | h <;> omega
  obtain ⟨_, hs⟩ := span_index_sq_of_gram_det b B hB v hn rfl
  apply no_square_among_nonsquare_row_values
    (Submodule.span ℤ (Set.range v)).toAddSubgroup.index
  rwa [hs]

/-- The index 24 is derived from the actual determinant 576. -/
theorem span_index_eq_twentyFour
    (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) (v : ι → M)
    (hdet : (familyGram B v).det.natAbs = 576) :
    (Submodule.span ℤ (Set.range v)).toAddSubgroup.index = 24 := by
  obtain ⟨_, hs⟩ := span_index_sq_of_gram_det b B hB v (by decide : 576 ≠ 0) hdet
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  simpa only [show (24 : ℕ)^2 = 576 by decide] using hs

/-- The index 36 is derived from the actual determinant 1296. -/
theorem span_index_eq_thirtySix
    (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) (v : ι → M)
    (hdet : (familyGram B v).det.natAbs = 1296) :
    (Submodule.span ℤ (Set.range v)).toAddSubgroup.index = 36 := by
  obtain ⟨_, hs⟩ := span_index_sq_of_gram_det b B hB v (by decide : 1296 ≠ 0) hdet
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  simpa only [show (36 : ℕ)^2 = 1296 by decide] using hs

private theorem factorization_twentyFour : (24 : ℕ).factorization 2 = 3 := by
  change (2^3 * 3 : ℕ).factorization 2 = 3
  rw [Nat.factorization_mul (by decide : (2 : ℕ)^3 ≠ 0) (by decide : (3 : ℕ) ≠ 0),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization]
  simp

private theorem factorization_thirtySix : (36 : ℕ).factorization 2 = 2 := by
  change (2^2 * 3^2 : ℕ).factorization 2 = 2
  rw [Nat.factorization_mul (by decide : (2 : ℕ)^2 ≠ 0) (by decide : (3 : ℕ)^2 ≠ 0),
    Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
  simp

variable [Fintype ν]

omit [Fintype ι] [Fintype ν] in
/-- Actual diagonal node rows imply even pairing with the entire actual
span. The even-pairing condition used by the code theorem is derived. -/
theorem node_rows_even_on_span
    (B : LinearMap.BilinForm ℤ M) (v : ι → M) (nodes : ν ↪ ι)
    (hrows : ∀ i j, B (v (nodes i)) (v j) = if nodes i = j then -2 else 0) :
    ∀ i y, y ∈ Submodule.span ℤ (Set.range v) → Even (B (v (nodes i)) y) := by
  intro i y hy
  apply even_pairing_span B v (v (nodes i)) ?_ y hy
  intro j
  rw [hrows]
  split_ifs <;> norm_num

/-- Three or four actual node summands at determinant 1296 contradict
characteristic parity. The actual span index is computed, not supplied. -/
theorem determinant1296_nodes_impossible
    (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) (v : ι → M)
    (hdet : (familyGram B v).det.natAbs = 1296)
    (nodes : ν ↪ ι)
    (hrows : ∀ i j, B (v (nodes i)) (v j) = if nodes i = j then -2 else 0)
    (K : M) (hchar : IsCharacteristic B K) (hK : ∀ i, B K (v (nodes i)) = 0)
    (hcard : Fintype.card ν = 3 ∨ Fintype.card ν = 4) : False := by
  obtain ⟨hv, _⟩ := span_index_sq_of_gram_det b B hB v (by decide : 1296 ≠ 0) hdet
  let Γ := Submodule.span ℤ (Set.range v)
  let bΓ : Basis ι ℤ Γ := Basis.span hv
  letI : Γ.toAddSubgroup.FiniteIndex := ⟨ne_of_gt (index_pos b Γ bΓ)⟩
  have hindex : Γ.toAddSubgroup.index.factorization 2 = 2 := by
    rw [show Γ.toAddSubgroup.index = 36 from span_index_eq_thirtySix b B hB v hdet,
      factorization_thirtySix]
  have hsq (i : ν) : B (v (nodes i)) (v (nodes i)) = -2 := by simp only [hrows, if_pos rfl, if_true]
  have horth (i j : ν) (hij : i ≠ j) : B (v (nodes i)) (v (nodes j)) = 0 := by
    rw [hrows, if_neg (fun h => hij (nodes.injective h))]
  have hpair := node_rows_even_on_span B v nodes hrows
  rcases hcard with hc | hc
  · have h := three_le_index_factorization_of_card_eq_three
      b B hB Γ (fun i => v (nodes i)) hpair K hchar hsq horth hK hc
    omega
  · have h := three_le_index_factorization_of_card_eq_four
      b B hB Γ (fun i => v (nodes i)) hpair K hchar hsq horth hK hc
    omega

/-- Four actual node rows at determinant 576 force the full half-sum in
the original integral module, with its actual square and canonical pairing. -/
theorem determinant576_four_nodes_half
    (b : Basis ι ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1) (v : ι → M)
    (hdet : (familyGram B v).det.natAbs = 576)
    (nodes : ν ↪ ι)
    (hrows : ∀ i j, B (v (nodes i)) (v j) = if nodes i = j then -2 else 0)
    (K : M) (hchar : IsCharacteristic B K) (hK : ∀ i, B K (v (nodes i)) = 0)
    (hcard : Fintype.card ν = 4) :
    ∃ m : M, (2 : ℤ) • m = (∑ i, v (nodes i)) ∧ B m m = -2 ∧ B K m = 0 := by
  obtain ⟨hv, _⟩ := span_index_sq_of_gram_det b B hB v (by decide : 576 ≠ 0) hdet
  let Γ := Submodule.span ℤ (Set.range v)
  let bΓ : Basis ι ℤ Γ := Basis.span hv
  letI : Γ.toAddSubgroup.FiniteIndex := ⟨ne_of_gt (index_pos b Γ bΓ)⟩
  have hindex : Γ.toAddSubgroup.index.factorization 2 ≤ 3 := by
    rw [show Γ.toAddSubgroup.index = 24 from span_index_eq_twentyFour b B hB v hdet,
      factorization_twentyFour]
  have hsq (i : ν) : B (v (nodes i)) (v (nodes i)) = -2 := by simp only [hrows, if_pos rfl, if_true]
  have horth (i j : ν) (hij : i ≠ j) : B (v (nodes i)) (v (nodes j)) = 0 := by
    rw [hrows, if_neg (fun h => hij (nodes.injective h))]
  exact exists_four_node_half_with_pairings_of_index_factorization_le_three
    b B hB Γ (fun i => v (nodes i)) (node_rows_even_on_span B v nodes hrows)
    K hchar hsq horth hK hcard hindex

omit [Fintype ν] in
/-- Casting an actual integer matrix to a rational computed matrix
transfers its absolute determinant back to the original integer lattice. -/
theorem natAbs_det_of_rational_matrix {Q : Matrix ι ι ℤ} {R : Matrix ι ι ℚ}
    (hQ : Q.map (fun z => (z : ℚ)) = R) {d : ℕ} (hd : |R.det| = (d : ℚ)) :
    Q.det.natAbs = d := by
  have hcast : (Q.det : ℚ) = R.det := by rw [Int.cast_det, hQ]
  apply Nat.cast_injective (R := ℚ)
  calc
    (Q.det.natAbs : ℚ) = |(Q.det : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    _ = (d : ℚ) := by rw [hcast, hd]

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype ι] [DecidableEq ι] [Fintype ν] [Fintype V] in
/-- An actual isolated weight-two graph vertex with zero border contact
gives a diagonal minus-two row against the full original vector family. -/
theorem isolated_graph_node_rows
    (B : LinearMap.BilinForm ℤ M) (w : V → M) (P : M)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight p : V → ℚ)
    (hGram : (familyGram B (Sum.elim w (fun _ : Unit => P))).map (fun z => (z : ℚ)) =
      borderedGram (graphWeightMatrix G weight) p (-1))
    (x : V) (hiso : ∀ y, ¬ G.Adj x y) (hweight : weight x = 2) (hp : p x = 0) :
    ∀ j : V ⊕ Unit,
      B (w x) (Sum.elim w (fun _ : Unit => P) j) =
        if Sum.inl x = j then -2 else 0 := by
  intro j
  have hc := congr_fun (congr_fun hGram (Sum.inl x)) j
  cases j with
  | inl y =>
      change (B (w x) (w y) : ℚ) = -(graphWeightMatrix G weight x y) at hc
      simp only [Sum.elim_inl, Sum.inl.injEq]
      apply Int.cast_injective (α := ℚ)
      by_cases h : x = y
      · subst y
        simpa [graphWeightMatrix_apply, hweight] using hc
      · simpa [graphWeightMatrix_apply, h, hiso, hweight] using hc
  | inr u =>
      change (B (w x) P : ℚ) = p x at hc
      simp only [Sum.elim_inr, Sum.inl_ne_inr, if_false]
      apply Int.cast_injective (α := ℚ)
      simpa only [hp, Int.cast_zero] using hc

omit [Fintype ι] [DecidableEq ι] in
/-- Actual graph and integral Gram data exclude the D1/E2 determinant
when three or four isolated canonical vertices miss the border vector. -/
theorem bordered_graph_determinant1296_impossible
    (b : Basis (V ⊕ Unit) ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (w : V → M) (P : M)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight p : V → ℚ)
    (hGram : (familyGram B (Sum.elim w (fun _ : Unit => P))).map (fun z => (z : ℚ)) =
      borderedGram (graphWeightMatrix G weight) p (-1))
    (hdet : |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 1296)
    (nodes : ν ↪ V) (hiso : ∀ i y, ¬ G.Adj (nodes i) y)
    (hweight : ∀ i, weight (nodes i) = 2) (hp : ∀ i, p (nodes i) = 0)
    (K : M) (hchar : IsCharacteristic B K) (hK : ∀ i, B K (w (nodes i)) = 0)
    (hcard : Fintype.card ν = 3 ∨ Fintype.card ν = 4) : False := by
  let e : ν ↪ (V ⊕ Unit) :=
    ⟨fun i => Sum.inl (nodes i), fun i j h => nodes.injective (Sum.inl.inj h)⟩
  exact determinant1296_nodes_impossible b B hB (Sum.elim w (fun _ : Unit => P))
    (natAbs_det_of_rational_matrix hGram hdet) e
    (fun i => isolated_graph_node_rows B w P G weight p hGram (nodes i)
      (hiso i) (hweight i) (hp i)) K hchar hK hcard

omit [Fintype ι] [DecidableEq ι] in
/-- Actual graph and integral Gram data at the A2 determinant force the
sum of the four specified isolated vertices to have an integral half. -/
theorem bordered_graph_determinant576_four_nodes_half
    (b : Basis (V ⊕ Unit) ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (w : V → M) (P : M)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight p : V → ℚ)
    (hGram : (familyGram B (Sum.elim w (fun _ : Unit => P))).map (fun z => (z : ℚ)) =
      borderedGram (graphWeightMatrix G weight) p (-1))
    (hdet : |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 576)
    (nodes : ν ↪ V) (hiso : ∀ i y, ¬ G.Adj (nodes i) y)
    (hweight : ∀ i, weight (nodes i) = 2) (hp : ∀ i, p (nodes i) = 0)
    (K : M) (hchar : IsCharacteristic B K) (hK : ∀ i, B K (w (nodes i)) = 0)
    (hcard : Fintype.card ν = 4) :
    ∃ m : M, (2 : ℤ) • m = (∑ i, w (nodes i)) ∧ B m m = -2 ∧ B K m = 0 := by
  let e : ν ↪ (V ⊕ Unit) :=
    ⟨fun i => Sum.inl (nodes i), fun i j h => nodes.injective (Sum.inl.inj h)⟩
  exact determinant576_four_nodes_half b B hB (Sum.elim w (fun _ : Unit => P))
    (natAbs_det_of_rational_matrix hGram hdet) e
    (fun i => isolated_graph_node_rows B w P G weight p hGram (nodes i)
      (hiso i) (hweight i) (hp i)) K hchar hK hcard

omit [Fintype ι] [DecidableEq ι] [Fintype ν] in
/-- The nonsquare rows are excluded directly from the actual rational
bordered graph determinant and actual integral Gram compatibility. -/
theorem bordered_graph_nonsquare_rows_impossible
    (b : Basis (V ⊕ Unit) ℤ M) (B : LinearMap.BilinForm ℤ M)
    (hB : (BilinForm.toMatrix b B).det.natAbs = 1)
    (w : V → M) (P : M)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight p : V → ℚ)
    (hGram : (familyGram B (Sum.elim w (fun _ : Unit => P))).map (fun z => (z : ℚ)) =
      borderedGram (graphWeightMatrix G weight) p (-1))
    (hdet : |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 768 ∨
      |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 720 ∨
      |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 972 ∨
      |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 1728 ∨
      |(borderedGram (graphWeightMatrix G weight) p (-1)).det| = 864) : False := by
  apply nonsquare_rows_impossible b B hB (Sum.elim w (fun _ : Unit => P))
  rcases hdet with h | h | h | h | h
  · exact Or.inl (natAbs_det_of_rational_matrix hGram h)
  · exact Or.inr (Or.inl (natAbs_det_of_rational_matrix hGram h))
  · exact Or.inr (Or.inr (Or.inl (natAbs_det_of_rational_matrix hGram h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (natAbs_det_of_rational_matrix hGram h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (natAbs_det_of_rational_matrix hGram h))))

end Graph

end KltDP.Lattices.TenRowPicardExclusions
