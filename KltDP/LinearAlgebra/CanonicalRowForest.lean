import KltDP.LinearAlgebra.Stieltjes
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# A forest from negative intersection and canonical discrepancy rows

For a matrix with negative quadratic values and nonnegative off-diagonal
entries, canonical rows and coefficients in `(-1,0]` exclude every nonempty
subfamily whose internal row sums are at least two. Restrict `1+d` to the
subfamily: its quadratic value is nonnegative by the rows and strictly
negative by the original matrix. Applying this to two vertices excludes
intersection at least two; applying it to the vertices of a cycle proves
acyclicity. No forest, principal-minor, or classification assumption is used.

The cycle adapter reuses pinned Mathlib's exact two-neighbor theorem for a
cycle's original walk subgraph. Existing Stieltjes and finite classification
sources and newer official Mathlib Acyclic/Matrix.PosDef were checked before
this adapter; no port or additional foundation is needed.
-/

noncomputable section

open Matrix SimpleGraph
open scoped BigOperators

universe u

namespace KltDP.LinearAlgebra.CanonicalRowForest

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- No nonempty family can have internal intersection weight at least two
at each vertex under strict klt canonical rows. -/
theorem not_internal_sum_ge_two (M : Matrix I I ℚ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hnegative : ∀ x : I → ℚ, x ≠ 0 → dotProduct x (M *ᵥ x) < 0)
    (d : I → ℚ) (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : M *ᵥ d = fun i => -M i i - 2)
    (s : Finset I) (hs : s.Nonempty) :
    ¬ ∀ i ∈ s, 2 ≤ ∑ j ∈ s.erase i, M i j := by
  classical
  intro hinternal
  let t : I → ℚ := fun i => if i ∈ s then 1 else -d i
  let x : I → ℚ := d + t
  have ht (i : I) : 0 ≤ t i := by
    by_cases hi : i ∈ s
    · simp [t, hi]
    · simpa only [t, if_neg hi] using neg_nonneg.mpr (hupper i)
  have hxpos (i : I) (hi : i ∈ s) : 0 < x i := by
    change 0 < d i + t i
    have hti : t i = 1 := by simp [t, hi]
    rw [hti]
    linarith only [hlower i]
  have hxzero (i : I) (hi : i ∉ s) : x i = 0 := by
    simp [x, t, hi]
  have hxne : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hs
    intro hzero
    have hz : x i = 0 := congrFun hzero i
    exact (ne_of_gt (hxpos i hi)) hz
  have himage (i : I) (hi : i ∈ s) : 0 ≤ (M *ᵥ x) i := by
    have hsmall : 2 ≤ ∑ j ∈ s.erase i, M i j * t j := by
      have heq : (∑ j ∈ s.erase i, M i j * t j) =
          ∑ j ∈ s.erase i, M i j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [t, Finset.mem_of_mem_erase hj]
      rw [heq]
      exact hinternal i hi
    have hsubset : s.erase i ⊆ Finset.univ.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ j⟩
    have hlarge : 2 ≤ ∑ j ∈ Finset.univ.erase i, M i j * t j :=
      hsmall.trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j hj _ => mul_nonneg (hoff i j (Finset.mem_erase.mp hj).1.symm) (ht j)))
    have hMt : M i i + 2 ≤ (M *ᵥ t) i := by
      change M i i + 2 ≤ ∑ j, M i j * t j
      rw [← Finset.add_sum_erase Finset.univ (fun j => M i j * t j)
        (Finset.mem_univ i)]
      have hti : t i = 1 := by simp [t, hi]
      rw [hti, mul_one]
      exact add_le_add_left hlarge _
    change 0 ≤ (M *ᵥ (d + t)) i
    rw [Matrix.mulVec_add, Pi.add_apply]
    have hri : (M *ᵥ d) i = -M i i - 2 := congrFun hrow i
    rw [hri]
    linarith only [hMt]
  have hnonneg : 0 ≤ dotProduct x (M *ᵥ x) := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i ∈ s
    · exact mul_nonneg (hxpos i hi).le (himage i hi)
    · rw [hxzero i hi, zero_mul]
  exact (not_lt_of_ge hnonneg) (hnegative x hxne)

/-- A symmetric matrix satisfying the canonical discrepancy rows cannot
have an off-diagonal entry at least two. -/
theorem offDiagonal_lt_two (M : Matrix I I ℚ)
    (hsymm : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hnegative : ∀ x : I → ℚ, x ≠ 0 → dotProduct x (M *ᵥ x) < 0)
    (d : I → ℚ) (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : M *ᵥ d = fun i => -M i i - 2)
    (i j : I) (hij : i ≠ j) : M i j < 2 := by
  classical
  by_contra hnot
  have htwo : 2 ≤ M i j := le_of_not_gt hnot
  apply not_internal_sum_ge_two M hoff hnegative d hlower hupper hrow
    {i, j} (by simp)
  intro v hv
  have hv' : v = i ∨ v = j := by simpa using hv
  rcases hv' with hvi | hvj
  · subst v
    simpa [hij, hij.symm] using htwo
  · subst v
    have htwo' : 2 ≤ M j i := by rw [hsymm j i]; exact htwo
    simpa [hij, hij.symm] using htwo'

/-- A graph whose edges have original intersection at least one is
acyclic under the canonical discrepancy rows. Its cycle support and its
two neighbors at each vertex are supplied by the original walk. -/
theorem isAcyclic (M : Matrix I I ℚ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hnegative : ∀ x : I → ℚ, x ≠ 0 → dotProduct x (M *ᵥ x) < 0)
    (d : I → ℚ) (hlower : ∀ i, -1 < d i) (hupper : ∀ i, d i ≤ 0)
    (hrow : M *ᵥ d = fun i => -M i i - 2)
    (G : SimpleGraph I) (hedge : ∀ i j, G.Adj i j → 1 ≤ M i j) :
    G.IsAcyclic := by
  classical
  intro v p hp
  let s : Finset I := p.support.toFinset
  have hs : s.Nonempty := ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  apply not_internal_sum_ge_two M hoff hnegative d hlower hupper hrow s hs
  intro i hi
  have hisupport : i ∈ p.support := List.mem_toFinset.mp hi
  obtain ⟨j, l, hjl, hneighbors⟩ := Set.ncard_eq_two.mp
    (hp.ncard_neighborSet_toSubgraph_eq_two hisupport)
  have hj : p.toSubgraph.Adj i j := by
    change j ∈ p.toSubgraph.neighborSet i
    rw [hneighbors]
    simp
  have hl : p.toSubgraph.Adj i l := by
    change l ∈ p.toSubgraph.neighborSet i
    rw [hneighbors]
    simp
  have hjmem : j ∈ s.erase i := Finset.mem_erase.mpr
    ⟨hj.adj_sub.ne.symm,
      List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hj.symm)⟩
  have hlmem : l ∈ s.erase i := Finset.mem_erase.mpr
    ⟨hl.adj_sub.ne.symm,
      List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hl.symm)⟩
  have hsum := Finset.add_le_sum
    (fun z hz => hoff i z (Finset.mem_erase.mp hz).1.symm) hjmem hlmem hjl
  have hjone := hedge i j hj.adj_sub
  have hlone := hedge i l hl.adj_sub
  linarith only [hsum, hjone, hlone]

end KltDP.LinearAlgebra.CanonicalRowForest

#print axioms KltDP.LinearAlgebra.CanonicalRowForest.not_internal_sum_ge_two
#print axioms KltDP.LinearAlgebra.CanonicalRowForest.isAcyclic
