import KltDP.Lattices.SmallADEForestLattice
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Total isolated-vertex cardinality for the small ADE forest table

A full matrix identification with the small ADE count model determines all
isolated vertices of the original graph. The existing transported `A1`
coordinates are not only distinct isolated vertices: they exhaust that set.
Consequently the count `a1` is the total isolated-vertex cardinality.

The argument uses a finite check on each of the five component matrices,
followed by an explicit bijection. No total-cardinality equation is assumed.
The source reuse record is `docs/reuse_sources/small_table_total_parallel/`.
-/

namespace KltDP.Support.SmallTableEightTotal

open Matrix SimpleGraph
open KltDP.Lattices.SmallADEPartitions KltDP.Lattices.SmallADEMatrices
open KltDP.Lattices.SmallADEGraphs KltDP.Lattices.SmallADEForestDecomposition
open KltDP.Lattices.SmallADEForestLattice

/-- Every vertex of a non-singleton component has a matrix entry minus one.
This checks only the four fixed matrices `A2`, `A3`, `A4`, and `D4`. -/
theorem componentMatrix_has_neighbor :
    ∀ k : Kind, k ≠ .a1 → ∀ v : KindVertex k,
      ∃ w : KindVertex k, componentMatrix k v w = (-1 : ℤ) := by
  decide

section Graph

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (counts : Counts) (e : V ≃ Vertex counts)
variable (hGram : (cartanMatrix counts).submatrix e e = graphCartanMatrix G)

include hGram

/-- Every isolated vertex of the original graph is one of the transported
`A1` coordinates. This is the surjectivity missing from a selected-node count. -/
theorem exists_transportedNode_of_not_mem_support (v : V) (hv : v ∉ G.support) :
    ∃ i : Fin counts.a1, transportedNode counts e i = v := by
  rcases hx : e v with ⟨k, w, j⟩
  have hk : k = .a1 := by
    by_contra hk
    obtain ⟨w', hn⟩ := componentMatrix_has_neighbor k hk w
    have hm : cartanMatrix counts (e v) ⟨k, w', j⟩ = -1 := by
      rw [hx]
      simpa [cartanMatrix, repeatedMatrix, Matrix.blockDiagonal_apply] using hn
    have h := congr_fun (congr_fun hGram v) (e.symm ⟨k, w', j⟩)
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at h
    rw [hm, graphCartanMatrix_isolated_row G v hv] at h
    split_ifs at h <;> norm_num at h
  subst k
  have hw : w = (0 : Fin 1) := Subsingleton.elim _ _
  subst w
  refine ⟨j, ?_⟩
  apply e.injective
  simpa only [transportedNode, Equiv.apply_symm_apply, nodeIndex] using hx.symm

/-- Isolation in the original graph is equivalent to membership in the full
image of its transported `A1` coordinates. -/
theorem not_mem_support_iff_exists_transportedNode (v : V) :
    v ∉ G.support ↔ ∃ i : Fin counts.a1, transportedNode counts e i = v := by
  constructor
  · exact exists_transportedNode_of_not_mem_support G counts e hGram v
  · rintro ⟨i, rfl⟩
    exact transportedNode_not_mem_support G counts e hGram i

/-- The existing node selection as a map into the type of all isolated
vertices of the original graph. -/
def isolatedNodeMap (i : Fin counts.a1) : {v : V // v ∉ G.support} :=
  ⟨transportedNode counts e i, transportedNode_not_mem_support G counts e hGram i⟩

/-- The node selection is a bijection onto the entire isolated-vertex type. -/
theorem isolatedNodeMap_bijective :
    Function.Bijective (isolatedNodeMap G counts e hGram) := by
  constructor
  · intro i j hij
    exact transportedNode_injective counts e (congrArg Subtype.val hij)
  · rintro ⟨v, hv⟩
    obtain ⟨i, hi⟩ := exists_transportedNode_of_not_mem_support G counts e hGram v hv
    exact ⟨i, Subtype.ext hi⟩

/-- The total number of isolated vertices is the `A1` multiplicity, with no
finite-type instance or cardinality equation required as a hypothesis. -/
theorem total_isolated_card_eq_a1 :
    Nat.card {v : V // v ∉ G.support} = counts.a1 := by
  have h := Nat.card_eq_of_bijective (isolatedNodeMap G counts e hGram)
    (isolatedNodeMap_bijective G counts e hGram)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h.symm

end Graph

end KltDP.Support.SmallTableEightTotal
