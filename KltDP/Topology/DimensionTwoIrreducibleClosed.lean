import KltDP.Compatibility.GrothendieckVanishing.TopologicalKrullDim

/-!
# Positive-dimensional irreducible closed subsets in dimension two

The existing proper-closed-subspace dimension-drop theorem reduces the
dimension bound from two to one. The discrete order on `WithBot ℕ∞` then
identifies any positive-dimensional proper irreducible closed subset as
one-dimensional. No separation or Noetherian hypothesis is needed.
-/

namespace KltDP.Topology

open TopologicalSpace

variable {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y]

/-- A proper closed subset of an irreducible space of dimension at most two
has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_isClosed_of_ne_univ
    (hdim : topologicalKrullDim Y ≤ 2) {Z : Set Y}
    (hclosed : IsClosed Z) (hne : Z ≠ Set.univ) :
    topologicalKrullDim Z ≤ 1 := by
  have hfin : topologicalKrullDim Z < ⊤ :=
    lt_of_le_of_lt ((topologicalKrullDim_subspace_le Z).trans hdim)
      (WithBot.coe_lt_coe.mpr (ENat.coe_lt_top 2))
  have hlt : topologicalKrullDim Z < 2 :=
    (topologicalKrullDim_lt_of_isIrreducible_of_isClosed hclosed hne hfin).trans_le hdim
  exact (WithBot.lt_add_one_iff (m := 1)).mp (by simpa using hlt)

/-- A positive-dimensional irreducible closed subset is a curve or the
entire ambient space when that irreducible space has dimension at most two. -/
theorem irreducibleClosed_dim_eq_one_or_eq_univ
    (hdim : topologicalKrullDim Y ≤ 2) (Z : IrreducibleCloseds Y)
    (hpositive : 0 < topologicalKrullDim (Z : Set Y)) :
    topologicalKrullDim (Z : Set Y) = 1 ∨ (Z : Set Y) = Set.univ := by
  classical
  by_cases hfull : (Z : Set Y) = Set.univ
  · exact Or.inr hfull
  · exact Or.inl (le_antisymm
      (topologicalKrullDim_le_one_of_isClosed_of_ne_univ hdim Z.isClosed hfull)
      ((WithBot.one_le_iff_pos _).mpr hpositive))

end KltDP.Topology
