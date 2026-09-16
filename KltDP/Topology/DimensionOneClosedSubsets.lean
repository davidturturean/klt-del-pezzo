import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Basic

/-!
# Proper closed subsets of a one-dimensional irreducible Noetherian space

In an irreducible space of topological Krull dimension at most one, every proper
irreducible closed subset is minimal among irreducible closed subsets
(`Order.krullDim_le_one_iff`), hence is the closure of each of its points; in a
`T₀` space it is therefore a single closed point. A proper closed subset of an
irreducible Noetherian space of dimension at most one is a finite union of such
irreducible closed subsets, so it is a finite set of closed points.

This is the chain argument behind the finiteness of `C ∩ Supp D` for a prime curve
`C ⊄ Supp D`; the scheme-theoretic application is in
`KltDP.Geometry.PrimeCurveIntersectionFinite`.
-/

namespace KltDP.Topology

open TopologicalSpace

variable {Y : Type*} [TopologicalSpace Y] [IrreducibleSpace Y]

/-- In dimension at most one, a proper irreducible closed subset is the closure of each of
its points. -/
theorem eq_closure_singleton_of_isIrreducible_of_isClosed_of_ne_univ
    (hdim : topologicalKrullDim Y ≤ 1) {Z : Set Y} (hZ : IsIrreducible Z) (hZc : IsClosed Z)
    (hne : Z ≠ Set.univ) {z : Y} (hz : z ∈ Z) : Z = closure {z} := by
  have hmin : IsMin (⟨Z, hZ, hZc⟩ : IrreducibleCloseds Y) := by
    rcases (Order.krullDim_le_one_iff.mp hdim) ⟨Z, hZ, hZc⟩ with h | h
    · exact h
    · exfalso
      have hle : (⟨Z, hZ, hZc⟩ : IrreducibleCloseds Y) ≤
          ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩ :=
        Set.subset_univ _
      exact hne (Set.eq_univ_of_univ_subset (h hle))
  have hle : (⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      IrreducibleCloseds Y) ≤ ⟨Z, hZ, hZc⟩ :=
    hZc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz)
  exact Set.Subset.antisymm (hmin hle) (hZc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz))

/-- In a `T₀` space of dimension at most one, a proper irreducible closed subset is a
singleton. -/
theorem eq_singleton_of_isIrreducible_of_isClosed_of_ne_univ [T0Space Y]
    (hdim : topologicalKrullDim Y ≤ 1) {Z : Set Y} (hZ : IsIrreducible Z) (hZc : IsClosed Z)
    (hne : Z ≠ Set.univ) : ∃ z, Z = {z} := by
  obtain ⟨z, hz⟩ := hZ.nonempty
  refine ⟨z, Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr hz)⟩
  intro z' hz'
  have h1 := eq_closure_singleton_of_isIrreducible_of_isClosed_of_ne_univ hdim hZ hZc hne hz
  have h2 := eq_closure_singleton_of_isIrreducible_of_isClosed_of_ne_univ hdim hZ hZc hne hz'
  exact (inseparable_iff_closure_eq.mpr (h2.symm.trans h1)).eq

/-- A proper closed subset of an irreducible Noetherian `T₀` space of dimension at most one
is a finite set of closed points. -/
theorem finite_and_isClosed_singleton_of_isClosed_of_ne_univ [T0Space Y] [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ 1) {T : Set Y} (hT : IsClosed T) (hne : T ≠ Set.univ) :
    T.Finite ∧ ∀ y ∈ T, IsClosed ({y} : Set Y) := by
  obtain ⟨S, hSf, hSc, hSi, hTS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hsing : ∀ t ∈ S, ∃ z, t = {z} ∧ IsClosed ({z} : Set Y) := by
    intro t ht
    have htT : t ⊆ T := hTS ▸ Set.subset_sUnion_of_mem ht
    have htne : t ≠ Set.univ := fun h => hne (Set.eq_univ_of_univ_subset (h ▸ htT))
    obtain ⟨z, hz⟩ :=
      eq_singleton_of_isIrreducible_of_isClosed_of_ne_univ hdim (hSi t ht) (hSc t ht) htne
    exact ⟨z, hz, hz ▸ hSc t ht⟩
  constructor
  · rw [hTS]
    refine Set.Finite.sUnion hSf fun t ht => ?_
    obtain ⟨z, hz, -⟩ := hsing t ht
    rw [hz]
    exact Set.finite_singleton z
  · intro y hy
    rw [hTS] at hy
    obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.mp hy
    obtain ⟨z, hz, hzc⟩ := hsing t ht
    rw [hz] at hyt
    rw [Set.mem_singleton_iff.mp hyt]
    exact hzc

end KltDP.Topology
