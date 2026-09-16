import KltDP.Topology.Dimension

/-!
# Krull dimension bounds from an open cover

A finite chain of irreducible closed sets can be restricted to any open
neighborhood of a point in its first member. Every member meets that open
set, and taking the closure of the restricted member recovers the original.
The restricted chain therefore has the same length.

Consequently a common dimension bound on the members of an actual open
cover bounds the ambient space. The cover need not be finite, and no
separation or Noetherianity assumption is needed.
-/

open TopologicalSpace Topology

universe u v

namespace KltDP.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Restriction of an irreducible closed set to an open set it meets. -/
private def restrictIrreducibleClosed (U : Opens X) (c : IrreducibleCloseds X)
    (h : ((c : Set X) ∩ (U : Set X)).Nonempty) : IrreducibleCloseds U where
  carrier := (Subtype.val : U → X) ⁻¹' (c : Set X)
  is_irreducible' := by
    refine ⟨?_, c.isIrreducible.2.preimage U.isOpenEmbedding'⟩
    obtain ⟨x, hxc, hxU⟩ := h
    exact ⟨⟨x, hxU⟩, hxc⟩
  is_closed' := c.isClosed.preimage continuous_subtype_val

/-- A nonempty open part of an irreducible closed set is dense in that set. -/
private theorem closure_image_restrictIrreducibleClosed
    (U : Opens X) (c : IrreducibleCloseds X)
    (h : ((c : Set X) ∩ (U : Set X)).Nonempty) :
    closure ((Subtype.val : U → X) ''
      (restrictIrreducibleClosed U c h : Set U)) = (c : Set X) := by
  have himage :
      (Subtype.val : U → X) '' (restrictIrreducibleClosed U c h : Set U) =
        (c : Set X) ∩ (U : Set X) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxc, hxU⟩
      exact ⟨⟨x, hxU⟩, hxc, rfl⟩
  rw [himage]
  exact le_antisymm
    (c.isClosed.closure_subset_iff.mpr Set.inter_subset_left)
    (subset_closure_inter_of_isPreirreducible_of_isOpen
      c.isIrreducible.2 U.isOpen h)

/-- Restricting two irreducible closed sets that meet the open set reflects
their inclusion, since closure of the images recovers both sets. -/
private theorem restrictIrreducibleClosed_le_iff
    (U : Opens X) (c d : IrreducibleCloseds X)
    (hc : ((c : Set X) ∩ (U : Set X)).Nonempty)
    (hd : ((d : Set X) ∩ (U : Set X)).Nonempty) :
    restrictIrreducibleClosed U c hc ≤ restrictIrreducibleClosed U d hd ↔ c ≤ d := by
  constructor
  · intro h
    change (c : Set X) ⊆ (d : Set X)
    calc
      (c : Set X) = closure ((Subtype.val : U → X) ''
          (restrictIrreducibleClosed U c hc : Set U)) :=
        (closure_image_restrictIrreducibleClosed U c hc).symm
      _ ⊆ closure ((Subtype.val : U → X) ''
          (restrictIrreducibleClosed U d hd : Set U)) :=
        closure_mono (Set.image_mono h)
      _ = (d : Set X) := closure_image_restrictIrreducibleClosed U d hd
  · intro h
    change (Subtype.val : U → X) ⁻¹' (c : Set X) ⊆
      (Subtype.val : U → X) ⁻¹' (d : Set X)
    exact Set.preimage_mono h

/-- Strict inclusion is also preserved on irreducible closed sets meeting
the open set. -/
private theorem restrictIrreducibleClosed_lt_iff
    (U : Opens X) (c d : IrreducibleCloseds X)
    (hc : ((c : Set X) ∩ (U : Set X)).Nonempty)
    (hd : ((d : Set X) ∩ (U : Set X)).Nonempty) :
    restrictIrreducibleClosed U c hc < restrictIrreducibleClosed U d hd ↔ c < d := by
  simp only [lt_iff_le_not_le, restrictIrreducibleClosed_le_iff]

/-- A common dimension bound on an actual open cover bounds the ambient
space. Each finite chain is restricted to one cover member meeting its
first irreducible closed set, so no finiteness assumption on the cover is
required. -/
theorem topologicalKrullDim_le_of_open_cover {ι : Type v}
    (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (d : WithBot ℕ∞) (hbound : ∀ i, topologicalKrullDim (U i) ≤ d) :
    topologicalKrullDim X ≤ d := by
  classical
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p ↦ ?_
  obtain ⟨x, hx⟩ := (p 0).isIrreducible.1
  obtain ⟨i, hxi⟩ := hcover x
  have hmeet (j : Fin (p.length + 1)) :
      ((p j : Set X) ∩ (U i : Set X)).Nonempty :=
    ⟨x, p.monotone (Fin.zero_le j) hx, hxi⟩
  let q : LTSeries (IrreducibleCloseds (U i)) :=
    LTSeries.mk p.length
      (fun j ↦ restrictIrreducibleClosed (U i) (p j) (hmeet j))
      (by
        intro a b hab
        exact (restrictIrreducibleClosed_lt_iff
          (U i) (p a) (p b) (hmeet a) (hmeet b)).mpr (p.strictMono hab))
  have hlength : (p.length : WithBot ℕ∞) ≤ topologicalKrullDim (U i) :=
    Order.LTSeries.length_le_krullDim q
  exact hlength.trans (hbound i)

end KltDP.Topology
