import KltDP.Geometry.PrimeDivisor
import Mathlib.Tactic

/-!
# Existence of actual prime curves on a surface

This file proves that the existing `PrimeCurve` type is inhabited for every
`NormalProjectiveSurface`. The curve is obtained from the surface's actual
topological Krull dimension, with no assumed curve, divisor or intersection
data. The topological argument applies to every space of dimension two.

The adapter identifies irreducible closed subsets of a closed subspace with
the lower interval in the ambient order of irreducible closed subsets. It
then reuses the pinned Mathlib chain and height theorems. No Noetherian,
normality, projectivity or field hypothesis is needed for this adapter.
The final surface corollary uses the genuine `dimension_two` field.

This proves existence of a prime curve. It does not assert existence of an
exterior curve for a specified exceptional divisor, positivity of a divisor
degree, or any intersection-theoretic statement from the manuscript.
-/

noncomputable section

open TopologicalSpace

universe u v

namespace KltDP.Topology

variable {X : Type u} [TopologicalSpace X]

/-- An ambient irreducible closed subset contained in `Z`, viewed with the
subspace topology on `Z`. -/
def restrictIrreducibleClosed {Z : Set X} (C : IrreducibleCloseds X)
    (hC : (C : Set X) ⊆ Z) : IrreducibleCloseds Z where
  carrier := Subtype.val ⁻¹' (C : Set X)
  is_irreducible' := by
    letI : IrreducibleSpace (C : Set X) := Subtype.irreducibleSpace C.isIrreducible
    simpa only [Set.image_univ, Set.range_inclusion] using
      (IrreducibleSpace.isIrreducible_univ (C : Set X)).image
        (Set.inclusion hC) (continuous_inclusion hC).continuousOn
  is_closed' := C.isClosed.preimage continuous_subtype_val

/-- Irreducible closed subsets of an actual closed subspace are exactly
the ambient irreducible closed subsets lying below it. -/
def irreducibleClosedsIic (Z : IrreducibleCloseds X) :
    IrreducibleCloseds (Z : Set X) ≃o Set.Iic Z where
  toFun C :=
    ⟨IrreducibleCloseds.map continuous_subtype_val
      Z.isClosed.isClosedMap_subtype_val C, by
        rintro x ⟨y, hy, rfl⟩
        exact y.property⟩
  invFun C := restrictIrreducibleClosed C.val C.property
  left_inv C := by
    apply IrreducibleCloseds.ext
    exact Set.preimage_image_eq _ Subtype.val_injective
  right_inv C := by
    apply Subtype.ext
    apply IrreducibleCloseds.ext
    exact Subtype.coe_image_of_subset C.property
  map_rel_iff' := by
    intro C D
    exact Set.image_subset_image_iff Subtype.val_injective

/-- The subspace dimension of an irreducible closed subset is its height
in the ambient order of irreducible closed subsets. -/
theorem topologicalKrullDim_irreducibleClosed_eq_height (Z : IrreducibleCloseds X) :
    topologicalKrullDim (Z : Set X) = (Order.height Z : WithBot ℕ∞) :=
  (Order.krullDim_eq_of_orderIso (irreducibleClosedsIic Z)).trans
    (Order.height_eq_krullDim_Iic Z).symm

/-- Every topological space of dimension two contains an actual
irreducible closed subspace of dimension one. -/
theorem exists_irreducibleClosed_dimension_one
    (hdim : topologicalKrullDim X = 2) :
    ∃ Z : IrreducibleCloseds X, topologicalKrullDim (Z : Set X) = 1 := by
  have hdim' : Order.krullDim (IrreducibleCloseds X) = 2 := hdim
  obtain ⟨p, hlen⟩ :=
    (Order.le_krullDim_iff (α := IrreducibleCloseds X) (n := 2)).mp hdim'.ge
  have hlast_upper : Order.height p.last ≤ (2 : ℕ∞) := by
    have h := Order.height_le_krullDim p.last
    rw [hdim'] at h
    exact WithBot.coe_le_coe.mp h
  have hlast_lower : (2 : ℕ∞) ≤ Order.height p.last := by
    simpa only [hlen] using (Order.length_le_height_last (p := p))
  have hlast : Order.height p.last = (2 : ℕ∞) :=
    le_antisymm hlast_upper hlast_lower
  have hlength : (p.length : ℕ∞) = Order.height p.last := by
    simpa only [hlen] using hlast.symm
  let i : Fin (p.length + 1) := ⟨1, by omega⟩
  refine ⟨p i, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed_eq_height,
    Order.height_eq_index_of_length_eq_height_last hlength i]
  simp [i]

end KltDP.Topology

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type v} [Field k]

/-- Every normal projective surface has a prime curve in the existing
geometric sense: an actual irreducible closed subset of dimension one. -/
theorem primeCurve_nonempty (X : NormalProjectiveSurface k) : Nonempty X.PrimeCurve := by
  obtain ⟨Z, hZ⟩ := KltDP.Topology.exists_irreducibleClosed_dimension_one X.dimension_two
  exact ⟨⟨Z, hZ⟩⟩

end KltDP.Geometry.NormalProjectiveSurface
