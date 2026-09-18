import KltDP.Geometry.ExceptionalForestClosedBlocks

/-! The original reduced exceptional block has dimension at most one. -/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- The original reduced block has the subspace topology of its literal union. -/
def blockHomeomorph (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    blockScheme π hbir c ≃ₜ blockSupport π c :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨blockSupport π c, blockSupport_isClosed π hbir c⟩).gluedSupportHomeomorph

/-- No original exceptional prime contains the generic point of the surface. -/
theorem genericPoint_not_mem_block
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    _root_.genericPoint S.toScheme ∉ blockSupport π c := by
  intro hx
  obtain ⟨E, hxE⟩ := Set.mem_iUnion.mp hx
  have hsubset : closure ({_root_.genericPoint S.toScheme} : Set S.toScheme) ⊆
      (E.val.val : Set S.toScheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hxE) E.val.val.isClosed
  rw [genericPoint_closure] at hsubset
  exact E.val.val.ne_univ (Set.eq_univ_of_univ_subset hsubset)

theorem blockSupport_ne_univ
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    blockSupport π c ≠ Set.univ := by
  intro h
  apply genericPoint_not_mem_block π c
  rw [h]
  exact Set.mem_univ _

/-- The dimension bound is on the same actual block scheme used for restriction. -/
theorem blockScheme_dimension_le_one
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    topologicalKrullDim (blockScheme π hbir c) ≤ 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq (blockHomeomorph π hbir c)
    (blockHomeomorph π hbir c).isHomeomorph]
  exact KltDP.Topology.topologicalKrullDim_le_one_of_isClosed_of_ne_univ
    S.dimension_two.le (blockSupport_isClosed π hbir c) (blockSupport_ne_univ π c)

end KltDP.Geometry.ExceptionalForestClosedBlocks

#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.blockScheme_dimension_le_one
