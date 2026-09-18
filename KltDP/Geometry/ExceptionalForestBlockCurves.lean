import KltDP.Geometry.ExceptionalForestClosedBlocks
import KltDP.Geometry.RationalTreePicardDualGraphTransport
import KltDP.Geometry.MinimalResolutionCount

/-!
# The original prime curves are exactly the components of their closed block

Each original exceptional curve in one graph component lifts into the actual
reduced block defined by its vanishing ideal. These closed immersions cover
the block, with incomparable ranges. The resulting component equivalence
identifies the intrinsic component intersection graph with the induced
original exceptional graph; a global forest therefore gives a block tree.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

open KltDP.Topology RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (b : (ActualExceptionalIncidence.graph π).ConnectedComponent)

theorem prime_subset_blockSupport (E : b.supp) :
    (E.val.val : Set S.toScheme) ⊆ blockSupport π b :=
  Set.subset_iUnion (fun F : b.supp => (F.val.val : Set S.toScheme)) E

theorem blockIdeal_le_primeKernel (E : b.supp) :
    blockIdeal π hbir b ≤ E.val.val.inclusion.ker := by
  refine le_trans ?_ (vanishingIdeal_le_ker E.val.val.inclusion
    E.val.val.closedSubset E.val.val.range_inclusion.symm)
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (prime_subset_blockSupport π b E)

/-- The original reduced prime scheme, mapped into its actual closed block. -/
def blockCurve (E : b.supp) : E.val.val.toScheme ⟶ blockScheme π hbir b :=
  liftGluedTo (blockIdeal π hbir b) E.val.val.inclusion (blockIdeal_le_primeKernel π hbir b E)

@[reassoc]
theorem blockCurve_inclusion (E : b.supp) :
    blockCurve π hbir b E ≫ blockInclusion π hbir b = E.val.val.inclusion :=
  liftGluedTo_gluedTo _ _ _

instance blockCurve_isClosedImmersion (E : b.supp) :
    IsClosedImmersion (blockCurve π hbir b E) := by
  letI : IsClosedImmersion (blockCurve π hbir b E ≫ blockInclusion π hbir b) := by
    rw [blockCurve_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (blockInclusion π hbir b)

theorem range_blockCurve (E : b.supp) :
    Set.range (blockCurve π hbir b E).base =
      (blockInclusion π hbir b).base ⁻¹' (E.val.val : Set S.toScheme) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (blockCurve π hbir b E ≫ blockInclusion π hbir b).base y ∈ (E.val.val : Set S.toScheme)
    rw [blockCurve_inclusion, ← E.val.val.range_inclusion]
    exact Set.mem_range_self y
  · intro hx
    have hx' : (blockInclusion π hbir b).base x ∈ Set.range E.val.val.inclusion.base := by
      rw [E.val.val.range_inclusion]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, (blockInclusion π hbir b).isClosedEmbedding.injective ?_⟩
    change (blockCurve π hbir b E ≫ blockInclusion π hbir b).base y = _
    rw [blockCurve_inclusion]
    exact hy

theorem blockCurve_cover :
    ⋃ E : b.supp, Set.range (blockCurve π hbir b E).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (blockInclusion π hbir b).base x ∈ blockSupport π b := by
    rw [← range_blockInclusion]
    exact Set.mem_range_self x
  obtain ⟨E, hE⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨E, (range_blockCurve π hbir b E).symm ▸ hE⟩

theorem blockCurve_incomparable (E F : b.supp)
    (h : Set.range (blockCurve π hbir b E).base ⊆
      Set.range (blockCurve π hbir b F).base) : E = F := by
  have hEF : (E.val.val : Set S.toScheme) ⊆ F.val.val := by
    intro x hx
    have hx' : x ∈ Set.range E.val.val.inclusion.base := by
      rwa [E.val.val.range_inclusion]
    obtain ⟨y, rfl⟩ := hx'
    have hy := h (Set.mem_range_self (f := (blockCurve π hbir b E).base) y)
    rw [range_blockCurve] at hy
    change (blockCurve π hbir b E ≫ blockInclusion π hbir b).base y ∈ (F.val.val : Set S.toScheme) at hy
    rwa [blockCurve_inclusion] at hy
  apply Subtype.ext
  apply Subtype.ext
  exact NormalProjectiveSurface.PrimeCurve.ext
    (E.val.val.coe_eq_of_subset_irreducibleCloseds F.val.val.1 hEF F.val.val.ne_univ)

/-- Actual irreducible components, with the original prime schemes retained. -/
def blockComponentEquiv : b.supp ≃ ↥(irreducibleComponents (blockScheme π hbir b)) := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI : Fintype b.supp := Fintype.ofFinite _
  exact curveComponentEquiv (blockScheme π hbir b) (fun E : b.supp => E.val.val.toScheme)
    (blockCurve π hbir b) (fun _ => inferInstance) (blockCurve_cover π hbir b)
    (blockCurve_incomparable π hbir b)

theorem blockComponentEquiv_val (E : b.supp) :
    (blockComponentEquiv π hbir b E).val = Set.range (blockCurve π hbir b E).base := rfl

theorem blockComponent_inter_nonempty_iff (E F : b.supp) :
    ((blockComponentEquiv π hbir b E).val ∩
      (blockComponentEquiv π hbir b F).val).Nonempty ↔
    ((E.val.val : Set S.toScheme) ∩ F.val.val).Nonempty := by
  rw [blockComponentEquiv_val, blockComponentEquiv_val, range_blockCurve,
    range_blockCurve, ← Set.preimage_inter]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(blockInclusion π hbir b).base x, hx⟩
  · rintro ⟨x, hxE, hxF⟩
    have hx : x ∈ Set.range (blockInclusion π hbir b).base := by
      rw [range_blockInclusion]
      exact prime_subset_blockSupport π b E hxE
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, hxE, hxF⟩

/-- The component graph is the induced graph on the original exceptional primes. -/
def blockComponentGraphIso : (ActualExceptionalIncidence.graph π).induce b.supp ≃g
    incidenceGraph (fun C : ↥(irreducibleComponents (blockScheme π hbir b)) => C.val) :=
  { blockComponentEquiv π hbir b with
    map_rel_iff' := by
      intro E F
      change ((blockComponentEquiv π hbir b E ≠ blockComponentEquiv π hbir b F) ∧
        ((blockComponentEquiv π hbir b E).val ∩
          (blockComponentEquiv π hbir b F).val).Nonempty) ↔
        (E.val ≠ F.val ∧ ((E.val.val : Set S.toScheme) ∩ F.val.val).Nonempty)
      rw [blockComponent_inter_nonempty_iff]
      exact and_congr (by simp only [ne_eq, Equiv.apply_eq_iff_eq, Subtype.val_inj]) Iff.rfl }

include hbir in
theorem blockComponentGraph_isTree (hforest : (ActualExceptionalIncidence.graph π).IsAcyclic) :
    (incidenceGraph
      (fun C : ↥(irreducibleComponents (blockScheme π hbir b)) => C.val)).IsTree := by
  apply isTree_of_iso (blockComponentGraphIso π hbir b).symm
  refine ⟨b.connected_induce_supp, ?_⟩
  let j : (ActualExceptionalIncidence.graph π).induce b.supp →g
      ActualExceptionalIncidence.graph π :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  intro x p hp
  exact hforest (p.map j) (hp.map Subtype.val_injective)

end KltDP.Geometry.ExceptionalForestClosedBlocks

#check @KltDP.Geometry.ExceptionalForestClosedBlocks.blockCurve
#check @KltDP.Geometry.ExceptionalForestClosedBlocks.blockComponentEquiv
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.blockComponentGraph_isTree
