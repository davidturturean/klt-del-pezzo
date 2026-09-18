import KltDP.Geometry.ActualExceptionalIncidence
import KltDP.Geometry.RationalTreePicardOfConfiguration
import KltDP.Geometry.ClosedPartitionUnitTriviality
import KltDP.Geometry.PositiveSquareNefNullLocusScheme

/-!
# Original reduced exceptional blocks inside the actual null scheme

Graph components select literal finite unions of original contracted primes.
Their original radical vanishing ideals define the blocks. Equality of the
original null locus with the full exceptional support constructs the block
maps into that same null scheme. Frames on these actual blocks then glue.
The rational-tree proof producing the block frames is separate.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

open KltDP.Topology

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme)

/-- One connected block of the original exceptional prime incidence graph. -/
def blockSupport (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    Set S.toScheme :=
  IncidenceGraphComponents.block
    (fun E : ActualExceptionalIncidence.Vertices π => (E.val : Set S.toScheme)) c

theorem blockSupport_subset_primeSupport
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    blockSupport π c ⊆ ActualExceptionalLocus.primeSupport π := by
  rw [← ActualExceptionalIncidence.union_eq_primeSupport π]
  exact IncidenceGraphComponents.block_subset_union _ c

theorem blockSupport_disjoint :
    Pairwise (fun c d : (ActualExceptionalIncidence.graph π).ConnectedComponent =>
      Disjoint (blockSupport π c) (blockSupport π d)) :=
  IncidenceGraphComponents.blocks_disjoint _

variable [IsProper π] (hbir : IsBirationalScheme π)

include hbir in
theorem components_finite :
    Finite (ActualExceptionalIncidence.graph π).ConnectedComponent := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  exact IncidenceGraphComponents.finite_graphComponents
    (fun E : ActualExceptionalIncidence.Vertices π => (E.val : Set S.toScheme))

include hbir

theorem blockSupport_isClosed
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    IsClosed (blockSupport π c) := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  exact isClosed_iUnion_of_finite (fun E : c.supp => E.val.val.isClosed)

/-- The block is the original reduced closed subscheme of its literal support. -/
def blockIdeal (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    S.toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨blockSupport π c, blockSupport_isClosed π hbir c⟩

def blockScheme (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) : Scheme.{u} :=
  (blockIdeal π hbir c).glueData.glued

def blockInclusion (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    blockScheme π hbir c ⟶ S.toScheme := (blockIdeal π hbir c).gluedTo

instance blockInclusion_isClosedImmersion
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    IsClosedImmersion (blockInclusion π hbir c) := inferInstanceAs
      (IsClosedImmersion (blockIdeal π hbir c).gluedTo)

instance blockScheme_isReduced
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    AlgebraicGeometry.IsReduced (blockScheme π hbir c) := by
  exact (blockIdeal π hbir c).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := blockIdeal π hbir c)).symm

instance blockScheme_noetherianSpace
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    NoetherianSpace (blockScheme π hbir c) :=
  (blockInclusion π hbir c).isClosedEmbedding.isInducing.noetherianSpace

instance blockScheme_isLocallyNoetherian
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    IsLocallyNoetherian (blockScheme π hbir c) := by
  letI : LocallyOfFiniteType S.structureMorphism := S.projective.locallyOfFiniteType
  exact isLocallyNoetherian_of_locallyOfFiniteType_toSpec
    (blockInclusion π hbir c ≫ S.structureMorphism)

theorem range_blockInclusion
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    Set.range (blockInclusion π hbir c).base = blockSupport π c :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨blockSupport π c, blockSupport_isClosed π hbir c⟩).range_gluedTo

variable (L : InvertibleSheaf S.toScheme)
  (hnull : Positivity.nullLocus S.structureMorphism L = ActualExceptionalLocus.primeSupport π)

include hnull in
theorem nullIdeal_le_blockKernel
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    Scheme.IdealSheafData.vanishingIdeal (Positivity.nullLocusClosed S.structureMorphism L) ≤
      (blockInclusion π hbir c).ker := by
  apply le_trans (b := blockIdeal π hbir c)
  · apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change blockSupport π c ⊆ Positivity.nullLocus S.structureMorphism L
    rw [hnull]
    exact blockSupport_subset_primeSupport π c
  · exact RationalTreePicard.vanishingIdeal_le_ker (blockInclusion π hbir c)
      ⟨blockSupport π c, blockSupport_isClosed π hbir c⟩ (range_blockInclusion π hbir c).symm

def blockToNull (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    blockScheme π hbir c ⟶ Positivity.nullLocusScheme S.structureMorphism L :=
  RationalTreePicard.liftGluedTo
    (Scheme.IdealSheafData.vanishingIdeal (Positivity.nullLocusClosed S.structureMorphism L))
    (blockInclusion π hbir c) (nullIdeal_le_blockKernel π hbir L hnull c)

@[reassoc]
theorem blockToNull_inclusion (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    blockToNull π hbir L hnull c ≫ Positivity.nullLocusInclusion S.structureMorphism L =
      blockInclusion π hbir c :=
  RationalTreePicard.liftGluedTo_gluedTo _ _ _

instance blockToNull_isClosedImmersion
    (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    IsClosedImmersion (blockToNull π hbir L hnull c) := by
  letI : IsClosedImmersion
      (blockToNull π hbir L hnull c ≫ Positivity.nullLocusInclusion S.structureMorphism L) := by
    rw [blockToNull_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp _ (Positivity.nullLocusInclusion S.structureMorphism L)

theorem range_blockToNull (c : (ActualExceptionalIncidence.graph π).ConnectedComponent) :
    Set.range (blockToNull π hbir L hnull c).base =
      (Positivity.nullLocusInclusion S.structureMorphism L).base ⁻¹' blockSupport π c := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (blockToNull π hbir L hnull c ≫
      Positivity.nullLocusInclusion S.structureMorphism L).base y ∈ blockSupport π c
    rw [blockToNull_inclusion, ← range_blockInclusion]
    exact Set.mem_range_self y
  · intro hx
    have hx' : (Positivity.nullLocusInclusion S.structureMorphism L).base x ∈
        Set.range (blockInclusion π hbir c).base := by
      rw [range_blockInclusion]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, (Positivity.nullLocusInclusion S.structureMorphism L).isClosedEmbedding.injective ?_⟩
    change (blockToNull π hbir L hnull c ≫
      Positivity.nullLocusInclusion S.structureMorphism L).base y = _
    rw [blockToNull_inclusion]
    exact hy

/-- Frames on the original connected exceptional blocks give a frame on the
whole original null restriction, via the actual finite disjoint closed cover. -/
def nullRestrictionUnitIsoOfBlocks
    (e : ∀ c : (ActualExceptionalIncidence.graph π).ConnectedComponent,
      (pullbackInvertibleSheaf (blockInclusion π hbir c) L).obj ≅
        _root_.SheafOfModules.unit (blockScheme π hbir c).ringCatSheaf) :
    (Positivity.nullLocusRestrict S.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit (Positivity.nullLocusScheme S.structureMorphism L).ringCatSheaf := by
  classical
  letI : Finite (ActualExceptionalIncidence.graph π).ConnectedComponent :=
    components_finite π hbir
  let Y := fun c : (ActualExceptionalIncidence.graph π).ConnectedComponent => blockScheme π hbir c
  let i := fun c : (ActualExceptionalIncidence.graph π).ConnectedComponent => blockToNull π hbir L hnull c
  have hdisj : ∀ c d, c ≠ d → Disjoint (Set.range (i c).base) (Set.range (i d).base) := by
    intro c d hcd
    rw [range_blockToNull, range_blockToNull]
    exact (blockSupport_disjoint π hcd).preimage _
  have hcover : ∀ x, ∃ c, x ∈ Set.range (i c).base := by
    intro x
    have hx := Set.mem_range_self (f := (Positivity.nullLocusInclusion S.structureMorphism L).base) x
    rw [PositiveSquareNefNullLocusScheme.range_inclusion, hnull] at hx
    obtain ⟨E, hE, hxE⟩ := (ActualExceptionalLocus.mem_primeSupport π _).mp hx
    let F : ActualExceptionalIncidence.Vertices π := ⟨E, hE⟩
    refine ⟨(ActualExceptionalIncidence.graph π).connectedComponentMk F, ?_⟩
    rw [range_blockToNull]
    exact Set.mem_iUnion.mpr ⟨⟨F, rfl⟩, hxE⟩
  refine ClosedPartitionUnitTriviality.unitIsoOfClosedPartition Y i hdisj hcover
    (Positivity.nullLocusRestrict S.structureMorphism L) (fun c => ?_)
  exact (schemeModulePullbackCompIso (i c)
    (Positivity.nullLocusInclusion S.structureMorphism L)).app L.obj ≪≫
      eqToIso (congrArg (fun f => (schemeModulePullback f).obj L.obj)
        (blockToNull_inclusion π hbir L hnull c)) ≪≫ e c

end KltDP.Geometry.ExceptionalForestClosedBlocks

#check @KltDP.Geometry.ExceptionalForestClosedBlocks.blockScheme
#check @KltDP.Geometry.ExceptionalForestClosedBlocks.nullRestrictionUnitIsoOfBlocks
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.nullRestrictionUnitIsoOfBlocks
