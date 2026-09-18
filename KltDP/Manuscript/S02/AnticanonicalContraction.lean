import KltDP.Geometry.ExceptionalForestClosedBlocks
import KltDP.Geometry.ExceptionalForestBlockCurves
import KltDP.Geometry.ExceptionalForestBlockDimension
import KltDP.Geometry.KltExceptionalBlockTransversal
import KltDP.Geometry.KltExceptionalBlockTree
import KltDP.Geometry.KltExceptionalNullRestriction
import KltDP.Geometry.NefPositiveSquareKeelRestriction
import KltDP.Geometry.PositiveSquareNefNullLocus
import KltDP.Geometry.SemiampleLargePower
import KltDP.Geometry.GeneratedCompleteSystemNormalSurface
import KltDP.Geometry.GeneratedCompleteSystemNormalAmple
import KltDP.Geometry.NormalFactorPrimeCurveCriterion
import KltDP.Geometry.ProperSteinConnected
import KltDP.Geometry.ExceptionalCurveFieldPointFactor
import KltDP.Geometry.ExceptionalCurveOfFieldPointFactor
import KltDP.Geometry.BirationalNumericalPullback
import KltDP.Geometry.NullCurveIntersectionMatrix
import KltDP.Geometry.NullCurveIndependenceRank
import KltDP.Geometry.NefNullCurveNegativeSquare
import KltDP.Geometry.SurfaceNumericalFinitenessProved
import KltDP.Geometry.RationalWeilIntersectionFamily
import KltDP.Geometry.QCartierBirationalPushforward
import KltDP.Geometry.BirationalWeilClassPushforward
import KltDP.Geometry.BirationalCartierPullbackPushforward
import KltDP.Geometry.BirationalPicardIntersectionPullback
import KltDP.Geometry.QCartierFromPicardClass
import KltDP.Geometry.AmpleCartierFromWeilClass
import KltDP.Geometry.CanonicalCartierRepresentativePushforward
import KltDP.Geometry.CanonicalWeilOfCartier
import KltDP.Geometry.CanonicalWeilClassIndependent
import KltDP.Geometry.TargetIsomorphismOpen
import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.SmoothStructureOnIsomorphismOpen
import KltDP.Geometry.OpenCartierWeilPrincipal
import KltDP.Geometry.CartierModuleIsoOfPicardClass
import KltDP.Geometry.NormalModelKltOfSNC
import KltDP.Geometry.FiniteSmoothCurveSumSNC
import KltDP.Geometry.DelPezzoType
import KltDP.Geometry.RationalCurveSmooth
import KltDP.Geometry.PrimeCurveIntersectionOneCrossing
import KltDP.Geometry.ActualExceptionalNoTriple
import KltDP.Geometry.SchemeKernelIdealIsoTransport
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Manuscript Theorem 2.6: anticanonical contraction to a rank-one klt del Pezzo surface

Source: `source/manuscript.tex`, lines 491–558, label `thm:anticanonical-contraction`.

`T` is a smooth projective surface (a `NormalProjectiveSurface` all of whose points are regular),
`G : ι → T.PrimeCurve` an injective finite family of smooth rational curves (`hrat`), forming a
simple-normal-crossing forest: the incidence graph `curveIncidenceGraph G` is acyclic and two
distinct members meet with intersection number at most one (`hpair`; with `hrat` this is the
manuscript's "SNC forest": transversality and the SNC property of the reduced sum are *derived*
from the union's `PrimeCurveIntersectionOneCrossing` and `finite_smooth_primeCurve_sum_isStrictNormalCrossings`).
`card ι + 1 = ρ(T)`, `λ_i < 1`, `H = -(K_T + Σ λ_i G_i)`, cleared by `m H = Hm` with `Hm` an actual
Cartier divisor (`hHm`); `(i)` `Hm` nef with `Hm² > 0` (bigness of a nef divisor on a surface);
`(ii)` `Hm · C = 0 ↔ C ∈ {G_i}`.

The proof follows the manuscript and the union's Frobenius pipeline: Lemma 2.2 (rational trees,
through the union's `RationalTreePicard` block machinery, ported here from the exceptional-locus
version to an arbitrary injective family), Keel's theorem (the admitted literal
`KltDP.Literature.Keel.semiampleness_completeSystem_literal`, through
`NefPositiveSquareKeelRestriction`), the Stein factorisation of the complete-system map
(`GeneratedCompleteSystemNormalFactor`), the numerical-rank computation, the canonical descent
`K_T + B = f^*K_Y` (negative definiteness of the intersection matrix of the `G_i`), and the
all-normal-model klt criterion `isKltWithCanonicalDivisor_of_snc_discrepancy`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Matrix
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open InvertibleSheafSectionPowers
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

universe u

namespace KltDP.Manuscript.S02

/-! ## Two `Finsupp` evaluation lemmas for sums of singletons over an injective family -/

theorem sum_single_apply_eq {ι α R : Type*} [Fintype ι] [AddCommMonoid R]
    (G : ι → α) (hinj : Function.Injective G) (c : ι → R) (i₀ : ι) :
    (∑ i, Finsupp.single (G i) (c i)) (G i₀) = c i₀ := by
  classical
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i₀]
  · simp
  · intro j _ hj
    exact Finsupp.single_eq_of_ne (fun h => hj (hinj h))
  · intro h
    exact absurd (Finset.mem_univ i₀) h

theorem sum_single_apply_of_not {ι α R : Type*} [Fintype ι] [AddCommMonoid R]
    (G : ι → α) (c : ι → R) (C : α) (hC : ∀ i, C ≠ G i) :
    (∑ i, Finsupp.single (G i) (c i)) C = 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact Finsupp.single_eq_of_ne (fun h => hC j h.symm)

/-! ## Forest blocks

The union's `ExceptionalForestClosedBlocks` machinery is indexed by the exceptional curves of a
resolution `π`.  Here the same construction is carried out for an arbitrary injective finite family
`G : ι → T.PrimeCurve`: the reduced closed subscheme on the union of the curves of one connected
component of the incidence graph is a rational tree (transversal configuration, tree
component-point graph), so a line bundle of degree zero on every `G i` is trivial on it, and the
finite disjoint closed cover then trivialises the line bundle on the whole null locus. -/

namespace ForestBlocks

set_option linter.unusedSectionVars false

open KltDP.Topology KltDP.Geometry.RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] {T : NormalProjectiveSurface k}
  {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve)

/-- The incidence graph of the family (edges = nonempty intersections). -/
abbrev graph : SimpleGraph ι := curveIncidenceGraph G

/-- The literal union of the curves in one connected component of the incidence graph. -/
def blockSupport (c : (graph G).ConnectedComponent) : Set T.toScheme :=
  IncidenceGraphComponents.block (fun i => (G i : Set T.toScheme)) c

theorem blockSupport_subset_union (c : (graph G).ConnectedComponent) :
    blockSupport G c ⊆ ⋃ i, (G i : Set T.toScheme) :=
  IncidenceGraphComponents.block_subset_union _ c

theorem blockSupport_disjoint :
    Pairwise (fun c d : (graph G).ConnectedComponent =>
      Disjoint (blockSupport G c) (blockSupport G d)) :=
  IncidenceGraphComponents.blocks_disjoint _

theorem components_finite : Finite (graph G).ConnectedComponent :=
  IncidenceGraphComponents.finite_graphComponents (fun i => (G i : Set T.toScheme))

theorem blockSupport_isClosed (c : (graph G).ConnectedComponent) :
    IsClosed (blockSupport G c) :=
  isClosed_iUnion_of_finite (fun i : c.supp => (G i.val).isClosed)

/-- The block is the reduced closed subscheme of its literal support. -/
def blockIdeal (c : (graph G).ConnectedComponent) : T.toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨blockSupport G c, blockSupport_isClosed G c⟩

def blockScheme (c : (graph G).ConnectedComponent) : Scheme.{u} :=
  (blockIdeal G c).glueData.glued

def blockInclusion (c : (graph G).ConnectedComponent) : blockScheme G c ⟶ T.toScheme :=
  (blockIdeal G c).gluedTo

instance blockInclusion_isClosedImmersion (c : (graph G).ConnectedComponent) :
    IsClosedImmersion (blockInclusion G c) :=
  inferInstanceAs (IsClosedImmersion (blockIdeal G c).gluedTo)

instance blockScheme_isReduced (c : (graph G).ConnectedComponent) :
    AlgebraicGeometry.IsReduced (blockScheme G c) :=
  (blockIdeal G c).glued_isReduced
    (Scheme.IdealSheafData.vanishingIdeal_support (I := blockIdeal G c)).symm

instance blockScheme_noetherianSpace (c : (graph G).ConnectedComponent) :
    NoetherianSpace (blockScheme G c) :=
  (blockInclusion G c).isClosedEmbedding.isInducing.noetherianSpace

instance blockScheme_isLocallyNoetherian (c : (graph G).ConnectedComponent) :
    IsLocallyNoetherian (blockScheme G c) := by
  letI : LocallyOfFiniteType T.structureMorphism := T.projective.locallyOfFiniteType
  exact isLocallyNoetherian_of_locallyOfFiniteType_toSpec
    (blockInclusion G c ≫ T.structureMorphism)

theorem range_blockInclusion (c : (graph G).ConnectedComponent) :
    Set.range (blockInclusion G c).base = blockSupport G c :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨blockSupport G c, blockSupport_isClosed G c⟩).range_gluedTo

section NullLocus

variable (L : InvertibleSheaf T.toScheme)
  (hnull : Positivity.nullLocus T.structureMorphism L = ⋃ i, (G i : Set T.toScheme))

include hnull in
theorem nullIdeal_le_blockKernel (c : (graph G).ConnectedComponent) :
    Scheme.IdealSheafData.vanishingIdeal (Positivity.nullLocusClosed T.structureMorphism L) ≤
      (blockInclusion G c).ker := by
  apply le_trans (b := blockIdeal G c)
  · apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change blockSupport G c ⊆ Positivity.nullLocus T.structureMorphism L
    rw [hnull]
    exact blockSupport_subset_union G c
  · exact vanishingIdeal_le_ker (blockInclusion G c)
      ⟨blockSupport G c, blockSupport_isClosed G c⟩ (range_blockInclusion G c).symm

def blockToNull (c : (graph G).ConnectedComponent) :
    blockScheme G c ⟶ Positivity.nullLocusScheme T.structureMorphism L :=
  liftGluedTo
    (Scheme.IdealSheafData.vanishingIdeal (Positivity.nullLocusClosed T.structureMorphism L))
    (blockInclusion G c) (nullIdeal_le_blockKernel G L hnull c)

@[reassoc]
theorem blockToNull_inclusion (c : (graph G).ConnectedComponent) :
    blockToNull G L hnull c ≫ Positivity.nullLocusInclusion T.structureMorphism L =
      blockInclusion G c :=
  liftGluedTo_gluedTo _ _ _

instance blockToNull_isClosedImmersion (c : (graph G).ConnectedComponent) :
    IsClosedImmersion (blockToNull G L hnull c) := by
  letI : IsClosedImmersion
      (blockToNull G L hnull c ≫ Positivity.nullLocusInclusion T.structureMorphism L) := by
    rw [blockToNull_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp _ (Positivity.nullLocusInclusion T.structureMorphism L)

theorem range_blockToNull (c : (graph G).ConnectedComponent) :
    Set.range (blockToNull G L hnull c).base =
      (Positivity.nullLocusInclusion T.structureMorphism L).base ⁻¹' blockSupport G c := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (blockToNull G L hnull c ≫
      Positivity.nullLocusInclusion T.structureMorphism L).base y ∈ blockSupport G c
    rw [blockToNull_inclusion, ← range_blockInclusion]
    exact Set.mem_range_self y
  · intro hx
    have hx' : (Positivity.nullLocusInclusion T.structureMorphism L).base x ∈
        Set.range (blockInclusion G c).base := by
      rw [range_blockInclusion]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, (Positivity.nullLocusInclusion T.structureMorphism L).isClosedEmbedding.injective ?_⟩
    change (blockToNull G L hnull c ≫
      Positivity.nullLocusInclusion T.structureMorphism L).base y = _
    rw [blockToNull_inclusion]
    exact hy

/-- Frames on the blocks give a frame on the whole null restriction, via the finite disjoint
closed cover. -/
def nullRestrictionUnitIsoOfBlocks
    (e : ∀ c : (graph G).ConnectedComponent,
      (pullbackInvertibleSheaf (blockInclusion G c) L).obj ≅
        _root_.SheafOfModules.unit (blockScheme G c).ringCatSheaf) :
    (Positivity.nullLocusRestrict T.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit (Positivity.nullLocusScheme T.structureMorphism L).ringCatSheaf := by
  classical
  letI : Finite (graph G).ConnectedComponent := components_finite G
  let Y := fun c : (graph G).ConnectedComponent => blockScheme G c
  let i := fun c : (graph G).ConnectedComponent => blockToNull G L hnull c
  have hdisj : ∀ c d, c ≠ d → Disjoint (Set.range (i c).base) (Set.range (i d).base) := by
    intro c d hcd
    rw [range_blockToNull, range_blockToNull]
    exact (blockSupport_disjoint G hcd).preimage _
  have hcover : ∀ x, ∃ c, x ∈ Set.range (i c).base := by
    intro x
    have hx := Set.mem_range_self
      (f := (Positivity.nullLocusInclusion T.structureMorphism L).base) x
    rw [PositiveSquareNefNullLocusScheme.range_inclusion, hnull] at hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    refine ⟨(graph G).connectedComponentMk j, ?_⟩
    rw [range_blockToNull]
    exact Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, hxj⟩
  refine ClosedPartitionUnitTriviality.unitIsoOfClosedPartition Y i hdisj hcover
    (Positivity.nullLocusRestrict T.structureMorphism L) (fun c => ?_)
  exact (schemeModulePullbackCompIso (i c)
    (Positivity.nullLocusInclusion T.structureMorphism L)).app L.obj ≪≫
      eqToIso (congrArg (fun f => (schemeModulePullback f).obj L.obj)
        (blockToNull_inclusion G L hnull c)) ≪≫ e c

end NullLocus

section Curves

variable (c : (graph G).ConnectedComponent)

theorem prime_subset_blockSupport (E : c.supp) :
    (G E.val : Set T.toScheme) ⊆ blockSupport G c :=
  Set.subset_iUnion (fun F : c.supp => (G F.val : Set T.toScheme)) E

theorem blockIdeal_le_primeKernel (E : c.supp) :
    blockIdeal G c ≤ (G E.val).inclusion.ker := by
  refine le_trans ?_ (vanishingIdeal_le_ker (G E.val).inclusion
    (G E.val).closedSubset (G E.val).range_inclusion.symm)
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (prime_subset_blockSupport G c E)

/-- The reduced prime scheme of `G i`, mapped into its block. -/
def blockCurve (E : c.supp) : (G E.val).toScheme ⟶ blockScheme G c :=
  liftGluedTo (blockIdeal G c) (G E.val).inclusion (blockIdeal_le_primeKernel G c E)

@[reassoc]
theorem blockCurve_inclusion (E : c.supp) :
    blockCurve G c E ≫ blockInclusion G c = (G E.val).inclusion :=
  liftGluedTo_gluedTo _ _ _

instance blockCurve_isClosedImmersion (E : c.supp) :
    IsClosedImmersion (blockCurve G c E) := by
  letI : IsClosedImmersion (blockCurve G c E ≫ blockInclusion G c) := by
    rw [blockCurve_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (blockInclusion G c)

theorem range_blockCurve (E : c.supp) :
    Set.range (blockCurve G c E).base =
      (blockInclusion G c).base ⁻¹' (G E.val : Set T.toScheme) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (blockCurve G c E ≫ blockInclusion G c).base y ∈ (G E.val : Set T.toScheme)
    rw [blockCurve_inclusion, ← (G E.val).range_inclusion]
    exact Set.mem_range_self y
  · intro hx
    have hx' : (blockInclusion G c).base x ∈ Set.range (G E.val).inclusion.base := by
      rw [(G E.val).range_inclusion]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, (blockInclusion G c).isClosedEmbedding.injective ?_⟩
    change (blockCurve G c E ≫ blockInclusion G c).base y = _
    rw [blockCurve_inclusion]
    exact hy

theorem blockCurve_cover :
    ⋃ E : c.supp, Set.range (blockCurve G c E).base = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : (blockInclusion G c).base x ∈ blockSupport G c := by
    rw [← range_blockInclusion]
    exact Set.mem_range_self x
  obtain ⟨E, hE⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨E, (range_blockCurve G c E).symm ▸ hE⟩

theorem blockCurve_incomparable (hinj : Function.Injective G) (E F : c.supp)
    (h : Set.range (blockCurve G c E).base ⊆ Set.range (blockCurve G c F).base) : E = F := by
  have hEF : (G E.val : Set T.toScheme) ⊆ G F.val := by
    intro x hx
    have hx' : x ∈ Set.range (G E.val).inclusion.base := by
      rwa [(G E.val).range_inclusion]
    obtain ⟨y, rfl⟩ := hx'
    have hy := h (Set.mem_range_self (f := (blockCurve G c E).base) y)
    rw [range_blockCurve] at hy
    change (blockCurve G c E ≫ blockInclusion G c).base y ∈ (G F.val : Set T.toScheme) at hy
    rwa [blockCurve_inclusion] at hy
  apply Subtype.ext
  apply hinj
  exact NormalProjectiveSurface.PrimeCurve.ext
    ((G E.val).coe_eq_of_subset_irreducibleCloseds (G F.val).1 hEF (G F.val).ne_univ)

/-- The curves of the block are exactly its irreducible components. -/
def blockComponentEquiv (hinj : Function.Injective G) :
    c.supp ≃ ↥(irreducibleComponents (blockScheme G c)) := by
  letI : Fintype c.supp := Fintype.ofFinite _
  exact curveComponentEquiv (blockScheme G c) (fun E : c.supp => (G E.val).toScheme)
    (blockCurve G c) (fun _ => inferInstance) (blockCurve_cover G c)
    (blockCurve_incomparable G c hinj)

theorem blockComponentEquiv_val (hinj : Function.Injective G) (E : c.supp) :
    (blockComponentEquiv G c hinj E).val = Set.range (blockCurve G c E).base := rfl

theorem blockComponent_inter_nonempty_iff (hinj : Function.Injective G) (E F : c.supp) :
    ((blockComponentEquiv G c hinj E).val ∩ (blockComponentEquiv G c hinj F).val).Nonempty ↔
      ((G E.val : Set T.toScheme) ∩ G F.val).Nonempty := by
  rw [blockComponentEquiv_val, blockComponentEquiv_val, range_blockCurve, range_blockCurve,
    ← Set.preimage_inter]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(blockInclusion G c).base x, hx⟩
  · rintro ⟨x, hxE, hxF⟩
    have hx : x ∈ Set.range (blockInclusion G c).base := by
      rw [range_blockInclusion]
      exact prime_subset_blockSupport G c E hxE
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, hxE, hxF⟩

/-- The component graph of the block is the induced incidence graph. -/
def blockComponentGraphIso (hinj : Function.Injective G) :
    (graph G).induce c.supp ≃g
      incidenceGraph (fun C : ↥(irreducibleComponents (blockScheme G c)) => C.val) :=
  { blockComponentEquiv G c hinj with
    map_rel_iff' := by
      intro E F
      change ((blockComponentEquiv G c hinj E ≠ blockComponentEquiv G c hinj F) ∧
        ((blockComponentEquiv G c hinj E).val ∩
          (blockComponentEquiv G c hinj F).val).Nonempty) ↔
        (E.val ≠ F.val ∧ ((G E.val : Set T.toScheme) ∩ G F.val).Nonempty)
      rw [blockComponent_inter_nonempty_iff]
      exact and_congr (by simp only [ne_eq, Equiv.apply_eq_iff_eq, Subtype.val_inj]) Iff.rfl }

theorem blockComponentGraph_isTree (hinj : Function.Injective G)
    (hforest : (graph G).IsAcyclic) :
    (incidenceGraph
      (fun C : ↥(irreducibleComponents (blockScheme G c)) => C.val)).IsTree := by
  apply isTree_of_iso (blockComponentGraphIso G c hinj).symm
  refine ⟨c.connected_induce_supp, ?_⟩
  let j : (graph G).induce c.supp →g graph G :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  intro x p hp
  exact hforest (p.map j) (hp.map Subtype.val_injective)

end Curves

section Dimension

def blockHomeomorph (c : (graph G).ConnectedComponent) :
    blockScheme G c ≃ₜ blockSupport G c :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨blockSupport G c, blockSupport_isClosed G c⟩).gluedSupportHomeomorph

theorem genericPoint_not_mem_block (c : (graph G).ConnectedComponent) :
    _root_.genericPoint T.toScheme ∉ blockSupport G c := by
  intro hx
  obtain ⟨E, hxE⟩ := Set.mem_iUnion.mp hx
  have hsubset : closure ({_root_.genericPoint T.toScheme} : Set T.toScheme) ⊆
      (G E.val : Set T.toScheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hxE) (G E.val).isClosed
  rw [genericPoint_closure] at hsubset
  exact (G E.val).ne_univ (Set.eq_univ_of_univ_subset hsubset)

theorem blockSupport_ne_univ (c : (graph G).ConnectedComponent) :
    blockSupport G c ≠ Set.univ := by
  intro h
  apply genericPoint_not_mem_block G c
  rw [h]
  exact Set.mem_univ _

theorem blockScheme_dimension_le_one (c : (graph G).ConnectedComponent) :
    topologicalKrullDim (blockScheme G c) ≤ 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq (blockHomeomorph G c)
    (blockHomeomorph G c).isHomeomorph]
  exact KltDP.Topology.topologicalKrullDim_le_one_of_isClosed_of_ne_univ
    T.dimension_two.le (blockSupport_isClosed G c) (blockSupport_ne_univ G c)

end Dimension

section Geometry

variable (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)

/-- The block of a forest of smooth rational curves crossing transversally is a transversal
configuration. -/
theorem block_transversalConfiguration (hinj : Function.Injective G)
    (hrat : ∀ i, ∃ e : (G i).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (G i).toSpec)
    (hacyclic : (graph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (c : (graph G).ConnectedComponent) :
    TransversalConfiguration (blockInclusion G c) := by
  letI : Fintype c.supp := Fintype.ofFinite _
  have hinj' : Function.Injective (fun E : c.supp => G E.val) := by
    intro E F h
    exact Subtype.ext (hinj h)
  apply TransversalClosedPrimeUnion.transversalConfiguration_of_original_primes
    T hreg (fun E : c.supp => G E.val) (blockInclusion G c)
    (blockCurve G c) (blockCurve_inclusion G c) hinj'
  · exact range_blockInclusion G c
  · intro E F D x hxE hxF hxD
    rcases KltDP.Topology.no_three_of_incidence_isAcyclic
        (fun i : ι => (G i : Set T.toScheme)) hacyclic E.val F.val D.val x hxE hxF hxD with
      h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · intro E F hEF x hxE hxF U hxU
    have hne : G E.val ≠ G F.val := fun h => hEF (hinj' h)
    obtain ⟨e, he⟩ := hrat E.val
    letI := smoothOne_of_projectiveLineIso (G E.val).toSpec e he
    letI : IsSmooth (G E.val).toSpec := IsSmoothOfRelativeDimension.isSmooth 1 _
    change x ∈ (G E.val : Set T.toScheme) at hxE
    rw [← (G E.val).range_inclusion] at hxE
    obtain ⟨y, rfl⟩ := hxE
    exact PrimeCurveIntersectionOneCrossing.vanishingIdeal_sup_eq_maximalIdeal_of_pairing_le_one
      T hreg (G E.val) (G F.val) hne (hpair E.val F.val (fun h => hEF (Subtype.ext h)))
      y hxF U hxU

/-- The component-point incidence graph of a block is a tree. -/
theorem block_componentPointIncidenceGraph_isTree (hinj : Function.Injective G)
    (hacyclic : (graph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (c : (graph G).ConnectedComponent) :
    (componentPointIncidenceGraph (blockScheme G c)).IsTree := by
  apply componentPointIncidenceGraph_isTree_of_incidence
    (blockScheme G c) (blockComponentGraph_isTree G c hinj hacyclic)
  intro C D hCD
  obtain ⟨E, rfl⟩ := (blockComponentEquiv G c hinj).surjective C
  obtain ⟨F, rfl⟩ := (blockComponentEquiv G c hinj).surjective D
  have hEF : E ≠ F := fun h => hCD (congrArg (blockComponentEquiv G c hinj) h)
  have hne : G E.val ≠ G F.val := fun h => hEF (Subtype.ext (hinj h))
  have hpoint := PrimeCurvePairingSupport.intersectionPairing_primeCurves_le_one_inter_subsingleton
    T hreg (G E.val) (G F.val) hne (hpair E.val F.val (fun h => hEF (Subtype.ext h)))
  rw [blockComponentEquiv_val, blockComponentEquiv_val, range_blockCurve,
    range_blockCurve, ← Set.preimage_inter]
  exact hpoint.preimage (blockInclusion G c).isClosedEmbedding.injective

/-- Lemma 2.2 on a block: degree zero on every curve gives a frame on the block. -/
theorem blockRestriction_trivial (hinj : Function.Injective G)
    (hrat : ∀ i, ∃ e : (G i).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (G i).toSpec)
    (hacyclic : (graph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (c : (graph G).ConnectedComponent) (L : InvertibleSheaf T.toScheme)
    (hdegree : ∀ i, (G i).restrictionDegree L = 0) :
    Nonempty ((pullbackInvertibleSheaf (blockInclusion G c) L).obj ≅
      _root_.SheafOfModules.unit (blockScheme G c).ringCatSheaf) := by
  classical
  letI : Fintype c.supp := Fintype.ofFinite _
  letI : LocallyOfFiniteType T.structureMorphism := T.projective.locallyOfFiniteType
  refine trivial_of_curve_frames_of_configuration
    (blockScheme G c) (blockInclusion G c) T.structureMorphism
    (block_transversalConfiguration G hreg hinj hrat hacyclic hpair c)
    (blockScheme_dimension_le_one G c)
    (block_componentPointIncidenceGraph_isTree G hreg hinj hacyclic hpair c)
    (fun E : c.supp => (G E.val).toScheme) (blockCurve G c)
    (fun _ => inferInstance) (blockCurve_cover G c)
    (blockCurve_incomparable G c hinj)
    (fun E => (hrat E.val).choose)
    (pullbackInvertibleSheaf (blockInclusion G c) L) ?_
  intro E
  obtain ⟨e, he⟩ := hrat E.val
  let e' : (pullbackInvertibleSheaf (G E.val).inclusion L).obj ≅
      _root_.SheafOfModules.unit (G E.val).toScheme.ringCatSheaf :=
    unitIsoOfEulerDegreeZero e (G E.val).toSpec he
      (pullbackInvertibleSheaf (G E.val).inclusion L) (hdegree E.val)
  exact ⟨(schemeModulePullbackCompIso (blockCurve G c E)
    (blockInclusion G c)).app L.obj ≪≫
      eqToIso (congrArg (fun f => (schemeModulePullback f).obj L.obj)
        (blockCurve_inclusion G c E)) ≪≫ e'⟩

/-- The restriction of `L` to the whole null locus `⋃ G i` is trivial. -/
theorem nullRestriction_trivial (hinj : Function.Injective G)
    (hrat : ∀ i, ∃ e : (G i).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (G i).toSpec)
    (hacyclic : (graph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (L : InvertibleSheaf T.toScheme)
    (hnull : Positivity.nullLocus T.structureMorphism L = ⋃ i, (G i : Set T.toScheme))
    (hdegree : ∀ i, (G i).restrictionDegree L = 0) :
    Nonempty ((Positivity.nullLocusRestrict T.structureMorphism L).obj ≅
      _root_.SheafOfModules.unit
        (Positivity.nullLocusScheme T.structureMorphism L).ringCatSheaf) :=
  ⟨nullRestrictionUnitIsoOfBlocks G L hnull
    (fun c => (blockRestriction_trivial G hreg hinj hrat hacyclic hpair c L hdegree).some)⟩

end Geometry

end ForestBlocks

/-! ## Stage (a): Keel makes the cleared divisor semiample -/

section Semiample

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Manuscript, proof of Theorem 2.6, first paragraph: `E(mH) = G`, `O(mH)` is trivial on each
tree (Lemma 2.2), hence `mH` is semiample by Keel; its complete systems are eventually birational. -/
theorem exists_semiample_of_forest (p : ℕ) [CharP k p] (hp : 0 < p)
    (T : NormalProjectiveSurface k) (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
    {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve) (hinj : Function.Injective G)
    (hrat : ∀ i, ∃ e : (G i).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (G i).toSpec)
    (hacyclic : (curveIncidenceGraph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (Hm : CartierDivisor T.toScheme)
    (hnef : Positivity.IsNef T.structureMorphism (cartierDivisorInvertibleSheaf T.toScheme Hm))
    (hsq : 0 < T.intersectionPairing hreg Hm Hm)
    (hnull : ∀ C : T.PrimeCurve,
      C.restrictionDegree (cartierDivisorInvertibleSheaf T.toScheme Hm) = 0 ↔ ∃ i, C = G i) :
    Positivity.IsSemiample (cartierDivisorInvertibleSheaf T.toScheme Hm) ∧
      KeelCompleteSystem.EventuallyBirational T.structureMorphism
        (cartierDivisorInvertibleSheaf T.toScheme Hm) ∧
      Positivity.IsBig T.structureMorphism (cartierDivisorInvertibleSheaf T.toScheme Hm) ∧
      Positivity.nullLocus T.structureMorphism (cartierDivisorInvertibleSheaf T.toScheme Hm) =
        ⋃ i, (G i : Set T.toScheme) := by
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hreg
  set L := cartierDivisorInvertibleSheaf T.toScheme Hm with hL
  have hpositive : 0 < T.selfIntersection hreg L := by
    change 0 < T.picardPairing hreg (cartierPicardClass T.toScheme Hm)
      (cartierPicardClass T.toScheme Hm)
    rw [T.picardPairing_class]
    exact hsq
  have hnullLocus : Positivity.nullLocus T.structureMorphism L =
      ⋃ i, (G i : Set T.toScheme) := by
    rw [PositiveSquareNefNullLocus.nullLocus_eq_union T L hnef hpositive]
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨C, hC, hx⟩
      obtain ⟨i, rfl⟩ := (hnull C).mp hC
      exact ⟨i, hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨G i, (hnull (G i)).mpr ⟨i, rfl⟩, hx⟩
  obtain ⟨e⟩ := ForestBlocks.nullRestriction_trivial G hreg hinj hrat hacyclic hpair L
    hnullLocus (fun i => (hnull (G i)).mpr ⟨i, rfl⟩)
  exact ⟨NefPositiveSquareKeelRestriction.isSemiample_of_nullRestriction_unitIso
      T p hp L hnef hpositive e,
    NefPositiveSquareKeelRestriction.eventuallyBirational T L hnef hpositive,
    NefPositiveSelfIntersectionBig.isBig T L hnef hpositive, hnullLocus⟩

end Semiample

/-! ## Stage (b), (c): the Stein factorisation of the complete-system map -/

section Contraction

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Manuscript, proof of Theorem 2.6, second paragraph: the Stein factorisation `f : T → Y` of the
morphism given by a sufficiently divisible basepoint-free multiple of `mH`, with `Y` a normal
projective surface, `f` proper, surjective, birational, `f_*O_T = O_Y`, connected fibres; a curve is
contracted iff it has degree zero against `L`; an ample `A` on `Y` with `f^*A ≅ L^{⊗ n}`. -/
theorem exists_contraction_of_semiample (T : NormalProjectiveSurface k)
    (L : InvertibleSheaf T.toScheme) (hsemi : Positivity.IsSemiample L)
    (hev : KeelCompleteSystem.EventuallyBirational T.structureMorphism L) :
    ∃ (Y : NormalProjectiveSurface k) (f : T.toScheme ⟶ Y.toScheme) (n : ℕ), 0 < n ∧
      f ≫ Y.structureMorphism = T.structureMorphism ∧ IsProper f ∧ Surjective f ∧
      IsBirationalScheme f ∧ IsIso f.c ∧
      (∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y})) ∧
      (∀ C : T.PrimeCurve,
        (∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
          C.inclusion ≫ f = C.toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _) ↔
        C.restrictionDegree L = 0) ∧
      ∃ A : InvertibleSheaf Y.toScheme, AmpleSerre.IsAmple A ∧
        Nonempty ((pullbackInvertibleSheaf f A).obj ≅ (power L n).obj) := by
  letI : IsProper T.structureMorphism := T.projective.isProper
  letI : IsIntegral T.toScheme := T.integral
  obtain ⟨N, -, hN⟩ := hev
  obtain ⟨n, hn, hnN, hG⟩ :=
    SemiampleActualPowers.exists_globallyGenerated_power_ge L hsemi N
  obtain ⟨hpos, hbir⟩ := hN n hnN
  let Y : NormalProjectiveSurface k :=
    GeneratedCompleteSystemNormalFactor.normalProjectiveSurface T (power L n) hpos hG hbir
  let f : T.toScheme ⟶ Y.toScheme :=
    GeneratedCompleteSystemNormalFactor.fromSource T.structureMorphism (power L n) hpos hG
  letI : IsProper Y.structureMorphism := Y.projective.isProper
  letI : IsLocallyNoetherian Y.toScheme := Y.isLocallyNoetherian
  letI : IsProper f :=
    GeneratedCompleteSystemNormalFactor.fromSource_isProper T.structureMorphism (power L n) hpos hG
  letI : IsIso f.c :=
    GeneratedCompleteSystemNormalFactor.fromSource_c_isIso T.structureMorphism (power L n) hpos hG
  refine ⟨Y, f, n, hn,
    GeneratedCompleteSystemNormalFactor.fromSource_structure T.structureMorphism (power L n) hpos hG,
    inferInstance,
    GeneratedCompleteSystemNormalFactor.fromSource_surjective T.structureMorphism (power L n) hpos hG,
    GeneratedCompleteSystemNormalFactor.fromSource_isBirationalScheme T.structureMorphism
      (power L n) hpos hG hbir,
    inferInstance,
    ProperSteinConnected.pointFibers_connected f, ?_,
    GeneratedCompleteSystemNormalFactor.line T.structureMorphism (power L n) hpos hG,
    GeneratedCompleteSystemNormalFactor.line_isAmple T.structureMorphism (power L n) hpos hG,
    ⟨GeneratedCompleteSystemNormalFactor.fromSource_pullbackLineIso T.structureMorphism
      (power L n) hpos hG⟩⟩
  intro C
  exact PrimeCurveImageContraction.generatedNormal_factors_iff T C L n hn hpos hG

end Contraction

/-! ## Stage (d): the target has Picard number one -/

section Rank

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Manuscript, proof of Theorem 2.6, third paragraph: the pullback `N¹(Y) → N¹(T)` is injective
and lands in the orthogonal complement of the `r = ρ(T) - 1` independent classes `[G_i]`, so
`ρ(Y) ≤ 1`; the ample class is nonzero, so `ρ(Y) ≥ 1`. -/
theorem picardRank_eq_one_of_contraction (T : NormalProjectiveSurface k)
    (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
    {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve) (hinj : Function.Injective G)
    (hcard : Fintype.card ι + 1 = T.picardRank)
    (Hm : CartierDivisor T.toScheme) (hsq : 0 < T.intersectionPairing hreg Hm Hm)
    (hnullHm : ∀ i, (G i).intersectionNumber Hm = 0)
    (Y : NormalProjectiveSurface k) (f : T.toScheme ⟶ Y.toScheme) [IsProper f]
    (hf : f ≫ Y.structureMorphism = T.structureMorphism) (hbir : IsBirationalScheme f)
    (hexc : ∀ i, IsExceptionalCurve f (G i))
    (A : InvertibleSheaf Y.toScheme) (n : ℕ) (hn : 0 < n)
    (e : (pullbackInvertibleSheaf f A).obj ≅
      (power (cartierDivisorInvertibleSheaf T.toScheme Hm) n).obj) :
    Y.picardRank = 1 := by
  classical
  letI : FiniteDimensional ℚ T.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite T hreg
  set B := T.numericalIntersectionBilinForm hreg with hB
  let W : Submodule ℚ T.NumericalClassGroup :=
    Submodule.span ℚ (Set.range (fun i => DisjointNegativeCurvesRank.curveClass T hreg (G i)))
  have hW : Module.finrank ℚ W = Fintype.card ι :=
    finrank_span_eq_card
      (NullCurveIndependenceRank.linearIndependent T hreg Hm hsq G hinj hnullHm)
  have horth : Module.finrank ℚ (B.orthogonal W) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal (T.numericalIntersectionBilinForm_nondegenerate hreg)
      (T.numericalIntersectionBilinForm_isSymm hreg).isRefl W, hW]
    change T.picardRank - Fintype.card ι = 1
    omega
  let φ := BirationalNumericalPullback.pullback f hf hbir
  have hφ : Function.Injective φ := BirationalNumericalPullback.pullback_injective f hf hbir
  have hrange : LinearMap.range φ ≤ B.orthogonal W := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hk : W ≤ LinearMap.ker (B (φ y)) := by
      apply Submodule.span_le.mpr
      rintro c ⟨i, rfl⟩
      change B (φ y) (DisjointNegativeCurvesRank.curveClass T hreg (G i)) = 0
      rw [DisjointNegativeCurvesRank.pairing_curveClass]
      exact BirationalNumericalPullback.degree_pullback_exceptional f hf hbir (G i) (hexc i) y
    change B w (φ y) = 0
    rw [LinearMap.BilinForm.IsSymm.eq (T.numericalIntersectionBilinForm_isSymm hreg)]
    exact hk hw
  letI : FiniteDimensional ℚ Y.NumericalClassGroup := FiniteDimensional.of_injective φ hφ
  have hle : Y.picardRank ≤ 1 := by
    change Module.finrank ℚ Y.NumericalClassGroup ≤ 1
    rw [← LinearMap.finrank_range_of_inj hφ, ← horth]
    exact Submodule.finrank_mono hrange
  have hne : Y.picardNumericalClass A.toPic ≠ 0 := by
    intro h0
    have h1 : φ (Y.picardNumericalClass A.toPic) =
        n • NefNullCurveNegativeSquare.cartierClass T Hm := by
      change T.picardNumericalMap (Additive.ofMul (schemePicardPullbackHom f A.toPic)) = _
      rw [schemePicardPullbackHom_toPic, SchemeKernelIdealIsoTransport.toPic_eq_of_iso _ _ e,
        power_toPic, ofMul_pow, map_nsmul]
      rfl
    have h2 : NefNullCurveNegativeSquare.cartierClass T Hm ≠ 0 := by
      intro hz
      have hpair := NefNullCurveNegativeSquare.cartierClass_pairing T hreg Hm Hm
      simp only [hz, map_zero, LinearMap.zero_apply] at hpair
      have h5 : T.intersectionPairing hreg Hm Hm = 0 := by exact_mod_cast hpair.symm
      omega
    rw [h0, map_zero] at h1
    have h3 : (n : ℚ) • NefNullCurveNegativeSquare.cartierClass T Hm = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact h1.symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) h4
    · exact h2 h4
  have hpos : 0 < Y.picardRank := by
    change 0 < Module.finrank ℚ Y.NumericalClassGroup
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩
  omega

end Rank

/-! ## The pushforward of a canonical Cartier divisor is a canonical Weil divisor -/

section CanonicalWeil

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Canonical Weil divisors (in the union's smooth-open sense) are stable under adding a principal
divisor. -/
theorem isCanonicalWeilDivisor_add_principal {X : NormalProjectiveSurface k} {D : X.WeilDivisor}
    (hD : IsCanonicalWeilDivisor X D) (g : X.toScheme.functionFieldˣ) :
    IsCanonicalWeilDivisor X (D + X.principalDivisor g) := by
  obtain ⟨U, hne, hsmooth, hU, KU, ⟨eKU⟩, hKU⟩ := hD
  letI : Nonempty U.toScheme := hne
  letI : Nonempty U := ⟨Classical.choice hne⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : IsSmoothOfRelativeDimension 2 (U.ι ≫ X.structureMorphism) := hsmooth
  let gU : U.toScheme.functionFieldˣ :=
    Units.map (OpenImmersionRational.functionFieldIso U.ι).hom.hom.toMonoidHom g
  have hgU : OpenCartierWeil.transportUnit U gU = g := by
    apply Units.ext
    exact Iso.hom_inv_id_apply (OpenImmersionRational.functionFieldIso U.ι) (g : X.toScheme.functionField)
  let KU' : CartierDivisor U.toScheme :=
    KU + principalCartierDivisorHom U.toScheme (Additive.ofMul gU)
  obtain ⟨e'⟩ := cartierModuleIso_of_picardHom_eq U.toScheme KU' KU (by
    show cartierPicardHom U.toScheme (KU + _) = cartierPicardHom U.toScheme KU
    rw [map_add, cartierPicardHom_principal, add_zero])
  have hKU' : OpenCartierWeil.restrictedWeilHom U KU' = D + X.principalDivisor g := by
    show OpenCartierWeil.restrictedWeilHom U (KU + _) = _
    rw [map_add, hKU, OpenCartierWeil.restrictedWeilHom_principal U hU gU, hgU]
  rw [← hKU']
  exact IsCanonicalWeilDivisor.of_smooth_open X U hU KU' (e' ≪≫ eKU)

/-- For a proper birational morphism `f : T → Y` from a smooth surface, the pushforward of a
canonical Cartier divisor of `T` is a canonical Weil divisor of `Y` (manuscript: "choose a nonzero
rational two-form on the common function field ... then `f_*K_T = K_Y`"). -/
theorem isCanonicalWeilDivisor_pushforward_of_cartier (T Y : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 T.structureMorphism]
    (f : T.toScheme ⟶ Y.toScheme) [IsProper f]
    (hf : f ≫ Y.structureMorphism = T.structureMorphism) (hbir : IsBirationalScheme f)
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2) :
    IsCanonicalWeilDivisor Y
      (BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT)) := by
  letI : IsIntegral T.toScheme := T.integral
  let U : Y.toScheme.Opens := targetIsomorphismOpen f
  letI : IsIso (f ∣_ U) := isIso_targetIsomorphismOpen f
  have hU : ∀ C : Y.PrimeCurve, C.genericPoint ∈ U := fun C =>
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve Y f hbir C
  letI : Nonempty U.toScheme := OpenCartierWeil.nonempty_of_primeGenericPoint_mem U hU
  letI : IsSmoothOfRelativeDimension 2 (U.ι ≫ Y.structureMorphism) :=
    SmoothStructureOnIsomorphismOpen.isSmoothOfRelativeDimension 2 T.structureMorphism
      Y.structureMorphism f hf U
  obtain ⟨D, ⟨eD⟩, hD⟩ :=
    CanonicalWeilBirational.exists_compatible_canonical_cartier T Y f hf U hbir hU
  have hKY0 : IsCanonicalWeilDivisor Y (SmoothOpenCanonicalWeil.weilRepresentative Y U) :=
    IsCanonicalWeilDivisor.smoothOpen_weilRepresentative Y U hU
  have hclassT : T.weilClassMap (T.cartierToWeilHom KT) = T.weilClassMap (T.cartierToWeilHom D) :=
    IsCanonicalWeilDivisor.weilClassMap_eq
      (IsCanonicalWeilDivisor.of_cartier T KT eKT) (IsCanonicalWeilDivisor.of_cartier T D eD)
  have hclassY : Y.weilClassMap
      (BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT)) =
      Y.weilClassMap (SmoothOpenCanonicalWeil.weilRepresentative Y U) := by
    have h := congrArg (BirationalWeilClassPushforward.pushforward f hbir) hclassT
    rw [BirationalWeilClassPushforward.pushforward_weilClassMap,
      BirationalWeilClassPushforward.pushforward_weilClassMap, hD] at h
    exact h
  obtain ⟨g, hg⟩ := (Y.weilClassMap_eq_iff _ _).mp hclassY
  have heq : BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT) =
      SmoothOpenCanonicalWeil.weilRepresentative Y U + Y.principalDivisor g := by
    rw [← hg]
    abel
  rw [heq]
  exact isCanonicalWeilDivisor_add_principal hKY0 g

end CanonicalWeil

/-! ## Stage (e): the canonical descent `K_T + B = f^*K_Y` -/

section Descent

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Manuscript, proof of Theorem 2.6, fourth paragraph.  `K_Y := f_*K_T`; from `nmH ∼ f^*A` the
divisor `K_Y` is `ℚ`-Cartier with `-K_Y` ample; `E = K_T + B - f^*K_Y` is exceptional and
numerically trivial on every `G_i`, hence zero by negative definiteness of the intersection matrix
of the `G_i` (Hodge index). -/
theorem canonical_descent (T : NormalProjectiveSurface k)
    (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
    (KT : CartierDivisor T.toScheme)
    {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve) (hinj : Function.Injective G)
    (lam : ι → ℚ) (m : ℕ) (hm : 0 < m) (Hm : CartierDivisor T.toScheme)
    (hHm : T.rationalCartierToWeilHom Hm =
      -((m : ℚ) • (T.rationalCartierToWeilHom KT + ∑ i, Finsupp.single (G i) (lam i))))
    (hsq : 0 < T.intersectionPairing hreg Hm Hm)
    (hnullHm : ∀ i, (G i).intersectionNumber Hm = 0)
    (Y : NormalProjectiveSurface k) (f : T.toScheme ⟶ Y.toScheme) [IsProper f]
    (hf : f ≫ Y.structureMorphism = T.structureMorphism) (hbir : IsBirationalScheme f)
    (hexc : ∀ C : T.PrimeCurve, IsExceptionalCurve f C ↔ ∃ i, C = G i)
    (A : InvertibleSheaf Y.toScheme) (hA : AmpleSerre.IsAmple A) (n : ℕ) (hn : 0 < n)
    (e : (pullbackInvertibleSheaf f A).obj ≅
      (power (cartierDivisorInvertibleSheaf T.toScheme Hm) n).obj) :
    ∃ hK : Y.QCartier (rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT))),
      Y.QAmple (-rationalizeWeilDivisor Y
        (BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT))) ∧
      letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      QCartierPullback.pullback f (rationalizeWeilDivisor Y
          (BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT))) hK =
        T.rationalCartierToWeilHom KT + ∑ i, Finsupp.single (G i) (lam i) := by
  classical
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  set KY : Y.WeilDivisor := BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT)
    with hKYdef
  have hfac : ∀ i, ∃ p : Spec (CommRingCat.of k) ⟶ Y.toScheme,
      (G i).inclusion ≫ f = (G i).toSpec ≫ p ∧ p ≫ Y.structureMorphism = 𝟙 _ :=
    fun i => IsExceptionalCurve.exists_fieldPoint_factor f hf (G i) ((hexc (G i)).mpr ⟨i, rfl⟩)
  -- pushforward of the cleared divisor
  have hpushHm : BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom Hm) =
      -(m • KY) := by
    apply rationalizeWeilDivisor_injective
    rw [← BirationalWeilPushforward.rationalPushforward_rationalize]
    change BirationalWeilPushforward.rationalPushforward f hbir (T.rationalCartierToWeilHom Hm) = _
    rw [hHm, map_neg, map_smul, map_add, map_sum]
    have h0 : ∀ i, BirationalWeilPushforward.rationalPushforward f hbir
        (Finsupp.single (G i) (lam i)) = 0 := by
      intro i
      obtain ⟨p, hp, hp'⟩ := hfac i
      exact BirationalWeilPushforward.rationalPushforward_single_contracted f hbir (G i) (lam i)
        p hp hp'
    simp only [h0, Finset.sum_const_zero, add_zero]
    change -((m : ℚ) • BirationalWeilPushforward.rationalPushforward f hbir
      (rationalizeWeilDivisor T (T.cartierToWeilHom KT))) = _
    rw [BirationalWeilPushforward.rationalPushforward_rationalize, map_neg, map_nsmul,
      Nat.cast_smul_eq_nsmul]
  -- the integral Weil class relation `(n m) K_Y + A = 0`
  obtain ⟨A', hA'⟩ := cartierPicardClass_surjective Y.toScheme A.toPic
  have hpicT : cartierPicardHom T.toScheme (DominantCartierPullback.pullbackHom f A') =
      n • cartierPicardHom T.toScheme Hm := by
    apply Additive.toMul.injective
    rw [toMul_nsmul, cartierPicardHom_apply, cartierPicardHom_apply,
      ← DominantCartierPullback.cartierPicardClass_pullback f A', hA',
      schemePicardPullbackHom_toPic, SchemeKernelIdealIsoTransport.toPic_eq_of_iso _ _ e,
      power_toPic]
    rfl
  have hweilT : T.weilClassMap (T.cartierToWeilHom (DominantCartierPullback.pullbackHom f A')) =
      T.weilClassMap (T.cartierToWeilHom (n • Hm)) := by
    rw [← T.picardToWeilClassHom_cartierPicardHom, ← T.picardToWeilClassHom_cartierPicardHom,
      hpicT]
    simp only [map_nsmul]
  have hweilY : Y.weilClassMap (Y.cartierToWeilHom A') =
      Y.weilClassMap (n • BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom Hm)) := by
    have h := congrArg (BirationalWeilClassPushforward.pushforward f hbir) hweilT
    rw [BirationalWeilClassPushforward.pushforward_weilClassMap,
      BirationalWeilClassPushforward.pushforward_weilClassMap,
      BirationalWeilPushforward.pushforward_cartier_pullback f hbir A', map_nsmul, map_nsmul] at h
    exact h
  have hA'' : Y.picardToWeilClassHom (Additive.ofMul A.toPic) =
      Y.weilClassMap (Y.cartierToWeilHom A') := by
    rw [← hA']
    exact Y.picardToWeilClassHom_cartierPicardHom A'
  have hrel : ((n * m : ℕ) : ℤ) • Y.weilClassMap KY +
      (1 : ℤ) • Y.picardToWeilClassHom (Additive.ofMul A.toPic) = 0 := by
    rw [hA'', hweilY, hpushHm, one_smul, map_nsmul, map_neg, map_nsmul, natCast_zsmul,
      mul_nsmul', neg_nsmul, add_neg_cancel]
  have hnm : (0 : ℤ) < ((n * m : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos hn hm
  have hK : Y.QCartier (rationalizeWeilDivisor Y KY) :=
    Y.qCartier_of_positive_int_picard_relation KY _ hnm A.toPic 1 hrel
  have hQAmple : Y.QAmple (-rationalizeWeilDivisor Y KY) := by
    obtain ⟨N, hN, Bd, hBd, hBample⟩ :=
      Y.exists_ample_anticanonical_multiple_of_positive_relation KY A _ 1 hnm one_pos hA hrel
    exact ⟨N, hN, Bd, by rw [hBd, map_nsmul, map_neg], hBample⟩
  -- the discrepancy divisor
  set M := NullCurveIntersectionMatrix.intersectionMatrix T hreg G with hMdef
  set Δ : T.RationalWeilDivisor :=
    T.rationalCartierToWeilHom KT - QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK
    with hΔdef
  have hexc' : ∀ i, IsExceptionalCurve f (G i) := fun i => (hexc (G i)).mpr ⟨i, rfl⟩
  have hcover : ∀ E : T.PrimeCurve, IsExceptionalCurve f E → E ∈ Set.range G := by
    intro E hE
    obtain ⟨i, hi⟩ := (hexc E).mp hE
    exact ⟨i, hi.symm⟩
  have hrow : ∀ i, (M *ᵥ (fun j => Δ (G j))) i = ((G i).intersectionNumber KT : ℚ) :=
    RationalWeilIntersection.intersectionMatrix_mulVec_compatible_difference
      hreg f hbir hf KT KY hK rfl G hinj hexc' hcover
  have hMij : ∀ i j, RationalWeilIntersection.degreeLinearMap T hreg (G i)
      (Finsupp.single (G j) (lam j)) = lam j * M i j := by
    intro i j
    show Finsupp.linearCombination ℚ
      (fun E => ((G i).intersectionNumber (T.primeCurveCartier hreg E) : ℚ))
      (Finsupp.single (G j) (lam j)) = _
    rw [Finsupp.linearCombination_single, smul_eq_mul]
    congr 1
    change _ = (T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) : ℚ)
    rw [T.intersectionPairing_symm hreg, T.intersectionPairing_primeCurve hreg]
  have hKTrow : ∀ i, ((G i).intersectionNumber KT : ℚ) = -(M *ᵥ lam) i := by
    intro i
    have h := congrArg (RationalWeilIntersection.degreeLinearMap T hreg (G i)) hHm
    rw [RationalWeilIntersection.degreeLinearMap_rationalCartier, hnullHm i, Int.cast_zero,
      map_neg, map_smul, map_add, RationalWeilIntersection.degreeLinearMap_rationalCartier,
      map_sum] at h
    simp only [hMij, smul_eq_mul] at h
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    have h' : ((G i).intersectionNumber KT : ℚ) + ∑ j, lam j * M i j = 0 := by
      rcases mul_eq_zero.mp (neg_eq_zero.mp h.symm) with h1 | h1
      · exact absurd h1 hm'
      · exact h1
    simp only [Matrix.mulVec, dotProduct]
    have hcomm : ∑ j, M i j * lam j = ∑ j, lam j * M i j :=
      Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [hcomm]
    linarith
  have hzero : M *ᵥ (fun j => Δ (G j) + lam j) = 0 := by
    funext i
    have hadd : (fun j => Δ (G j) + lam j) = (fun j => Δ (G j)) + lam := rfl
    rw [hadd, Matrix.mulVec_add, Pi.add_apply, hrow i, hKTrow i, Pi.zero_apply]
    ring
  have hdet : M.det ≠ 0 :=
    NullCurveIntersectionMatrix.det_ne_zero T hreg Hm hsq G hinj hnullHm
  have hcoef : ∀ j, Δ (G j) = -lam j := by
    have hv := Matrix.eq_zero_of_mulVec_eq_zero hdet hzero
    intro j
    have hj := congrFun hv j
    simp only [Pi.zero_apply] at hj
    linarith
  have hΔsupp : ∀ C : T.PrimeCurve, (∀ i, C ≠ G i) → Δ C = 0 := by
    intro C hC
    by_contra hne
    have hmem : C ∈ Δ.support := Finsupp.mem_support_iff.mpr hne
    have hE := MinimalResolutionDiscrepancy.difference_support_subset_exceptional
      f hbir KT KY hK rfl hmem
    obtain ⟨i, hi⟩ := (hexc C).mp hE
    exact hC i hi
  have hΔ : Δ = ∑ i, Finsupp.single (G i) (-lam i) := by
    ext C
    by_cases hC : ∃ i, C = G i
    · obtain ⟨i₀, rfl⟩ := hC
      rw [hcoef i₀, sum_single_apply_eq G hinj _ i₀]
    · rw [hΔsupp C (fun i h => hC ⟨i, h⟩), sum_single_apply_of_not G _ C (fun i h => hC ⟨i, h⟩)]
  refine ⟨hK, hQAmple, ?_⟩
  have hpull : QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK =
      T.rationalCartierToWeilHom KT - Δ := by
    rw [hΔdef, sub_sub_cancel]
  rw [hpull, hΔ]
  simp only [Finsupp.single_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

end Descent

/-! ## Theorem 2.6 -/

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Manuscript Theorem 2.6** (`thm:anticanonical-contraction`, lines 491–521).

Let `T` be a smooth projective surface over an algebraically closed field of characteristic
`p > 0`, `K_T` a canonical Cartier divisor, `G : ι → T.PrimeCurve` an injective finite family of
smooth rational curves forming an SNC forest (`hrat`, `hacyclic`, `hpair`), with
`card ι + 1 = ρ(T)`; `λ_i < 1`; `H = -(K_T + Σ λ_i G_i)` cleared to the Cartier divisor
`Hm = m H` (`hHm`), nef with `Hm² > 0` (i) and with `Hm · C = 0 ↔ C ∈ {G_i}` (ii).  Then a
sufficiently divisible multiple of `H` defines a proper birational contraction `f : T → Y` with
connected fibres and exceptional curves exactly the `G_i`, onto a normal projective rank-one klt
del Pezzo surface `Y`, and with `K_Y := f_*K_T` the crepant equality `K_T + Σ λ_i G_i = f^*K_Y`
holds, `-K_Y` is ample and `ρ(Y) = 1`. -/
theorem anticanonicalContraction (p : ℕ) [CharP k p] (hp : 0 < p)
    (T : NormalProjectiveSurface k) (hreg : ∀ x : T.Point, RegularPoint T.toScheme x)
    (KT : CartierDivisor T.toScheme)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2)
    {ι : Type u} [Fintype ι] (G : ι → T.PrimeCurve) (hinj : Function.Injective G)
    (hrat : ∀ i, ∃ e : (G i).toScheme ≅ projectiveSpace k 1,
      e.hom ≫ projectiveSpaceToSpec k 1 = (G i).toSpec)
    (hacyclic : (curveIncidenceGraph G).IsAcyclic)
    (hpair : ∀ i j, i ≠ j → T.intersectionPairing hreg (T.primeCurveCartier hreg (G i))
      (T.primeCurveCartier hreg (G j)) ≤ 1)
    (hcard : Fintype.card ι + 1 = T.picardRank)
    (lam : ι → ℚ) (hlam : ∀ i, lam i < 1)
    (m : ℕ) (hm : 0 < m) (Hm : CartierDivisor T.toScheme)
    (hHm : T.rationalCartierToWeilHom Hm =
      -((m : ℚ) • (T.rationalCartierToWeilHom KT + ∑ i, Finsupp.single (G i) (lam i))))
    (hnef : Positivity.IsNef T.structureMorphism (cartierDivisorInvertibleSheaf T.toScheme Hm))
    (hsq : 0 < T.intersectionPairing hreg Hm Hm)
    (hnull : ∀ C : T.PrimeCurve,
      C.restrictionDegree (cartierDivisorInvertibleSheaf T.toScheme Hm) = 0 ↔ ∃ i, C = G i) :
    ∃ (Y : NormalProjectiveSurface k) (f : T.toScheme ⟶ Y.toScheme)
      (hproper : IsProper f) (hbir : IsBirationalScheme f),
      f ≫ Y.structureMorphism = T.structureMorphism ∧ IsIso f.c ∧ IsBirational f ∧
      (∀ y : Y.toScheme, IsConnected (f.base ⁻¹' {y})) ∧
      (∀ C : T.PrimeCurve, IsExceptionalCurve f C ↔ ∃ i, C = G i) ∧
      IsKltDelPezzo Y ∧ Y.picardRank = 1 ∧
      letI : IsProper f := hproper
      letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
      let KY : Y.WeilDivisor :=
        BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT)
      IsKltWithCanonicalDivisor Y KY ∧ Y.QAmple (-rationalizeWeilDivisor Y KY) ∧
      ∃ hK : Y.QCartier (rationalizeWeilDivisor Y KY),
        QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK =
          T.rationalCartierToWeilHom KT + ∑ i, Finsupp.single (G i) (lam i) := by
  classical
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hreg
  letI : IsSmooth T.structureMorphism := IsSmoothOfRelativeDimension.isSmooth 2 T.structureMorphism
  letI : IsIntegral T.toScheme := T.integral
  have hnullHm : ∀ i, (G i).intersectionNumber Hm = 0 := fun i => (hnull (G i)).mpr ⟨i, rfl⟩
  obtain ⟨hsemi, hev, -, -⟩ :=
    exists_semiample_of_forest p hp T hreg G hinj hrat hacyclic hpair Hm hnef hsq hnull
  obtain ⟨Y, f, n, hn, hf, hproper, hsurj, hbir, hc, hconn, hcrit, A, hA, ⟨e⟩⟩ :=
    exists_contraction_of_semiample T (cartierDivisorInvertibleSheaf T.toScheme Hm) hsemi hev
  letI : IsProper f := hproper
  letI : GenericPointPreserving f := ⟨hbir.map_genericPoint⟩
  have hexc : ∀ C : T.PrimeCurve, IsExceptionalCurve f C ↔ ∃ i, C = G i := by
    intro C
    rw [← hnull C, ← hcrit C]
    exact ⟨fun hC => IsExceptionalCurve.exists_fieldPoint_factor f hf C hC,
      fun ⟨q, hq, _⟩ => IsExceptionalCurve.of_fieldPoint_factor f C q hq⟩
  have hrank : Y.picardRank = 1 :=
    picardRank_eq_one_of_contraction T hreg G hinj hcard Hm hsq hnullHm Y f hf hbir
      (fun i => (hexc (G i)).mpr ⟨i, rfl⟩) A n hn e
  obtain ⟨hK, hQAmple, hpull⟩ :=
    canonical_descent T hreg KT G hinj lam m hm Hm hHm hsq hnullHm Y f hf hbir hexc A hA n hn e
  set KY : Y.WeilDivisor := BirationalWeilPushforward.pushforward f hbir (T.cartierToWeilHom KT)
    with hKYdef
  have hKY : IsCanonicalWeilDivisor Y KY :=
    isCanonicalWeilDivisor_pushforward_of_cartier T Y f hf hbir KT eKT
  -- the discrepancy divisor `K_T - f^*K_Y = -Σ λ_i G_i`
  have hΔ : T.rationalCartierToWeilHom KT -
      QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK =
      ∑ i, Finsupp.single (G i) (-lam i) := by
    rw [hpull, sub_add_cancel_left, ← Finset.sum_neg_distrib]
    simp only [Finsupp.single_neg]
  -- the SNC boundary `Σ G_i`
  haveI : ∀ i, IsSmooth (G i).toSpec := fun i => by
    obtain ⟨e, he⟩ := hrat i
    letI := smoothOne_of_projectiveLineIso (G i).toSpec e he
    exact IsSmoothOfRelativeDimension.isSmooth 1 _
  have hno : ∀ i j l (x : T.toScheme), x ∈ (G i : Set T.toScheme) →
      x ∈ (G j : Set T.toScheme) → x ∈ (G l : Set T.toScheme) → i = j ∨ i = l ∨ j = l :=
    fun i j l x hi hj hl => KltDP.Topology.no_three_of_incidence_isAcyclic
      (fun i : ι => (G i : Set T.toScheme)) hacyclic i j l x hi hj hl
  set EG : CartierDivisor T.toScheme := ∑ i, T.primeCurveCartier hreg (G i) with hEGdef
  have hEG : IsStrictNormalCrossingsCartier T.toScheme EG :=
    finite_smooth_primeCurve_sum_isStrictNormalCrossings T hreg G hinj hpair hno
  have hEGweil : T.cartierToWeilHom EG = ∑ i, Finsupp.single (G i) (1 : ℤ) := by
    rw [hEGdef, map_sum]
    simp only [T.cartierToWeilHom_primeCurveCartier hreg]
  have hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom EG C = 0 ∨ T.cartierToWeilHom EG C = 1 := by
    intro C
    rw [hEGweil]
    by_cases hC : ∃ i, C = G i
    · obtain ⟨i, rfl⟩ := hC
      exact Or.inr (sum_single_apply_eq G hinj _ i)
    · exact Or.inl (sum_single_apply_of_not G _ C (fun i h => hC ⟨i, h⟩))
  have hsupport : (T.rationalCartierToWeilHom KT -
      QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK).support ⊆
      (T.cartierToWeilHom EG).support := by
    intro C hC
    rw [Finsupp.mem_support_iff] at hC ⊢
    by_cases hCG : ∃ i, C = G i
    · obtain ⟨i, rfl⟩ := hCG
      rw [hEGweil, sum_single_apply_eq G hinj _ i]
      exact one_ne_zero
    · exfalso
      apply hC
      rw [hΔ]
      exact sum_single_apply_of_not G _ C (fun i h => hCG ⟨i, h⟩)
  have hbound : ∀ C : T.PrimeCurve, (-1 : ℚ) < (T.rationalCartierToWeilHom KT -
      QCartierPullback.pullback f (rationalizeWeilDivisor Y KY) hK) C := by
    intro C
    rw [hΔ]
    by_cases hCG : ∃ i, C = G i
    · obtain ⟨i, rfl⟩ := hCG
      rw [sum_single_apply_eq G hinj _ i]
      show (-1 : ℚ) < -lam i
      linarith [hlam i]
    · rw [sum_single_apply_of_not G _ C (fun i h => hCG ⟨i, h⟩)]
      norm_num
  have hklt : IsKltWithCanonicalDivisor Y KY :=
    isKltWithCanonicalDivisor_of_snc_discrepancy T Y f hbir hf KT eKT KY hKY hK rfl
      EG hEG hcoeff hsupport hbound
  refine ⟨Y, f, hproper, hbir, hf, hc, (isBirational_iff_isBirationalScheme f).mpr hbir, hconn,
    hexc, (isLogDelPezzoPair_zero_iff Y).mpr ⟨KY, hklt, hQAmple⟩, hrank, hklt, hQAmple, hK, hpull⟩

end Main

end KltDP.Manuscript.S02

#print axioms KltDP.Manuscript.S02.anticanonicalContraction
