import KltDP.Geometry.RationalTreePicardOfConfiguration
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Routine transports for the configuration corollary of `lem:tree-picard`

BRIEF19, task 2. The corollary `rationalTreePicard_of_configuration` carries three hypotheses on
the configuration scheme `X` itself: `hTree` (the component-point incidence graph is a tree),
`hdim : topologicalKrullDim X ≤ 1`, and `[IsLocallyNoetherian X]`. This module supplies them from
data that is available for concrete configurations:

* **Trees.** Path graphs are acyclic (`pathGraph_isAcyclic`: every edge is a bridge, by the
  invariant "after deleting the edge `{u, u+1}`, everything reachable from `u` is `≤ u`"), hence
  trees (`pathGraph_isTree`), and `IsTree` transports along graph isomorphisms (`isTree_of_iso`).
  For a *chain* of components `e : Fin (m+1) ≃ irreducibleComponents X` in which adjacent members
  meet in exactly one point and non-adjacent members are disjoint, the incidence graph is
  isomorphic to the path graph on `2m+1` vertices (`chainIso`; components at even positions,
  intersection points at odd positions), so it is a tree (`isTree_of_chain`). Members of such a
  chain with at least two points each are pairwise incomparable (`chain_not_subset`), which is
  the `hdistinct` input of the corollary.
* **Noetherian hypotheses** along a closed immersion `ι : X ⟶ S`
  (`noetherianSpace_of_isClosedImmersion`, `isLocallyNoetherian_of_isClosedImmersion`; the latter
  is the accepted proof of `componentUnionScheme_isLocallyNoetherian` for an arbitrary closed
  immersion).
* **Dimension.** A scheme covered by finitely many closed curves of dimension `≤ 1` has
  dimension `≤ 1` (`topologicalKrullDim_le_one_of_curves`): a chain of irreducible closed subsets
  lies inside the image of one curve (the last member is irreducible) and pulls back to a chain
  in that curve (`preimageIrreducibleCloseds`).

Not done: the transport of `hTree` from a general `J`-indexed tree of curves (subdivision of an
arbitrary tree); only the chain case, which is what the witnesses of BRIEF19 need, is written.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace SimpleGraph Topology

universe u v

namespace KltDP.Geometry.RationalTreePicard

/-! ## Path graphs are trees -/

section PathGraph

/-- After deleting the edge `{u, v}` with `u + 1 = v` from the path graph, every vertex reachable
from a vertex `≤ u` is `≤ u`. -/
theorem pathGraph_deleteEdge_le {n : ℕ} {u v : Fin n} (huv : u.val + 1 = v.val) :
    ∀ {a b : Fin n}, (pathGraph n \ fromEdgeSet {s(u, v)}).Walk a b →
      a.val ≤ u.val → b.val ≤ u.val := by
  intro a b p
  induction p with
  | nil => exact id
  | @cons a c b hac p ih =>
    intro ha
    apply ih
    rw [sdiff_adj, fromEdgeSet_adj, pathGraph_adj] at hac
    obtain ⟨h1, h2⟩ := hac
    rcases h1 with h1 | h1
    · by_contra hc
      have hau' : a = u := Fin.ext (by omega)
      have hcv' : c = v := Fin.ext (by omega)
      refine h2 ⟨?_, fun h => ?_⟩
      · rw [hau', hcv']
        exact Set.mem_singleton _
      · rw [h] at h1
        omega
    · omega

/-- Path graphs are acyclic: every edge is a bridge. -/
theorem pathGraph_isAcyclic (n : ℕ) : (pathGraph n).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [isBridge_iff]
  refine ⟨huv, fun hreach => ?_⟩
  rcases pathGraph_adj.mp huv with h | h
  · obtain ⟨p⟩ := hreach
    have := pathGraph_deleteEdge_le h p le_rfl
    omega
  · have hreach' := hreach.symm
    rw [Sym2.eq_swap] at hreach'
    obtain ⟨p⟩ := hreach'
    have := pathGraph_deleteEdge_le h p le_rfl
    omega

/-- Path graphs on at least one vertex are trees. -/
theorem pathGraph_isTree (n : ℕ) : (pathGraph (n + 1)).IsTree :=
  ⟨pathGraph_connected n, pathGraph_isAcyclic (n + 1)⟩

/-- Being a tree transports along a graph isomorphism. -/
theorem isTree_of_iso {V : Type u} {V' : Type v} {G : SimpleGraph V} {H : SimpleGraph V'}
    (e : G ≃g H) (hH : H.IsTree) : G.IsTree :=
  ⟨e.connected_iff.mpr hH.isConnected,
    fun _ c hc => hH.IsAcyclic (c.map e.toHom) (hc.map e.injective)⟩

end PathGraph

/-! ## Chains of components -/

section Chain

variable (X : Scheme.{u})

/-- A chain of components: an enumeration `e` of the irreducible components of `X` in which
adjacent members meet in at most one point (and at least one), and non-adjacent members are
disjoint. -/
structure IsChain {m : ℕ} (e : Fin (m + 1) ≃ ↥(irreducibleComponents X)) : Prop where
  subsingleton : ∀ j : Fin m, ((e j.castSucc).1 ∩ (e j.succ).1).Subsingleton
  nonempty : ∀ j : Fin m, ((e j.castSucc).1 ∩ (e j.succ).1).Nonempty
  disjoint : ∀ i j : Fin (m + 1), i.val + 1 < j.val → Disjoint (e i).1 (e j).1

variable {m : ℕ} (e : Fin (m + 1) ≃ ↥(irreducibleComponents X)) (hc : IsChain X e)

/-- The common point of two adjacent members of the chain. -/
def chainPoint (j : Fin m) : X := (hc.nonempty j).choose

theorem chainPoint_mem (j : Fin m) :
    chainPoint X e hc j ∈ (e j.castSucc).1 ∩ (e j.succ).1 := (hc.nonempty j).choose_spec

theorem chain_inter_eq (j : Fin m) :
    (e j.castSucc).1 ∩ (e j.succ).1 = {chainPoint X e hc j} :=
  (hc.subsingleton j).eq_singleton_of_mem (chainPoint_mem X e hc j)

/-- The common point of `e l`, `e (l+1)` lies on `e i` exactly for `i ∈ {l, l+1}`. -/
theorem chainPoint_mem_iff (l : Fin m) (i : Fin (m + 1)) :
    chainPoint X e hc l ∈ (e i).1 ↔ i = l.castSucc ∨ i = l.succ := by
  constructor
  · intro hi
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hmem := chainPoint_mem X e hc l
    have h1' : i.val ≠ l.val := fun h => h1 (Fin.ext (by rw [Fin.coe_castSucc]; exact h))
    have h2' : i.val ≠ l.val + 1 := fun h => h2 (Fin.ext (by rw [Fin.val_succ]; exact h))
    rcases lt_or_gt_of_ne h1' with hlt | hgt
    · exact Set.disjoint_left.mp (hc.disjoint i l.succ (by rw [Fin.val_succ]; omega)) hi hmem.2
    · exact Set.disjoint_left.mp (hc.disjoint l.castSucc i (by rw [Fin.coe_castSucc]; omega)) hmem.1 hi
  · rintro (rfl | rfl)
    · exact (chainPoint_mem X e hc l).1
    · exact (chainPoint_mem X e hc l).2

theorem chainPoint_injective : Function.Injective (chainPoint X e hc) := by
  intro l l' h
  by_contra hll
  have hmem := chainPoint_mem X e hc l
  have hmem' := chainPoint_mem X e hc l'
  rw [h] at hmem
  have hv : l.val ≠ l'.val := fun hv => hll (Fin.ext hv)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact Set.disjoint_left.mp
      (hc.disjoint l.castSucc l'.succ (by rw [Fin.coe_castSucc, Fin.val_succ]; omega)) hmem.1 hmem'.2
  · exact Set.disjoint_left.mp
      (hc.disjoint l'.castSucc l.succ (by rw [Fin.coe_castSucc, Fin.val_succ]; omega)) hmem'.1 hmem.2

/-- A point on two members `e i`, `e j` with `i < j` is the common point of an adjacent pair. -/
theorem eq_chainPoint_of_mem_of_lt {i j : Fin (m + 1)} (hij : i.val < j.val) {x : X}
    (hi : x ∈ (e i).1) (hj : x ∈ (e j).1) : ∃ l : Fin m, x = chainPoint X e hc l := by
  by_cases h : i.val + 1 < j.val
  · exact absurd hj (Set.disjoint_left.mp (hc.disjoint i j h) hi)
  · have hlt : i.val < m := by have := j.isLt; omega
    refine ⟨⟨i.val, hlt⟩, ?_⟩
    have hi' : i = Fin.castSucc ⟨i.val, hlt⟩ := Fin.ext rfl
    have hj' : j = Fin.succ ⟨i.val, hlt⟩ := Fin.ext (show j.val = i.val + 1 by omega)
    have hx : x ∈ (e (Fin.castSucc ⟨i.val, hlt⟩)).1 ∩ (e (Fin.succ ⟨i.val, hlt⟩)).1 := by
      rw [← hi', ← hj']
      exact ⟨hi, hj⟩
    rw [chain_inter_eq X e hc] at hx
    exact hx

/-- The intersection points of `X` are exactly the common points of adjacent pairs. -/
theorem mem_componentIntersectionPoints_iff_chain (x : X) :
    x ∈ componentIntersectionPoints X ↔ ∃ l : Fin m, x = chainPoint X e hc l := by
  constructor
  · rintro ⟨C, D, hCD, hxC, hxD⟩
    obtain ⟨i, rfl⟩ := e.surjective C
    obtain ⟨j, rfl⟩ := e.surjective D
    have hij : i.val ≠ j.val := fun h => hCD (congrArg e (Fin.ext h))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact eq_chainPoint_of_mem_of_lt X e hc hlt hxC hxD
    · exact eq_chainPoint_of_mem_of_lt X e hc hgt hxD hxC
  · rintro ⟨l, rfl⟩
    refine ⟨e l.castSucc, e l.succ, fun h => ?_, (chainPoint_mem X e hc l).1,
      (chainPoint_mem X e hc l).2⟩
    have := congrArg Fin.val (e.injective h)
    rw [Fin.coe_castSucc, Fin.val_succ] at this
    omega

/-- The chain index of an intersection point. -/
def chainPointIndex (p : ↥(componentIntersectionPoints X)) : Fin m :=
  ((mem_componentIntersectionPoints_iff_chain X e hc p.1).mp p.2).choose

theorem chainPoint_chainPointIndex (p : ↥(componentIntersectionPoints X)) :
    chainPoint X e hc (chainPointIndex X e hc p) = p.1 :=
  ((mem_componentIntersectionPoints_iff_chain X e hc p.1).mp p.2).choose_spec.symm

/-- The common point of an adjacent pair as an intersection point. -/
def chainPointSubtype (l : Fin m) : ↥(componentIntersectionPoints X) :=
  ⟨chainPoint X e hc l, (mem_componentIntersectionPoints_iff_chain X e hc _).mpr ⟨l, rfl⟩⟩

theorem chainPointIndex_chainPointSubtype (l : Fin m) :
    chainPointIndex X e hc (chainPointSubtype X e hc l) = l :=
  chainPoint_injective X e hc (chainPoint_chainPointIndex X e hc _)

/-- The position of a vertex of the incidence graph on the path: components at even positions,
intersection points at odd positions. -/
def chainPosition : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X) → Fin (2 * m + 1)
  | Sum.inl C => ⟨2 * (e.symm C).val, by have := (e.symm C).isLt; omega⟩
  | Sum.inr p => ⟨2 * (chainPointIndex X e hc p).val + 1,
      by have := (chainPointIndex X e hc p).isLt; omega⟩

theorem chainPosition_inl (C : ↥(irreducibleComponents X)) :
    (chainPosition X e hc (Sum.inl C)).val = 2 * (e.symm C).val := rfl

theorem chainPosition_inr (p : ↥(componentIntersectionPoints X)) :
    (chainPosition X e hc (Sum.inr p)).val =
      2 * (chainPointIndex X e hc p).val + 1 := rfl

theorem chainPosition_injective : Function.Injective (chainPosition X e hc) := by
  intro v w h
  have h' := congrArg Fin.val h
  rcases v with C | p <;> rcases w with D | p'
  · rw [chainPosition_inl, chainPosition_inl] at h'
    have : e.symm C = e.symm D := Fin.ext (by omega)
    exact congrArg Sum.inl (e.symm.injective this)
  · rw [chainPosition_inl, chainPosition_inr] at h'
    omega
  · rw [chainPosition_inr, chainPosition_inl] at h'
    omega
  · rw [chainPosition_inr, chainPosition_inr] at h'
    have : chainPointIndex X e hc p = chainPointIndex X e hc p' :=
      Fin.ext (by omega)
    have hp := chainPoint_chainPointIndex X e hc p
    rw [this, chainPoint_chainPointIndex] at hp
    exact congrArg Sum.inr (Subtype.ext hp.symm)

theorem chainPosition_surjective : Function.Surjective (chainPosition X e hc) := by
  intro t
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' t.val
  · have hlt : i < m + 1 := by have := t.isLt; omega
    refine ⟨Sum.inl (e ⟨i, hlt⟩), Fin.ext ?_⟩
    rw [chainPosition_inl, Equiv.symm_apply_apply, hi]
  · have hlt : i < m := by have := t.isLt; omega
    refine ⟨Sum.inr (chainPointSubtype X e hc ⟨i, hlt⟩), Fin.ext ?_⟩
    rw [chainPosition_inr, chainPointIndex_chainPointSubtype, hi]

theorem chainPosition_adj (v w : ↥(irreducibleComponents X) ⊕ ↥(componentIntersectionPoints X)) :
    (pathGraph (2 * m + 1)).Adj (chainPosition X e hc v)
        (chainPosition X e hc w) ↔
      (componentPointIncidenceGraph X).Adj v w := by
  rw [pathGraph_adj]
  rcases v with C | p <;> rcases w with D | p'
  · rw [chainPosition_inl, chainPosition_inl]
    exact ⟨fun h => by omega, fun h => (h : False).elim⟩
  · rw [chainPosition_inl, chainPosition_inr]
    obtain ⟨i, rfl⟩ := e.surjective C
    show _ ↔ p'.1 ∈ (e i).1
    rw [Equiv.symm_apply_apply, ← chainPoint_chainPointIndex X e hc p',
      chainPoint_mem_iff X e hc]
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.ext (by rw [Fin.coe_castSucc]; omega))
      · exact Or.inr (Fin.ext (by rw [Fin.val_succ]; omega))
    · rintro (rfl | rfl)
      · left
        rw [Fin.coe_castSucc]
      · right
        rw [Fin.val_succ]
        omega
  · rw [chainPosition_inr, chainPosition_inl]
    obtain ⟨i, rfl⟩ := e.surjective D
    show _ ↔ p.1 ∈ (e i).1
    rw [Equiv.symm_apply_apply, ← chainPoint_chainPointIndex X e hc p,
      chainPoint_mem_iff X e hc]
    constructor
    · rintro (h | h)
      · exact Or.inr (Fin.ext (by rw [Fin.val_succ]; omega))
      · exact Or.inl (Fin.ext (by rw [Fin.coe_castSucc]; omega))
    · rintro (rfl | rfl)
      · right
        rw [Fin.coe_castSucc]
      · left
        rw [Fin.val_succ]
        omega
  · rw [chainPosition_inr, chainPosition_inr]
    exact ⟨fun h => by omega, fun h => (h : False).elim⟩

/-- The incidence graph of a chain is the path graph on `2m+1` vertices. -/
def chainIso : componentPointIncidenceGraph X ≃g pathGraph (2 * m + 1) :=
  { Equiv.ofBijective (chainPosition X e hc)
      ⟨chainPosition_injective X e hc, chainPosition_surjective X e hc⟩ with
    map_rel_iff' := fun {v w} => chainPosition_adj X e hc v w }

include e hc in
/-- **The incidence graph of a chain of components is a tree.** -/
theorem isTree_of_chain : (componentPointIncidenceGraph X).IsTree :=
  isTree_of_iso (chainIso X e hc) (pathGraph_isTree (2 * m))

end Chain

/-- Members of a chain of sets (adjacent intersections subsingleton, non-adjacent members
disjoint), none of which is a subsingleton, are pairwise incomparable. -/
theorem chain_not_subset {Y : Type v} {m : ℕ} (R : Fin (m + 1) → Set Y)
    (hsub : ∀ j : Fin m, (R j.castSucc ∩ R j.succ).Subsingleton)
    (hdisj : ∀ i j : Fin (m + 1), i.val + 1 < j.val → Disjoint (R i) (R j))
    (hnt : ∀ i, ¬ (R i).Subsingleton) (i j : Fin (m + 1)) (h : R i ⊆ R j) : i = j := by
  by_contra hij
  apply hnt i
  rw [← Set.inter_eq_left.mpr h]
  have hv : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · by_cases hadj : i.val + 1 < j.val
    · rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj i j hadj)]
      exact Set.subsingleton_empty
    · have hl : i.val < m := by have := j.isLt; omega
      have hi : i = Fin.castSucc ⟨i.val, hl⟩ := Fin.ext rfl
      have hj : j = Fin.succ ⟨i.val, hl⟩ := Fin.ext (show j.val = i.val + 1 by omega)
      have := hsub ⟨i.val, hl⟩
      rwa [← hi, ← hj] at this
  · rw [Set.inter_comm]
    by_cases hadj : j.val + 1 < i.val
    · rw [Set.disjoint_iff_inter_eq_empty.mp (hdisj j i hadj)]
      exact Set.subsingleton_empty
    · have hl : j.val < m := by have := i.isLt; omega
      have hj : j = Fin.castSucc ⟨j.val, hl⟩ := Fin.ext rfl
      have hi : i = Fin.succ ⟨j.val, hl⟩ := Fin.ext (show i.val = j.val + 1 by omega)
      have := hsub ⟨j.val, hl⟩
      rwa [← hj, ← hi] at this

/-- Transversal crossing is symmetric in the two components. -/
theorem TransversalCrossing.symm {X S : Scheme.{u}} [NoetherianSpace X] {ι : X ⟶ S}
    {C D : ↥(irreducibleComponents X)} {q : X} (h : TransversalCrossing ι C D q) :
    TransversalCrossing ι D C q where
  regular := h.regular
  dim_eq := h.dim_eq
  exists_equations := by
    obtain ⟨f, g, hspan, hker, hf, hg⟩ := h.exists_equations
    refine ⟨g, f, ?_, ?_, hg, hf⟩
    · rw [Set.pair_comm]
      exact hspan
    · rw [mul_comm]
      exact hker

/-! ## Noetherian hypotheses along a closed immersion -/

section Noetherian

variable {X S : Scheme.{u}}

/-- A closed subscheme of a Noetherian space is a Noetherian space. -/
theorem noetherianSpace_of_isClosedImmersion (ι : X ⟶ S) [IsClosedImmersion ι]
    [NoetherianSpace S] : NoetherianSpace X :=
  ι.isEmbedding.isInducing.noetherianSpace

/-- A closed subscheme of a locally Noetherian scheme is locally Noetherian: on the pullback of
an affine cover, the section rings are quotients of Noetherian rings. -/
theorem isLocallyNoetherian_of_isClosedImmersion (ι : X ⟶ S) [IsClosedImmersion ι]
    [IsLocallyNoetherian S] : IsLocallyNoetherian X := by
  let 𝒰 := S.affineCover.pullbackCover ι
  haveI hci : ∀ i, IsClosedImmersion (pullback.snd ι (S.affineCover.map i)) :=
    fun i => MorphismProperty.pullback_snd _ _ inferInstance
  haveI : ∀ i, IsAffine (𝒰.obj i) := fun i =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.snd ι (S.affineCover.map i))).1
  rw [isLocallyNoetherian_iff_of_affine_openCover 𝒰]
  intro i
  haveI hS : IsNoetherianRing Γ(S.affineCover.obj i, ⊤) :=
    (isLocallyNoetherian_iff_of_affine_openCover S.affineCover).mp inferInstance i
  exact isNoetherianRing_of_surjective _ _
    (pullback.snd ι (S.affineCover.map i)).appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.snd ι (S.affineCover.map i))).2

end Noetherian

/-! ## Dimension of a finite union of curves -/

section Dimension

/-- The preimage under an inducing map of an irreducible set contained in the range is
irreducible. -/
theorem isIrreducible_preimage_of_isInducing {Y Z : Type v} [TopologicalSpace Y]
    [TopologicalSpace Z] {f : Y → Z} (hf : IsInducing f) {T : Set Z} (hT : IsIrreducible T)
    (hTf : T ⊆ Set.range f) : IsIrreducible (f ⁻¹' T) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := hT.nonempty
    obtain ⟨y, rfl⟩ := hTf hz
    exact ⟨y, hz⟩
  · intro u v hu hv ⟨y₁, hy₁, hy₁u⟩ ⟨y₂, hy₂, hy₂v⟩
    obtain ⟨u', hu', rfl⟩ := hf.isOpen_iff.mp hu
    obtain ⟨v', hv', rfl⟩ := hf.isOpen_iff.mp hv
    obtain ⟨z, hzT, hzu, hzv⟩ := hT.2 u' v' hu' hv' ⟨f y₁, hy₁, hy₁u⟩ ⟨f y₂, hy₂, hy₂v⟩
    obtain ⟨y, rfl⟩ := hTf hzT
    exact ⟨y, hzT, hzu, hzv⟩

/-- The preimage of an irreducible closed subset of the range of a closed embedding. -/
def preimageIrreducibleCloseds {Y Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → Z} (hf : IsClosedEmbedding f) (T : IrreducibleCloseds Z)
    (hT : (T : Set Z) ⊆ Set.range f) : IrreducibleCloseds Y where
  carrier := f ⁻¹' T
  is_irreducible' := isIrreducible_preimage_of_isInducing hf.toIsEmbedding.isInducing
    T.isIrreducible hT
  is_closed' := T.isClosed.preimage hf.continuous

theorem preimageIrreducibleCloseds_coe {Y Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → Z} (hf : IsClosedEmbedding f) (T : IrreducibleCloseds Z)
    (hT : (T : Set Z) ⊆ Set.range f) :
    ((preimageIrreducibleCloseds hf T hT : IrreducibleCloseds Y) : Set Y) = f ⁻¹' T := rfl

/-- A scheme covered by finitely many closed curves of dimension at most one has dimension at
most one. -/
theorem topologicalKrullDim_le_one_of_curves (X : Scheme.{u}) {J : Type u} [Fintype J]
    (Cv : J → Scheme.{u}) (c : ∀ j, Cv j ⟶ X) [∀ j, IsClosedImmersion (c j)]
    (hcover : ⋃ j, Set.range (c j).base = Set.univ)
    (hdim : ∀ j, topologicalKrullDim (Cv j) ≤ 1) : topologicalKrullDim X ≤ 1 := by
  show Order.krullDim (IrreducibleCloseds X) ≤ 1
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨j, hj⟩ := exists_curveRange_subset_of_isIrreducible X Cv c hcover (p.last : Set X)
    p.last.isIrreducible
  have hsub : ∀ i, ((p i : IrreducibleCloseds X) : Set X) ⊆ Set.range (c j).base :=
    fun i => (SetLike.coe_subset_coe.mpr (p.strictMono.monotone (Fin.le_last i))).trans hj
  have hstep : ∀ i : Fin p.length,
      preimageIrreducibleCloseds (c j).isClosedEmbedding (p i.castSucc) (hsub _) <
        preimageIrreducibleCloseds (c j).isClosedEmbedding (p i.succ) (hsub _) := by
    intro i
    have hlt := p.step i
    refine lt_of_le_of_ne ?_ ?_
    · show (c j).base ⁻¹' (p i.castSucc : Set X) ⊆ (c j).base ⁻¹' (p i.succ : Set X)
      exact Set.preimage_mono (SetLike.coe_subset_coe.mpr hlt.le)
    · intro heq
      apply hlt.ne
      apply IrreducibleCloseds.ext
      have h := congrArg (fun T : IrreducibleCloseds (Cv j) => (c j).base '' (T : Set (Cv j))) heq
      simp only [preimageIrreducibleCloseds_coe] at h
      rwa [Set.image_preimage_eq_of_subset (hsub _), Set.image_preimage_eq_of_subset (hsub _)] at h
  let q : LTSeries (IrreducibleCloseds (Cv j)) :=
    ⟨p.length, fun i => preimageIrreducibleCloseds (c j).isClosedEmbedding (p i) (hsub i), hstep⟩
  exact le_trans (Order.LTSeries.length_le_krullDim q) (hdim j)

end Dimension

end KltDP.Geometry.RationalTreePicard
