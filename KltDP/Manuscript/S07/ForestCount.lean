import KltDP.Manuscript.S03.RulingFibers
import KltDP.Manuscript.S07.AdjointConfiguration
import KltDP.Support.WeightedForestCore
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Manuscript Lemma 7.1: the connected-component count from a rational ruling

Source: `source/manuscript.tex`, lines 2000–2064, `lem:forest-count`.

For a rational ruling `g : S → P¹` (fibre class `F`) of the resolution surface of a resolution
datum `R`, a vertex `i` of the exceptional dual graph `R.graph` is *vertical* if the curve `i.val`
lies in a fibre (`InFiber g t i.val` for some `t`, equivalently `F · D_i = 0`) and *horizontal*
otherwise. For a finite set `T` of points of `P¹` containing every fibre carrying a vertical
vertex, write

* `s = numHorizontal g` for the number of horizontal vertices,
* `r_t = numPieces g t` for the number of connected pieces of the exceptional vertical part in
  the fibre over `t` (connected components of the graph induced on the vertical vertices over `t`),
* `a_t = mixedIncidences g t` for the number of horizontal–vertical incidences in the fibre over
  `t` (`= Σ_i Σ_j H_i · R_{t,j}` by `mixedIncidences_eq_sum`, since distinct exceptional curves
  meet with intersection number `0` or `1`),
* `q_h = horizontalIncidences g` for the number of horizontal–horizontal incidences.

Then `#π₀(D) = s + Σ_t (r_t − a_t) − q_h` (`forestCount`, in `ℤ`; `forestCount_nat` in `ℕ`).

The proof is the manuscript's: a vertical vertex lies in a (reducible, closed) fibre, edges of the
forest `R.graph` between vertical vertices join vertices of the same fibre, and in a finite forest
`#components = #vertices − #edges` (`KltDP.Support.WeightedForestCore.forest_natCard_edges`),
applied to `R.graph` and to the graph induced on the vertical vertices of each fibre. We do not
contract the pieces to single vertices; instead the edges of `R.graph` are split into
horizontal–horizontal, horizontal–vertical and vertical–vertical edges, the last ones lying inside
single fibres (`forest_component_count`, a statement about an arbitrary finite acyclic graph with
a vertex labelling `V → Option T`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Finset SimpleGraph
open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Manuscript KltDP.Manuscript.S03

universe u v w

namespace KltDP.Manuscript.S07

/-! ### The finite-graph count -/

section Graph

variable {V : Type v} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {T : Type w} [Fintype T] [DecidableEq T] (fib : V → Option T)

/-- The horizontal vertices (`fib v = none`). -/
def horFinset : Finset V := univ.filter fun v => fib v = none

/-- The vertical vertices over `t` (`fib v = some t`). -/
def vertFinset (t : T) : Finset V := univ.filter fun v => fib v = some t

/-- The mixed adjacent pairs `(u, v)`: `u` horizontal, `v` vertical, `u ~ v`. -/
def mixedPairs : Finset (V × V) :=
  univ.filter fun p => fib p.1 = none ∧ fib p.2 ≠ none ∧ G.Adj p.1 p.2

/-- The mixed adjacent pairs whose vertical end lies over `t`. -/
def mixedPairsAt (t : T) : Finset (V × V) :=
  univ.filter fun p => fib p.1 = none ∧ fib p.2 = some t ∧ G.Adj p.1 p.2

/-- The edges with both ends horizontal. -/
def hhEdges : Finset (Sym2 V) := G.edgeFinset ∩ (horFinset fib).sym2

/-- The edges with both ends vertical over `t`. -/
def vvEdges (t : T) : Finset (Sym2 V) := G.edgeFinset ∩ (vertFinset fib t).sym2

/-- The remaining edges (one horizontal and one vertical end, once `fib` is compatible with
adjacency). -/
def mixedEdges : Finset (Sym2 V) :=
  G.edgeFinset \ (hhEdges G fib ∪ univ.biUnion (vvEdges G fib))

omit [Fintype T] in
theorem mem_hhEdges (x y : V) :
    s(x, y) ∈ hhEdges G fib ↔ G.Adj x y ∧ fib x = none ∧ fib y = none := by
  simp only [hhEdges, horFinset, Finset.mem_inter, mem_edgeFinset, mem_edgeSet,
    Finset.mk_mem_sym2_iff, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype T] in
theorem mem_vvEdges (t : T) (x y : V) :
    s(x, y) ∈ vvEdges G fib t ↔ G.Adj x y ∧ fib x = some t ∧ fib y = some t := by
  simp only [vvEdges, vertFinset, Finset.mem_inter, mem_edgeFinset, mem_edgeSet,
    Finset.mk_mem_sym2_iff, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An induced subgraph of an acyclic graph is acyclic. -/
theorem isAcyclic_induce (hG : G.IsAcyclic) (s : Set V) : (G.induce s).IsAcyclic := by
  intro v c hc
  exact hG (c.map (Embedding.induce (G := G) s).toHom) (hc.map (Embedding.induce (G := G) s).injective)

/-- The edges of the graph induced on a finset `s` are the edges of `G` inside `s`
(the map `Sym2.map Subtype.val` is a bijection). -/
theorem natCard_edgeSet_induce_coe (s : Finset V) :
    Nat.card (G.induce (↑s : Set V)).edgeSet = (G.edgeFinset ∩ s.sym2).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective
    (fun e : (G.induce (↑s : Set V)).edgeSet =>
      (⟨Sym2.map Subtype.val e.1, ?_⟩ : {x // x ∈ G.edgeFinset ∩ s.sym2})) ⟨?_, ?_⟩)
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet, comap_adj] at he
      rw [Sym2.map_pair_eq, Finset.mem_inter, mem_edgeFinset, mem_edgeSet,
        Finset.mk_mem_sym2_iff]
      exact ⟨he, Finset.mem_coe.mp a.2, Finset.mem_coe.mp b.2⟩
  · intro e e' hee'
    apply Subtype.ext
    exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val hee')
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h x y =>
      rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mk_mem_sym2_iff] at he
      obtain ⟨hadj, hx, hy⟩ := he
      refine ⟨⟨s(⟨x, Finset.mem_coe.mpr hx⟩, ⟨y, Finset.mem_coe.mpr hy⟩), ?_⟩, ?_⟩
      · rw [mem_edgeSet, comap_adj]
        exact hadj
      · apply Subtype.ext
        simp only [Sym2.map_pair_eq]

omit [DecidableEq V] in
/-- The vertices split into the horizontal ones and the vertical ones over each `t`. -/
theorem card_eq_hor_add_vert :
    Fintype.card V = (horFinset fib).card + ∑ t, (vertFinset fib t).card := by
  rw [← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := fib) (t := univ) (fun _ _ => mem_univ _),
    Fintype.sum_option]
  rfl

omit [Fintype T] in
theorem disjoint_hhEdges_vvEdges (t : T) : Disjoint (hhEdges G fib) (vvEdges G fib t) := by
  rw [Finset.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | h x y =>
    intro he he'
    rw [mem_hhEdges] at he
    rw [mem_vvEdges] at he'
    exact Option.some_ne_none t (he'.2.1.symm.trans he.2.1)

omit [Fintype T] in
theorem disjoint_vvEdges (t t' : T) (htt' : t ≠ t') :
    Disjoint (vvEdges G fib t) (vvEdges G fib t') := by
  rw [Finset.disjoint_left]
  intro e
  induction e using Sym2.ind with
  | h x y =>
    intro he he'
    rw [mem_vvEdges] at he he'
    exact htt' (Option.some_inj.mp (he.2.1.symm.trans he'.2.1))

/-- The edge count splits into the three kinds of edges. -/
theorem card_edgeFinset_decomp :
    G.edgeFinset.card =
      (hhEdges G fib).card + ∑ t, (vvEdges G fib t).card + (mixedEdges G fib).card := by
  have hsub : hhEdges G fib ∪ univ.biUnion (vvEdges G fib) ⊆ G.edgeFinset := by
    apply Finset.union_subset Finset.inter_subset_left
    exact Finset.biUnion_subset.mpr fun t _ => Finset.inter_subset_left
  have h1 : (mixedEdges G fib).card + (hhEdges G fib ∪ univ.biUnion (vvEdges G fib)).card =
      G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hdisj : Disjoint (hhEdges G fib) (univ.biUnion (vvEdges G fib)) := by
    rw [Finset.disjoint_biUnion_right]
    intro t _
    exact disjoint_hhEdges_vvEdges G fib t
  have h2 := Finset.card_union_of_disjoint hdisj
  have h3 : (univ.biUnion (vvEdges G fib)).card = ∑ t, (vvEdges G fib t).card :=
    Finset.card_biUnion fun t _ t' _ htt' => disjoint_vvEdges G fib t t' htt'
  omega

/-- The mixed edges correspond to the mixed adjacent pairs `(horizontal, vertical)`. -/
theorem card_mixedPairs
    (hcross : ∀ u v t t', G.Adj u v → fib u = some t → fib v = some t' → t = t') :
    (mixedPairs G fib).card = (mixedEdges G fib).card := by
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    rw [mixedPairs, Finset.mem_filter] at hp
    obtain ⟨-, hx, hy, hadj⟩ := hp
    rw [mixedEdges, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, mem_edgeFinset,
      mem_edgeSet]
    refine ⟨hadj, ?_⟩
    rintro (h | ⟨t, -, h⟩)
    · rw [mem_hhEdges] at h
      exact hy h.2.2
    · rw [mem_vvEdges] at h
      exact Option.some_ne_none t (h.2.1.symm.trans hx)
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' heq
    rw [mixedPairs, Finset.mem_filter] at hp hp'
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · dsimp only at h1 h2 hp hp'
      rw [h1] at hp
      exact (hp'.2.2.1 hp.2.1).elim
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mixedEdges, Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, mem_edgeFinset,
        mem_edgeSet] at he
      obtain ⟨hadj, hnot⟩ := he
      rcases hx : fib x with _ | t <;> rcases hy : fib y with _ | t'
      · exact absurd (Or.inl ((mem_hhEdges G fib x y).mpr ⟨hadj, hx, hy⟩)) hnot
      · refine ⟨(x, y), ?_, rfl⟩
        rw [mixedPairs, Finset.mem_filter]
        exact ⟨mem_univ _, hx, by rw [hy]; exact Option.some_ne_none t', hadj⟩
      · refine ⟨(y, x), ?_, Sym2.eq_swap⟩
        rw [mixedPairs, Finset.mem_filter]
        exact ⟨mem_univ _, hy, by rw [hx]; exact Option.some_ne_none t, hadj.symm⟩
      · have htt := hcross x y t t' hadj hx hy
        subst htt
        exact absurd (Or.inr ⟨t, mem_univ _, (mem_vvEdges G fib t x y).mpr ⟨hadj, hx, hy⟩⟩) hnot

omit [DecidableEq V] in
/-- The mixed pairs split according to the fibre of the vertical end. -/
theorem card_mixedPairs_eq_sum :
    (mixedPairs G fib).card = ∑ t, (mixedPairsAt G fib t).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : V × V => fib p.2) (t := univ)
    (fun _ _ => mem_univ _), Fintype.sum_option]
  have h0 : ((mixedPairs G fib).filter fun p => fib p.2 = none).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    rw [mixedPairs, Finset.mem_filter] at hp
    exact hp.2.2.1
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  ext p
  simp only [mixedPairs, mixedPairsAt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, -, h3⟩, h4⟩
    exact ⟨h1, h4, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by rw [h2]; exact Option.some_ne_none t, h3⟩, h2⟩

/-- **The forest count** (manuscript Lemma 7.1 as a statement about finite graphs). For a finite
acyclic graph `G` with vertices labelled by `fib : V → Option T` (`none` = horizontal, `some t` =
vertical over `t`) such that adjacent vertical vertices have the same label,
`#components(G) + #(horizontal–vertical incidences) + #(horizontal–horizontal edges)
  = #horizontal + Σ_t #components(G restricted to the vertical vertices over t)`. -/
theorem forest_component_count (hG : G.IsAcyclic)
    (hcross : ∀ u v t t', G.Adj u v → fib u = some t → fib v = some t' → t = t') :
    Nat.card G.ConnectedComponent + (mixedPairs G fib).card
        + Nat.card (G.induce (↑(horFinset fib) : Set V)).edgeSet
      = (horFinset fib).card
        + ∑ t, Nat.card (G.induce (↑(vertFinset fib t) : Set V)).ConnectedComponent := by
  classical
  have h0 := KltDP.Support.WeightedForestCore.forest_natCard_edges G hG
  rw [Nat.card_eq_fintype_card (α := V), card_eq_hor_add_vert fib] at h0
  have hEG : Nat.card G.edgeSet = G.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, edgeFinset_card]
  have hE := card_edgeFinset_decomp G fib
  have hmix := card_mixedPairs G fib hcross
  have hhh : Nat.card (G.induce (↑(horFinset fib) : Set V)).edgeSet = (hhEdges G fib).card :=
    natCard_edgeSet_induce_coe G (horFinset fib)
  have hvv : ∀ t, Nat.card (G.induce (↑(vertFinset fib t) : Set V)).edgeSet
      + Nat.card (G.induce (↑(vertFinset fib t) : Set V)).ConnectedComponent
      = (vertFinset fib t).card := by
    intro t
    have h := KltDP.Support.WeightedForestCore.forest_natCard_edges
      (G.induce (↑(vertFinset fib t) : Set V)) (isAcyclic_induce G hG _)
    rw [h, Set.Nat.card_coe_set_eq, Set.ncard_coe_Finset]
  have hvv' : ∀ t, Nat.card (G.induce (↑(vertFinset fib t) : Set V)).edgeSet =
      (vvEdges G fib t).card := fun t => natCard_edgeSet_induce_coe G _
  have hsum : ∑ t, (vvEdges G fib t).card
      + ∑ t, Nat.card (G.induce (↑(vertFinset fib t) : Set V)).ConnectedComponent
      = ∑ t, (vertFinset fib t).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [← hvv' t]; exact hvv t
  omega

end Graph

/-! ### The datum: horizontal and vertical exceptional curves -/

section Datum

variable {k : Type u} [Field k] [IsAlgClosed k] {R : ResolutionDatum k}
  (F : CartierDivisor R.S.toScheme)
  (g : R.S.toScheme ⟶ projectiveSpace k 1)
  (hg : g ≫ projectiveSpaceToSpec k 1 = R.S.structureMorphism)
  (e : (pullbackInvertibleSheaf g (ProjectiveSpaceDegreeOneSheaf.degreeOne k 1)).obj ≅
    cartierDivisorModule R.S.toScheme F)

/-- A vertex of the exceptional graph is *horizontal* for the ruling `g` if its curve lies in no
fibre (manuscript: "a component of `D` is vertical if it lies in a fibre and horizontal
otherwise"). -/
def IsHorizontal (i : R.Vertices) : Prop := ∀ t : projectiveSpace k 1, ¬ InFiber g t i.val

/-- A prime curve lies in at most one fibre. -/
theorem inFiber_unique {t t' : projectiveSpace k 1} {C : R.S.PrimeCurve} (h : InFiber g t C)
    (h' : InFiber g t' C) : t = t' := by
  obtain ⟨x, hx⟩ := C.isIrreducible.nonempty
  exact (h x hx).symm.trans (h' x hx)

include hg e in
/-- Horizontal means `F · D_i ≠ 0` (verticality criterion of Lemma 3.1). -/
theorem isHorizontal_iff (i : R.Vertices) :
    IsHorizontal g i ↔ i.val.intersectionNumber F ≠ 0 := by
  rw [Ne, intersectionNumber_eq_zero_iff_vertical R F g hg e i.val]
  exact not_exists.symm

/-- Adjacent vertical vertices lie in the same fibre (fibres over distinct points are disjoint). -/
theorem adj_inFiber_eq {i j : R.Vertices} (h : R.graph.Adj i j) {t t' : projectiveSpace k 1}
    (hi : InFiber g t i.val) (hj : InFiber g t' j.val) : t = t' := by
  obtain ⟨x, hxi, hxj⟩ := h.2
  exact (hi x hxi).symm.trans (hj x hxj)

/-- Distinct exceptional curves meet with intersection number `0` or `1` (forest structure of the
exceptional divisor, `exceptional_forest_and_singular_count_from_klt`): `D_i · D_j = 1` if the
vertices are adjacent (the curves meet) and `D_i · D_j = 0` otherwise. -/
theorem contact_eq_one_of_adj {i j : R.Vertices} (h : R.graph.Adj i j) :
    R.contact i.val j = 1 := by
  have hij : i ≠ j := h.1
  have hle := (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.2 i j hij
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hnn := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg R.S R.hreg
    i.val j.val hne
  have hiff := PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg i.val j.val hne
  have hcontact : R.contact i.val j = R.S.intersectionPairing R.hreg
      (R.S.primeCurveCartier R.hreg i.val) (R.S.primeCurveCartier R.hreg j.val) :=
    (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg
      i.val j.val).symm
  have h0 : R.S.intersectionPairing R.hreg (R.S.primeCurveCartier R.hreg i.val)
      (R.S.primeCurveCartier R.hreg j.val) ≠ 0 := fun h0 =>
    (Set.not_disjoint_iff_nonempty_inter.mpr h.2) (hiff.mp h0)
  rw [hcontact]
  omega

theorem contact_eq_zero_of_not_adj {i j : R.Vertices} (hij : i ≠ j) (h : ¬ R.graph.Adj i j) :
    R.contact i.val j = 0 := by
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hiff := PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_zero_iff_disjoint
    R.S R.hreg i.val j.val hne
  have hcontact : R.contact i.val j = R.S.intersectionPairing R.hreg
      (R.S.primeCurveCartier R.hreg i.val) (R.S.primeCurveCartier R.hreg j.val) :=
    (PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber R.S R.hreg
      i.val j.val).symm
  rw [hcontact]
  apply hiff.mpr
  by_contra hnd
  apply h
  show i ≠ j ∧ ((i.val : Set R.S.toScheme) ∩ (j.val : Set R.S.toScheme)).Nonempty
  exact ⟨hij, Set.not_disjoint_iff_nonempty_inter.mp hnd⟩

/-- An exceptional curve has self-intersection at most `-2` (`w_i ≥ 2`). -/
theorem selfIntersection_le_neg_two (i : R.Vertices) :
    i.val.selfIntersectionNumber R.hreg ≤ -2 := by
  have h := R.two_le_w i
  change (2 : ℚ) ≤ -(R.S.intersectionPairing R.hreg
    (R.S.primeCurveCartier R.hreg i.val) (R.S.primeCurveCartier R.hreg i.val) : ℚ) at h
  rw [R.S.intersectionPairing_primeCurve R.hreg] at h
  have h' : ((i.val.intersectionNumber (R.S.primeCurveCartier R.hreg i.val) : ℤ) : ℚ) ≤ -2 := by
    linarith
  exact_mod_cast h'

include hg e in
/-- A vertical exceptional curve lies in a closed reducible fibre: closedness from the verticality
criterion, reducibility because an irreducible fibre is a curve of square `0` while exceptional
curves have square `≤ -2` (manuscript lines 2049–2051). -/
theorem inFiber_exceptional_closed_reducible [IsProper g] [Surjective g]
    (hFF : R.S.intersectionPairing R.hreg F F = 0)
    (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
    (i : R.Vertices) (t : projectiveSpace k 1) (hi : InFiber g t i.val) :
    IsClosed ({t} : Set (projectiveSpace k 1)) ∧
      ∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C' := by
  have h0 : i.val.intersectionNumber F = 0 :=
    intersectionNumber_eq_zero_of_vertical R F g hg e i.val t hi
  obtain ⟨t', ht', hi'⟩ := exists_vertical_of_intersectionNumber_eq_zero R F g hg e i.val h0
  have htt : t' = t := inFiber_unique g hi' hi
  subst htt
  refine ⟨ht', ?_⟩
  obtain ⟨E, hE⟩ := exists_isFiberDivisor R F g e t' ht'
  by_contra hnot
  push_neg at hnot
  have hirr : ∀ C', InFiber g t' C' → C' = i.val := fun C' hC' => hnot C' i.val hC' hi
  have hsq := (irreducibleFiber_component R F hFF hKF g hE i.val hi hirr).2.2.1
  have hle := selfIntersection_le_neg_two i
  omega

/-! ### The fibre labelling and the counts -/

open Classical in
/-- The fibre label of a vertex relative to a finite set `T` of points of `P¹`: `some t` if the
curve lies in the fibre over `t ∈ T`, `none` otherwise. -/
def fiberIndex (T : Finset (projectiveSpace k 1)) (i : R.Vertices) : Option T :=
  if h : ∃ t ∈ T, InFiber g t i.val then some ⟨h.choose, h.choose_spec.1⟩ else none

theorem fiberIndex_eq_some_iff (T : Finset (projectiveSpace k 1)) (i : R.Vertices) (t : T) :
    fiberIndex g T i = some t ↔ InFiber g t.1 i.val := by
  unfold fiberIndex
  split_ifs with h
  · constructor
    · intro heq
      rw [← Option.some_inj.mp heq]
      exact h.choose_spec.2
    · intro hin
      congr 1
      exact Subtype.ext (inFiber_unique g h.choose_spec.2 hin)
  · constructor
    · intro heq
      simp at heq
    · intro hin
      exact (h ⟨t.1, t.2, hin⟩).elim

theorem fiberIndex_eq_none_iff (T : Finset (projectiveSpace k 1))
    (hT : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T)
    (i : R.Vertices) : fiberIndex g T i = none ↔ IsHorizontal g i := by
  unfold fiberIndex
  split_ifs with h
  · constructor
    · intro heq
      simp at heq
    · intro hhor
      obtain ⟨t, -, ht⟩ := h
      exact (hhor t ht).elim
  · constructor
    · intro _ t ht
      exact h ⟨t, hT i t ht, ht⟩
    · intro _
      rfl

open Classical in
/-- `s`: the number of horizontal exceptional curves. -/
def numHorizontal : ℕ := (Finset.univ.filter fun i : R.Vertices => IsHorizontal g i).card

/-- `r_t`: the number of connected pieces of the exceptional vertical part in the fibre over `t`
(connected components of the graph induced on the vertical vertices over `t`). -/
def numPieces (t : projectiveSpace k 1) : ℕ :=
  Nat.card (R.graph.induce {i : R.Vertices | InFiber g t i.val}).ConnectedComponent

open Classical in
/-- `a_t`: the number of horizontal–vertical incidences in the fibre over `t`, i.e. of pairs
`(H, C)` of a horizontal vertex `H` and a vertical vertex `C` over `t` which meet. -/
def mixedIncidences (t : projectiveSpace k 1) : ℕ :=
  (Finset.univ.filter fun p : R.Vertices × R.Vertices =>
    IsHorizontal g p.1 ∧ InFiber g t p.2.val ∧ R.graph.Adj p.1 p.2).card

/-- `q_h`: the number of horizontal–horizontal incidences (edges of the graph induced on the
horizontal vertices). -/
def horizontalIncidences : ℕ :=
  Nat.card (R.graph.induce {i : R.Vertices | IsHorizontal g i}).edgeSet

/-- **Manuscript Lemma 7.1** (`lem:forest-count`, lines 2000–2064), additive form: for a finite set
`T` of points of `P¹` containing every fibre carrying a vertical exceptional curve,
`#π₀(D) + Σ_{t ∈ T} a_t + q_h = s + Σ_{t ∈ T} r_t`. -/
theorem forestCount_nat (T : Finset (projectiveSpace k 1))
    (hT : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T) :
    Nat.card R.graph.ConnectedComponent + ∑ t ∈ T, mixedIncidences g t + horizontalIncidences g
      = numHorizontal g + ∑ t ∈ T, numPieces g t := by
  classical
  have hforest : R.graph.IsAcyclic :=
    (R.hmin.exceptional_forest_and_singular_count_from_klt R.hklt).2.2.1
  have hcross : ∀ (u v : R.Vertices) (t t' : T), R.graph.Adj u v →
      fiberIndex g T u = some t → fiberIndex g T v = some t' → t = t' := by
    intro u v t t' hadj hu hv
    rw [fiberIndex_eq_some_iff] at hu hv
    exact Subtype.ext (adj_inFiber_eq g hadj hu hv)
  have key := forest_component_count R.graph (fiberIndex g T) hforest hcross
  -- the horizontal vertices
  have hhorSet : (↑(horFinset (fiberIndex g T)) : Set R.Vertices) = {i | IsHorizontal g i} := by
    ext i
    rw [Finset.mem_coe, horFinset, Finset.mem_filter, Set.mem_setOf_eq]
    simp only [Finset.mem_univ, true_and]
    exact fiberIndex_eq_none_iff g T hT i
  have hcardHor : (horFinset (fiberIndex g T)).card = numHorizontal g := by
    unfold numHorizontal
    congr 1
    ext i
    simp only [horFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fiberIndex_eq_none_iff g T hT i
  have hhh : Nat.card (R.graph.induce (↑(horFinset (fiberIndex g T)) : Set R.Vertices)).edgeSet =
      horizontalIncidences g := by
    unfold horizontalIncidences
    exact congrArg (fun s : Set R.Vertices => Nat.card (R.graph.induce s).edgeSet) hhorSet
  -- the vertical vertices over `t`
  have hvertSet : ∀ t : T, (↑(vertFinset (fiberIndex g T) t) : Set R.Vertices) =
      {i | InFiber g t.1 i.val} := by
    intro t
    ext i
    rw [Finset.mem_coe, vertFinset, Finset.mem_filter, Set.mem_setOf_eq]
    simp only [Finset.mem_univ, true_and]
    exact fiberIndex_eq_some_iff g T i t
  have hpieces : ∑ t : T, Nat.card (R.graph.induce
      (↑(vertFinset (fiberIndex g T) t) : Set R.Vertices)).ConnectedComponent
      = ∑ t ∈ T, numPieces g t := by
    rw [← Finset.sum_coe_sort T]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold numPieces
    exact congrArg (fun s : Set R.Vertices => Nat.card (R.graph.induce s).ConnectedComponent)
      (hvertSet t)
  -- the mixed incidences
  have hmixAt : ∀ t : T, (mixedPairsAt R.graph (fiberIndex g T) t).card = mixedIncidences g t.1 := by
    intro t
    unfold mixedPairsAt mixedIncidences
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fiberIndex_eq_none_iff g T hT, fiberIndex_eq_some_iff]
  have hmix : (mixedPairs R.graph (fiberIndex g T)).card = ∑ t ∈ T, mixedIncidences g t := by
    rw [card_mixedPairs_eq_sum, ← Finset.sum_coe_sort T]
    exact Finset.sum_congr rfl fun t _ => hmixAt t
  rw [hcardHor, hhh, hpieces, hmix] at key
  exact key

/-- **Manuscript Lemma 7.1** (`lem:forest-count`, equation `eq:collapsed-fiber-euler`):
`#π₀(D) = s + Σ_{t ∈ T} (r_t − a_t) − q_h`. -/
theorem forestCount (T : Finset (projectiveSpace k 1))
    (hT : ∀ (i : R.Vertices) (t : projectiveSpace k 1), InFiber g t i.val → t ∈ T) :
    (Nat.card R.graph.ConnectedComponent : ℤ)
      = numHorizontal g + ∑ t ∈ T, ((numPieces g t : ℤ) - mixedIncidences g t)
        - horizontalIncidences g := by
  have h := congrArg (Nat.cast (R := ℤ)) (forestCount_nat g T hT)
  push_cast at h
  rw [Finset.sum_sub_distrib]
  linarith

include hg e in
/-- Lemma 7.1 with `T` any finite set of points containing all closed points with reducible fibre
(for instance the finite set of reducible fibres, `rulingFibers_reducibleFibers_finite`). -/
theorem forestCount_of_reducible_subset [IsProper g] [Surjective g]
    (hFF : R.S.intersectionPairing R.hreg F F = 0)
    (hKF : R.S.intersectionPairing R.hreg R.KS F = -2)
    (T : Finset (projectiveSpace k 1))
    (hT : ∀ t : projectiveSpace k 1, IsClosed ({t} : Set (projectiveSpace k 1)) →
      (∃ C C' : R.S.PrimeCurve, InFiber g t C ∧ InFiber g t C' ∧ C ≠ C') → t ∈ T) :
    (Nat.card R.graph.ConnectedComponent : ℤ)
      = numHorizontal g + ∑ t ∈ T, ((numPieces g t : ℤ) - mixedIncidences g t)
        - horizontalIncidences g := by
  apply forestCount g T
  intro i t hi
  obtain ⟨hcl, hred⟩ := inFiber_exceptional_closed_reducible F g hg e hFF hKF i t hi
  exact hT t hcl hred

/-! ### The incidence counts as intersection numbers -/

open Classical in
/-- `a_t = Σ_{i horizontal} Σ_{j vertical over t} H_i · D_j` (the manuscript's
`Σ_i Σ_j H_i · R_{t,j}`), since distinct exceptional curves have intersection number `0` or `1`. -/
theorem mixedIncidences_eq_sum (t : projectiveSpace k 1) :
    (mixedIncidences g t : ℤ) =
      ∑ i ∈ Finset.univ.filter (fun i : R.Vertices => IsHorizontal g i),
        ∑ j ∈ Finset.univ.filter (fun j : R.Vertices => InFiber g t j.val), R.contact i.val j := by
  unfold mixedIncidences
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]
  by_cases hi : IsHorizontal g i
  · rw [if_pos hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : InFiber g t j.val
    · rw [if_pos hj]
      have hij : i ≠ j := fun h => hi t (h ▸ hj)
      by_cases hadj : R.graph.Adj i j
      · rw [if_pos ⟨hi, hj, hadj⟩, contact_eq_one_of_adj hadj]
      · rw [if_neg (fun h => hadj h.2.2), contact_eq_zero_of_not_adj hij hadj]
    · rw [if_neg hj, if_neg (fun h => hj h.2.1)]
  · rw [if_neg hi]
    exact Finset.sum_eq_zero fun j _ => if_neg (fun h => hi h.1)

end Datum

end KltDP.Manuscript.S07

#print axioms KltDP.Manuscript.S07.forest_component_count
#print axioms KltDP.Manuscript.S07.forestCount_nat
#print axioms KltDP.Manuscript.S07.forestCount
#print axioms KltDP.Manuscript.S07.forestCount_of_reducible_subset
#print axioms KltDP.Manuscript.S07.mixedIncidences_eq_sum
#print axioms KltDP.Manuscript.S07.contact_eq_one_of_adj
