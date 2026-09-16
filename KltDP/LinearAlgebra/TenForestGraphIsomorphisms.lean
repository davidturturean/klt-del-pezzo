import KltDP.LinearAlgebra.TenForestClassification
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-!
# Marked weighted isomorphisms for the candidate forests

The finite graph isomorphisms in this module are constructed from actual
edge finsets and actual isolated complements. The complement is numbered
only after its cardinality has been proved. The core vertices retain their
labels under the resulting isomorphism, and every vertex retains its weight.

These are adapters for the graph data produced by the candidate classifier,
not assumptions restricting its original search space. The explicit A1,
A2 and B models include their isolated vertices and the unused-edge A2
completion. Further family adapters are separate obligations.

Reuse: pinned SimpleGraph sums, Sym2.map injectivity, Equiv.ofInjective,
Equiv.Set.sumCompl, and Fintype.equivFinOfCardEq; the existing actual
outsideRange API. The newer official graph-sum API was also inspected.
No source port, new axiom, or finite search is needed for these isomorphisms.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

section Complement

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Number the actual complementary vertices after their count is proved,
while preserving the values of every supplied core label. -/
def labeledComplementEquiv (e : I ↪ V) (m : ℕ)
    (hcard : Fintype.card {v // v ∉ Set.range e} = m) : I ⊕ Fin m ≃ V := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective)
    (Fintype.equivFinOfCardEq hcard).symm).trans (Equiv.Set.sumCompl (Set.range e))

theorem labeledComplementEquiv_inl (e : I ↪ V) (m : ℕ)
    (hcard : Fintype.card {v // v ∉ Set.range e} = m) (i : I) :
    labeledComplementEquiv e m hcard (Sum.inl i) = e i := rfl

theorem labeledComplementEquiv_inr_not_mem (e : I ↪ V) (m : ℕ)
    (hcard : Fintype.card {v // v ∉ Set.range e} = m) (i : Fin m) :
    labeledComplementEquiv e m hcard (Sum.inr i) ∉ Set.range e :=
  ((Fintype.equivFinOfCardEq hcard).symm i).property

/-- The actual cardinality of the complement of an embedded finite core. -/
theorem card_labeled_complement (e : I ↪ V) :
    Fintype.card {v // v ∉ Set.range e} = Fintype.card V - Fintype.card I := by
  classical
  rw [Fintype.card_subtype_compl]
  have hrange : Fintype.card {v // v ∈ Set.range e} = Fintype.card I :=
    (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm
  rw [hrange]

/-- A specified core and its actual isolated complement give a graph
isomorphism which fixes every core label. -/
def labeledIsolatedComplementIso (G : SimpleGraph V) (H : SimpleGraph I)
    (e : I ↪ V) (m : ℕ) (hcard : Fintype.card {v // v ∉ Set.range e} = m)
    (hcore : ∀ i j, G.Adj (e i) (e j) ↔ H.Adj i j)
    (houtside : ∀ v, v ∉ Set.range e → ∀ w, ¬ G.Adj v w) :
    (H ⊕g (⊥ : SimpleGraph (Fin m))) ≃g G where
  toEquiv := labeledComplementEquiv e m hcard
  map_rel_iff' := by
    rintro (i | i) (j | j)
    · change G.Adj (e i) (e j) ↔ H.Adj i j
      exact hcore i j
    · have hnone : ¬ G.Adj (e i) (labeledComplementEquiv e m hcard (Sum.inr j)) :=
        fun h => houtside _ (labeledComplementEquiv_inr_not_mem e m hcard j) _ h.symm
      simpa [SimpleGraph.sum, labeledComplementEquiv_inl] using (iff_false_intro hnone)
    · have hnone : ¬ G.Adj (labeledComplementEquiv e m hcard (Sum.inr i)) (e j) :=
        houtside _ (labeledComplementEquiv_inr_not_mem e m hcard i) _
      simpa [SimpleGraph.sum, labeledComplementEquiv_inl] using (iff_false_intro hnone)
    · change G.Adj (labeledComplementEquiv e m hcard (Sum.inr i))
        (labeledComplementEquiv e m hcard (Sum.inr j)) ↔ False
      exact iff_false_intro (houtside _ (labeledComplementEquiv_inr_not_mem e m hcard i) _)

/-- A finite edge list on the actual embedded core determines the induced
core adjacency, with loops excluded by the actual graph. -/
theorem core_adj_of_edgeFinset_image (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : I ↪ V) (edges : Finset (Sym2 I))
    (hedges : G.edgeFinset = edges.image (Sym2.map e)) (i j : I) :
    G.Adj (e i) (e j) ↔ (SimpleGraph.fromEdgeSet (edges : Set (Sym2 I))).Adj i j := by
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · intro hij
    have hm : s(e i, e j) ∈ G.edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hij
    rw [hedges] at hm
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
    have heq' : a = s(i, j) := (Sym2.map.injective e.injective) heq
    exact ⟨heq' ▸ ha, fun h => hij.ne (congrArg e h)⟩
  · rintro ⟨hmem, _⟩
    have hm : s(e i, e j) ∈ G.edgeFinset := by
      rw [hedges]
      exact Finset.mem_image.mpr ⟨s(i, j), hmem, rfl⟩
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hm

/-- Vertices outside the actual image cannot meet an edge when the complete
edge finset is the image of an edge list on the core. -/
theorem isolated_outside_edgeFinset_image (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : I ↪ V) (edges : Finset (Sym2 I))
    (hedges : G.edgeFinset = edges.image (Sym2.map e)) :
    ∀ v, v ∉ Set.range e → ∀ w, ¬ G.Adj v w := by
  intro v hv w hvw
  have hm : s(v, w) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hvw
  rw [hedges] at hm
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
  have hmem : v ∈ Sym2.map e a := ha.symm ▸ Sym2.mem_mk_left v w
  obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp hmem
  exact hv ⟨i, hi⟩

/-- Complete actual edge and weight data give a weighted isomorphism,
including the named core vertices and the numbered isolated complement. -/
theorem exists_weighted_iso_of_edgeFinset_image
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (e : I ↪ V) (edges : Finset (Sym2 I)) (coreWeight : I → ℕ) (m : ℕ)
    (hcard : Fintype.card {v // v ∉ Set.range e} = m)
    (hedges : G.edgeFinset = edges.image (Sym2.map e))
    (hweight : ∀ i, weight (e i) = coreWeight i)
    (houtside : ∀ v, v ∉ Set.range e → weight v = 2) :
    ∃ f : ((SimpleGraph.fromEdgeSet (edges : Set (Sym2 I))) ⊕g
        (⊥ : SimpleGraph (Fin m))) ≃g G,
      (∀ i, f (Sum.inl i) = e i) ∧
      ∀ v, weight (f v) = Sum.elim coreWeight (fun _ => 2) v := by
  let f := labeledIsolatedComplementIso G
    (SimpleGraph.fromEdgeSet (edges : Set (Sym2 I))) e m hcard
    (core_adj_of_edgeFinset_image G e edges hedges)
    (isolated_outside_edgeFinset_image G e edges hedges)
  refine ⟨f, fun i => labeledComplementEquiv_inl e m hcard i, ?_⟩
  rintro (i | i)
  · exact hweight i
  · exact houtside _ (labeledComplementEquiv_inr_not_mem e m hcard i)

end Complement

section ABModels

/-- The A1 model has core labels `[C,T,B1,B2]`, one edge `C-T`, and
six isolated canonical vertices. -/
def familyA1CoreEdges : Finset (Sym2 (Fin 4)) := {s(0, 1)}

def familyA1CoreWeight : Fin 4 → ℕ := ![2, 3, 3, 3]

def familyA1Graph : SimpleGraph (Fin 4 ⊕ Fin 6) :=
  SimpleGraph.fromEdgeSet (familyA1CoreEdges : Set (Sym2 (Fin 4))) ⊕g ⊥

def familyA1GraphWeight : Fin 4 ⊕ Fin 6 → ℕ :=
  Sum.elim familyA1CoreWeight (fun _ => 2)

/-- The A2 core labels are `[u,v,C,T,B1,B2]`. The first edge is the
additional canonical component; four isolated canonical vertices remain. -/
def familyA2CoreEdges : Finset (Sym2 (Fin 6)) := {s(2, 3), s(0, 1)}

def familyA2CoreWeight : Fin 6 → ℕ := ![2, 2, 2, 3, 3, 3]

def familyA2Graph : SimpleGraph (Fin 6 ⊕ Fin 4) :=
  SimpleGraph.fromEdgeSet (familyA2CoreEdges : Set (Sym2 (Fin 6))) ⊕g ⊥

def familyA2GraphWeight : Fin 6 ⊕ Fin 4 → ℕ :=
  Sum.elim familyA2CoreWeight (fun _ => 2)

/-- The B core labels are `[M,C,T,B1,B2]`, with the two edges `C-M-T`
and five isolated canonical vertices. -/
def familyBCoreEdges : Finset (Sym2 (Fin 5)) := {s(1, 0), s(0, 2)}

def familyBCoreWeight : Fin 5 → ℕ := ![2, 2, 3, 3, 3]

def familyBGraph : SimpleGraph (Fin 5 ⊕ Fin 5) :=
  SimpleGraph.fromEdgeSet (familyBCoreEdges : Set (Sym2 (Fin 5))) ⊕g ⊥

def familyBGraphWeight : Fin 5 ⊕ Fin 5 → ℕ :=
  Sum.elim familyBCoreWeight (fun _ => 2)

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem familyA_labels_injective (weight : V → ℕ) (C T B D : V)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) :
    Function.Injective (![C, T, B, D] : Fin 4 → V) := by
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  simp [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Matrix.range_empty,
    Function.injective_of_subsingleton, hCT, hCB, hCD, hTB, hTD, hBD]

/-- The exact A1 edge set and actual weights yield a marked weighted graph
isomorphism, including all six isolated vertices. -/
theorem familyA1_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C T B D : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hedges : G.edgeFinset = {s(C, T)})
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2) :
    ∃ f : familyA1Graph ≃g G,
      f (Sum.inl 0) = C ∧ f (Sum.inl 1) = T ∧
      f (Sum.inl 2) = B ∧ f (Sum.inl 3) = D ∧
      ∀ v, weight (f v) = familyA1GraphWeight v := by
  let e : Fin 4 ↪ V := ⟨![C, T, B, D],
    familyA_labels_injective weight C T B D hC hT hB hD hTB hTD hBD⟩
  have hcount : Fintype.card {v // v ∉ Set.range e} = 6 := by
    rw [card_labeled_complement, hcard]
    norm_num
  have he : G.edgeFinset = familyA1CoreEdges.image (Sym2.map e) := by
    simpa only [familyA1CoreEdges, Finset.image_singleton, Sym2.map_pair_eq] using hedges
  have hw : ∀ i, weight (e i) = familyA1CoreWeight i := by
    intro i
    fin_cases i <;> simp [e, familyA1CoreWeight, hC, hT, hB, hD]
  have ho : ∀ v, v ∉ Set.range e → weight v = 2 := by
    intro v hv
    apply hother v
    · intro h; exact hv ⟨2, h.symm⟩
    · intro h; exact hv ⟨3, h.symm⟩
    · intro h; exact hv ⟨1, h.symm⟩
  obtain ⟨f, hf, hwf⟩ := exists_weighted_iso_of_edgeFinset_image G weight e
    familyA1CoreEdges familyA1CoreWeight 6 hcount he hw ho
  exact ⟨f, hf 0, hf 1, hf 2, hf 3, hwf⟩

/-- The A2 completion is an actual second canonical edge, disjoint from
the named core. The resulting isomorphism preserves both of its endpoints. -/
theorem familyA2_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C T B D u v : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (huv : u ≠ v) (hu : u ∉ ({C, T, B, D} : Finset V))
    (hv : v ∉ ({C, T, B, D} : Finset V))
    (hedges : G.edgeFinset = {s(C, T), s(u, v)})
    (hother : ∀ w, w ≠ B → w ≠ D → w ≠ T → weight w = 2) :
    ∃ f : familyA2Graph ≃g G,
      f (Sum.inl 0) = u ∧ f (Sum.inl 1) = v ∧
      f (Sum.inl 2) = C ∧ f (Sum.inl 3) = T ∧
      f (Sum.inl 4) = B ∧ f (Sum.inl 5) = D ∧
      ∀ w, weight (f w) = familyA2GraphWeight w := by
  have hu' : u ≠ C ∧ u ≠ T ∧ u ≠ B ∧ u ≠ D := by simpa only
    [Finset.mem_insert, Finset.mem_singleton, not_or] using hu
  have hv' : v ≠ C ∧ v ≠ T ∧ v ≠ B ∧ v ≠ D := by simpa only
    [Finset.mem_insert, Finset.mem_singleton, not_or] using hv
  have hu2 := hother u hu'.2.2.1 hu'.2.2.2 hu'.2.1
  have hv2 := hother v hv'.2.2.1 hv'.2.2.2 hv'.2.1
  have hbase := familyA_labels_injective weight C T B D hC hT hB hD hTB hTD hBD
  have hlabels : Function.Injective (![u, v, C, T, B, D] : Fin 6 → V) := by
    apply Fin.cons_injective_of_injective
    · simp [Matrix.vecCons, Fin.range_cons, Matrix.range_empty, huv,
        hu'.1, hu'.2.1, hu'.2.2.1, hu'.2.2.2]
    · apply Fin.cons_injective_of_injective
      · simp [Matrix.vecCons, Fin.range_cons, Matrix.range_empty,
          hv'.1, hv'.2.1, hv'.2.2.1, hv'.2.2.2]
      · exact hbase
  let e : Fin 6 ↪ V := ⟨![u, v, C, T, B, D], hlabels⟩
  have hcount : Fintype.card {w // w ∉ Set.range e} = 4 := by
    rw [card_labeled_complement, hcard]
    norm_num
  have he : G.edgeFinset = familyA2CoreEdges.image (Sym2.map e) := by
    simpa only [familyA2CoreEdges, Finset.image_insert, Finset.image_singleton,
      Sym2.map_pair_eq] using hedges
  have hw : ∀ i, weight (e i) = familyA2CoreWeight i := by
    intro i
    fin_cases i <;> simp [e, familyA2CoreWeight, hu2, hv2, hC, hT, hB, hD]
  have ho : ∀ w, w ∉ Set.range e → weight w = 2 := by
    intro w hw
    apply hother w
    · intro h; exact hw ⟨4, h.symm⟩
    · intro h; exact hw ⟨5, h.symm⟩
    · intro h; exact hw ⟨3, h.symm⟩
  obtain ⟨f, hf, hwf⟩ := exists_weighted_iso_of_edgeFinset_image G weight e
    familyA2CoreEdges familyA2CoreWeight 4 hcount he hw ho
  exact ⟨f, hf 0, hf 1, hf 2, hf 3, hf 4, hf 5, hwf⟩

/-- The actual B path and exhausted edge set give the marked model with
its middle vertex and all five isolated canonical vertices preserved. -/
theorem familyB_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M T B D : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D) (hCM : G.Adj C M)
    (hedges : G.edgeFinset = {s(C, M), s(M, T)})
    (hother : ∀ w, w ≠ B → w ≠ D → w ≠ T → weight w = 2) :
    ∃ f : familyBGraph ≃g G,
      f (Sum.inl 0) = M ∧ f (Sum.inl 1) = C ∧ f (Sum.inl 2) = T ∧
      f (Sum.inl 3) = B ∧ f (Sum.inl 4) = D ∧
      ∀ w, weight (f w) = familyBGraphWeight w := by
  have hMT : M ≠ T := by intro h; have := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  have hbase := familyA_labels_injective weight C T B D hC hT hB hD hTB hTD hBD
  have hlabels : Function.Injective (![M, C, T, B, D] : Fin 5 → V) := by
    apply Fin.cons_injective_of_injective
    · simp [Matrix.vecCons, Fin.range_cons, Matrix.range_empty,
        Ne.symm hCM.ne, hMT, hMB, hMD]
    · exact hbase
  let e : Fin 5 ↪ V := ⟨![M, C, T, B, D], hlabels⟩
  have hcount : Fintype.card {w // w ∉ Set.range e} = 5 := by
    rw [card_labeled_complement, hcard]
    norm_num
  have he : G.edgeFinset = familyBCoreEdges.image (Sym2.map e) := by
    simpa only [familyBCoreEdges, Finset.image_insert, Finset.image_singleton,
      Sym2.map_pair_eq] using hedges
  have hw : ∀ i, weight (e i) = familyBCoreWeight i := by
    intro i
    fin_cases i <;> simp [e, familyBCoreWeight, hM, hC, hT, hB, hD]
  have ho : ∀ w, w ∉ Set.range e → weight w = 2 := by
    intro w hw
    apply hother w
    · intro h; exact hw ⟨3, h.symm⟩
    · intro h; exact hw ⟨4, h.symm⟩
    · intro h; exact hw ⟨2, h.symm⟩
  obtain ⟨f, hf, hwf⟩ := exists_weighted_iso_of_edgeFinset_image G weight e
    familyBCoreEdges familyBCoreWeight 5 hcount he hw ho
  exact ⟨f, hf 0, hf 1, hf 2, hf 3, hf 4, hwf⟩

/-- The actual A/B classifier outputs imply one of the three marked
weighted model isomorphisms. The canonical weights outside the core are
derived separately from each row's actual leftover vertices. -/
theorem ABForestRows_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C T B D : V)
    (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hT : weight T = 3) (hB : weight B = 3) (hD : weight D = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hrows : ABForestRows G weight coeff C B D T) :
    (∃ f : familyA1Graph ≃g G,
      f (Sum.inl 0) = C ∧ f (Sum.inl 1) = T ∧
      f (Sum.inl 2) = B ∧ f (Sum.inl 3) = D ∧
      ∀ v, weight (f v) = familyA1GraphWeight v) ∨
    (∃ f : familyA2Graph ≃g G,
      f (Sum.inl 2) = C ∧ f (Sum.inl 3) = T ∧
      f (Sum.inl 4) = B ∧ f (Sum.inl 5) = D ∧
      ∀ v, weight (f v) = familyA2GraphWeight v) ∨
    (∃ f : familyBGraph ≃g G,
      f (Sum.inl 1) = C ∧ f (Sum.inl 2) = T ∧
      f (Sum.inl 3) = B ∧ f (Sum.inl 4) = D ∧
      ∀ v, weight (f v) = familyBGraphWeight v) := by
  obtain ⟨_, _, hcases⟩ := hrows
  rcases hcases with ⟨he, _, hr, _⟩ |
      ⟨u, v, huv, hu, hv, hu2, hv2, he, _, hr, _⟩ |
      ⟨M, hM, hCM, _, he, _, hr, _⟩
  · have hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
      intro v hvB hvD hvT
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvT, hvB, hvD⟩)).1
    exact Or.inl (familyA1_weighted_graph_iso G weight C T B D hcard
      hC hT hB hD hTB hTD hBD he hother)
  · have hother : ∀ w, w ≠ B → w ≠ D → w ≠ T → weight w = 2 := by
      intro w hwB hwD hwT
      by_cases hwu : w = u
      · simpa only [hwu] using hu2
      by_cases hwv : w = v
      · simpa only [hwv] using hv2
      by_cases hwC : w = C
      · simpa only [hwC] using hC
      · exact (hr w (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hwu, hwv, hwC, hwT, hwB, hwD⟩)).1
    obtain ⟨f, _, _, hfC, hfT, hfB, hfD, hweight⟩ :=
      familyA2_weighted_graph_iso G weight C T B D u v hcard hC hT hB hD
        hTB hTD hBD huv hu hv he hother
    exact Or.inr (Or.inl ⟨f, hfC, hfT, hfB, hfD, hweight⟩)
  · have hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
      intro v hvB hvD hvT
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      by_cases hvM : v = M
      · simpa only [hvM] using hM
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvM, hvT, hvB, hvD⟩)).1
    obtain ⟨f, _, hfC, hfT, hfB, hfD, hweight⟩ :=
      familyB_weighted_graph_iso G weight C M T B D hcard hC hM hT hB hD
        hTB hTD hBD hCM he hother
    exact Or.inr (Or.inr ⟨f, hfC, hfT, hfB, hfD, hweight⟩)

end ABModels

end KltDP.LinearAlgebra
