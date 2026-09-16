import KltDP.LinearAlgebra.TenForestCDGraphIsomorphisms

/-!
# Marked weighted graph isomorphisms for the four E completions

The fixed six-vertex component data are assembled with the actual induced
five-vertex complement. Its four graph shapes are those already derived
by the candidate classifier. The assembly constructs a full bijection;
it preserves the named fixed vertices and all weights.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

section Assembly

variable {V I W : Type*} [DecidableEq V]

/-- Assemble an actual core and any isomorphic actual complementary graph.
The complement need not be discrete. -/
def labeledGraphComplementIso (G : SimpleGraph V) (H : SimpleGraph I)
    (K : SimpleGraph W) (e : I ↪ V)
    (rest : K ≃g G.induce {v | v ∉ Set.range e})
    (hcore : ∀ i j, G.Adj (e i) (e j) ↔ H.Adj i j)
    (hcross : ∀ i v, v ∉ Set.range e → ¬ G.Adj (e i) v) : (H ⊕g K) ≃g G := by
  classical
  let E : I ⊕ W ≃ V :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) rest.toEquiv).trans
      (Equiv.Set.sumCompl (Set.range e))
  refine ⟨E, ?_⟩
  rintro (i | i) (j | j)
  · change G.Adj (e i) (e j) ↔ H.Adj i j
    exact hcore i j
  · simpa [E, SimpleGraph.sum] using
      (iff_false_intro (hcross i (rest j).val (rest j).property))
  · simpa [E, SimpleGraph.sum] using
      (iff_false_intro (fun h => hcross j (rest i).val (rest i).property h.symm))
  · change G.Adj (rest i).val (rest j).val ↔ K.Adj i j
    exact rest.map_rel_iff

theorem labeledGraphComplementIso_inl (G : SimpleGraph V) (H : SimpleGraph I)
    (K : SimpleGraph W) (e : I ↪ V)
    (rest : K ≃g G.induce {v | v ∉ Set.range e})
    (hcore : ∀ i j, G.Adj (e i) (e j) ↔ H.Adj i j)
    (hcross : ∀ i v, v ∉ Set.range e → ¬ G.Adj (e i) v) (i : I) :
    labeledGraphComplementIso G H K e rest hcore hcross (Sum.inl i) = e i := rfl

theorem labeledGraphComplementIso_inr (G : SimpleGraph V) (H : SimpleGraph I)
    (K : SimpleGraph W) (e : I ↪ V)
    (rest : K ≃g G.induce {v | v ∉ Set.range e})
    (hcore : ∀ i j, G.Adj (e i) (e j) ↔ H.Adj i j)
    (hcross : ∀ i v, v ∉ Set.range e → ¬ G.Adj (e i) v) (i : W) :
    labeledGraphComplementIso G H K e rest hcore hcross (Sum.inr i) = (rest i).val := rfl

/-- Change only the predicate describing the same actual complementary
vertices. The graph map is the identity on their underlying values. -/
def complementPredicateIso (G : SimpleGraph V) (p q : V → Prop)
    (hpq : ∀ v, p v ↔ q v) : G.induce {v | p v} ≃g G.induce {v | q v} where
  toEquiv :=
    { toFun := fun v => ⟨v.val, (hpq v.val).mp v.property⟩
      invFun := fun v => ⟨v.val, (hpq v.val).mpr v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

end Assembly

/-- Fixed E core labels `[C,M,B1,B2,T,U]`, with the single edge M-B1. -/
def familyECoreGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet ({s(1, 2)} : Finset (Sym2 (Fin 6)))

def familyECoreWeight : Fin 6 → ℕ := ![2, 2, 3, 4, 3, 3]

theorem familyECoreGraph_adj (i j : Fin 6) :
    familyECoreGraph.Adj i j ↔ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  change (s(i, j) ∈ ({s(1, 2)} : Finset (Sym2 (Fin 6))) ∧ i ≠ j) ↔ _
  rw [Finset.mem_singleton, Sym2.eq_iff]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

def familyE1RemainingEdges : Finset (Sym2 (Fin 0)) := ∅
def familyE2RemainingEdges : Finset (Sym2 (Fin 2)) := {s(0, 1)}
def familyE3RemainingEdges : Finset (Sym2 (Fin 3)) := {s(0, 1), s(1, 2)}
def familyE4RemainingEdges : Finset (Sym2 (Fin 4)) := {s(0, 1), s(2, 3)}

def familyE1RemainingGraph : SimpleGraph (Fin 0 ⊕ Fin 5) :=
  SimpleGraph.fromEdgeSet (familyE1RemainingEdges : Set (Sym2 (Fin 0))) ⊕g ⊥
def familyE2RemainingGraph : SimpleGraph (Fin 2 ⊕ Fin 3) :=
  SimpleGraph.fromEdgeSet (familyE2RemainingEdges : Set (Sym2 (Fin 2))) ⊕g ⊥
def familyE3RemainingGraph : SimpleGraph (Fin 3 ⊕ Fin 2) :=
  SimpleGraph.fromEdgeSet (familyE3RemainingEdges : Set (Sym2 (Fin 3))) ⊕g ⊥
def familyE4RemainingGraph : SimpleGraph (Fin 4 ⊕ Fin 1) :=
  SimpleGraph.fromEdgeSet (familyE4RemainingEdges : Set (Sym2 (Fin 4))) ⊕g ⊥

def familyE1Graph : SimpleGraph (Fin 6 ⊕ (Fin 0 ⊕ Fin 5)) :=
  familyECoreGraph ⊕g familyE1RemainingGraph
def familyE2Graph : SimpleGraph (Fin 6 ⊕ (Fin 2 ⊕ Fin 3)) :=
  familyECoreGraph ⊕g familyE2RemainingGraph
def familyE3Graph : SimpleGraph (Fin 6 ⊕ (Fin 3 ⊕ Fin 2)) :=
  familyECoreGraph ⊕g familyE3RemainingGraph
def familyE4Graph : SimpleGraph (Fin 6 ⊕ (Fin 4 ⊕ Fin 1)) :=
  familyECoreGraph ⊕g familyE4RemainingGraph

/-- The complementary vertices are all canonical, independently of which
of the four actual remaining graphs occurs. -/
def familyEGraphWeight {W : Type*} : Fin 6 ⊕ W → ℕ :=
  Sum.elim familyECoreWeight (fun _ => 2)

section Remaining

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem familyE1_remaining_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 5) (he : G.edgeFinset = ∅) :
    Nonempty (familyE1RemainingGraph ≃g G) := by
  let e : Fin 0 ↪ V := ⟨Fin.elim0, Function.injective_of_subsingleton _⟩
  have hc : Fintype.card {v // v ∉ Set.range e} = 5 := by
    rw [card_labeled_complement, hcard]
    norm_num
  obtain ⟨f, _, _⟩ := exists_weighted_iso_of_edgeFinset_image G (fun _ => 2) e
    familyE1RemainingEdges (fun _ => 2) 5 hc
    (by simpa only [familyE1RemainingEdges, Finset.image_empty] using he)
    (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨f⟩

theorem familyE2_remaining_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 5) (x y : V) (hxy : x ≠ y)
    (he : G.edgeFinset = {s(x, y)}) : Nonempty (familyE2RemainingGraph ≃g G) := by
  have hi : Function.Injective (![x, y] : Fin 2 → V) := by
    simp [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Matrix.range_empty,
      Function.injective_of_subsingleton, hxy]
  let e : Fin 2 ↪ V := ⟨![x, y], hi⟩
  have hc : Fintype.card {v // v ∉ Set.range e} = 3 := by
    rw [card_labeled_complement, hcard]
    norm_num
  obtain ⟨f, _, _⟩ := exists_weighted_iso_of_edgeFinset_image G (fun _ => 2) e
    familyE2RemainingEdges (fun _ => 2) 3 hc
    (by simpa only [familyE2RemainingEdges, Finset.image_singleton, Sym2.map_pair_eq] using he)
    (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨f⟩

theorem familyE3_remaining_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 5) (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (he : G.edgeFinset = {s(x, y), s(y, z)}) :
    Nonempty (familyE3RemainingGraph ≃g G) := by
  have hi : Function.Injective (![x, y, z] : Fin 3 → V) := by
    simp [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Matrix.range_empty,
      Function.injective_of_subsingleton, hxy, hxz, hyz]
  let e : Fin 3 ↪ V := ⟨![x, y, z], hi⟩
  have hc : Fintype.card {v // v ∉ Set.range e} = 2 := by
    rw [card_labeled_complement, hcard]
    norm_num
  obtain ⟨f, _, _⟩ := exists_weighted_iso_of_edgeFinset_image G (fun _ => 2) e
    familyE3RemainingEdges (fun _ => 2) 2 hc
    (by simpa only [familyE3RemainingEdges, Finset.image_insert, Finset.image_singleton,
      Sym2.map_pair_eq] using he) (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨f⟩

theorem familyE4_remaining_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 5) (x y z w : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (he : G.edgeFinset = {s(x, y), s(z, w)}) :
    Nonempty (familyE4RemainingGraph ≃g G) := by
  have hi : Function.Injective (![x, y, z, w] : Fin 4 → V) := by
    simp [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Matrix.range_empty,
      Function.injective_of_subsingleton, hxy, hxz, hxw, hyz, hyw, hzw]
  let e : Fin 4 ↪ V := ⟨![x, y, z, w], hi⟩
  have hc : Fintype.card {v // v ∉ Set.range e} = 1 := by
    rw [card_labeled_complement, hcard]
    norm_num
  obtain ⟨f, _, _⟩ := exists_weighted_iso_of_edgeFinset_image G (fun _ => 2) e
    familyE4RemainingEdges (fun _ => 2) 1 hc
    (by simpa only [familyE4RemainingEdges, Finset.image_insert, Finset.image_singleton,
      Sym2.map_pair_eq] using he) (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨f⟩

end Remaining

section FixedCore

variable {V W : Type*} [Fintype V] [DecidableEq V]

/-- Assemble the actual fixed E core with any model of its actual induced
complement. Closed-edge and isolation data prove every cross-adjacency
vanishes, and the resulting isomorphism preserves all fixed labels. -/
theorem familyE_fixed_core_weighted_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M B D T U : V)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hUB : U ≠ B) (hTU : T ≠ U)
    (hBM : G.Adj B M) (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hCiso : ∀ v, ¬ G.Adj C v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (H : SimpleGraph W)
    (rest : H ≃g G.induce {v | v ∉ ({C, B, M, D, T, U} : Finset V)})
    (hrestWeight : ∀ v : {v | v ∉ ({C, B, M, D, T, U} : Finset V)}, weight v.val = 2) :
    ∃ f : (familyECoreGraph ⊕g H) ≃g G,
      (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
      ∀ v, weight (f v) = familyEGraphWeight v := by
  classical
  have hCM : C ≠ M := by intro h; subst M; exact hCiso B hBM.symm
  have hBD : B ≠ D := by intro h; have := congrArg weight h; omega
  have hTD : T ≠ D := by intro h; have := congrArg weight h; omega
  have hUD : U ≠ D := by intro h; have := congrArg weight h; omega
  let e : Fin 6 ↪ V := ⟨![C, M, B, D, T, U], six_source_labels_injective
    weight C M B D T U hC hM (by omega) (by omega) (by omega) (by omega)
    hCM hBD hTB hTD hUB hUD hTU⟩
  have hfixed (v : V) : v ∈ Set.range e ↔ v ∈ ({C, B, M, D, T, U} : Finset V) := by
    simp [e, Matrix.vecCons, Fin.range_cons, Matrix.range_empty,
      or_assoc, or_comm, or_left_comm]
  have hBrow (v : V) : G.Adj B v ↔ v = M := by
    rw [← G.mem_neighborFinset, hnB, Finset.mem_singleton]
  have hMrow (v : V) : G.Adj M v ↔ v = B := by
    rw [← G.mem_neighborFinset, hnM, Finset.mem_singleton]
  have hrows (i : Fin 6) (v : V) : G.Adj (e i) v ↔
      (i = 1 ∧ v = B) ∨ (i = 2 ∧ v = M) := by
    fin_cases i <;> simp [e, hCiso v, hDiso v, hTiso v, hUiso v, hBrow v, hMrow v]
  have hcore (i j : Fin 6) : G.Adj (e i) (e j) ↔ familyECoreGraph.Adj i j := by
    rw [hrows, familyECoreGraph_adj]
    change ((i = 1 ∧ e j = e 2) ∨ (i = 2 ∧ e j = e 1)) ↔ _
    simp only [e.injective.eq_iff]
  have hcross (i : Fin 6) (v : V) (hv : v ∉ Set.range e) : ¬ G.Adj (e i) v := by
    intro h
    rcases (hrows i v).mp h with ⟨_, h⟩ | ⟨_, h⟩
    · exact hv ⟨2, h.symm⟩
    · exact hv ⟨1, h.symm⟩
  let changePredicate := complementPredicateIso G
    (fun v => v ∉ ({C, B, M, D, T, U} : Finset V))
    (fun v => v ∉ Set.range e) (fun v => not_congr (hfixed v).symm)
  let rest' := changePredicate.comp rest
  let f := labeledGraphComplementIso G familyECoreGraph H e rest' hcore hcross
  refine ⟨f, fun i => rfl, ?_⟩
  rintro (i | i)
  · change weight (e i) = familyECoreWeight i
    fin_cases i <;> simp [e, familyECoreWeight, hC, hM, hB, hD, hT, hU]
  · calc
      weight (f (Sum.inr i)) = weight (rest' i).val :=
        congrArg weight
          (labeledGraphComplementIso_inr G familyECoreGraph H e rest' hcore hcross i)
      _ = weight (rest i).val := rfl
      _ = 2 := hrestWeight (rest i)

end FixedCore

section SourceRow

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete E classifier output gives the four actual marked weighted
graph isomorphisms. The five-vertex shapes, their endpoints, canonical
weights, and the closed fixed core are all extracted from that output. -/
theorem EForestRows_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D T U : V)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = 4)
    (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hUB : U ≠ B) (hTU : T ≠ U)
    (hrows : EForestRows G (fun v => (weight v : ℚ)) coeff C B D T U) :
    ∃ M,
      (∃ f : familyE1Graph ≃g G,
        (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
        ∀ v, weight (f v) = familyEGraphWeight v) ∨
      (∃ f : familyE2Graph ≃g G,
        (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
        ∀ v, weight (f v) = familyEGraphWeight v) ∨
      (∃ f : familyE3Graph ≃g G,
        (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
        ∀ v, weight (f v) = familyEGraphWeight v) ∨
      (∃ f : familyE4Graph ≃g G,
        (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
        ∀ v, weight (f v) = familyEGraphWeight v) := by
  classical
  obtain ⟨M, hM, hBM, hnB, hnM, _, hCiso, hDiso, hTiso, hUiso, _, _, _, hr⟩ := hrows
  let fixed : Finset V := {C, B, M, D, T, U}
  let Z := G.induce {v | v ∉ fixed}
  obtain ⟨_, hZcard, hZweight, _, hshape⟩ := hr
  have hMnat : weight M = 2 := by
    change (weight M : ℚ) = 2 at hM
    exact_mod_cast hM
  have hZnat : ∀ v : {v | v ∉ fixed}, weight v.val = 2 := by
    intro v
    have h := hZweight v
    change (weight v.val : ℚ) = 2 at h
    exact_mod_cast h
  have assemble {W : Type} (H : SimpleGraph W) (rest : H ≃g Z) :
      ∃ f : (familyECoreGraph ⊕g H) ≃g G,
        (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
        ∀ v, weight (f v) = familyEGraphWeight v :=
    familyE_fixed_core_weighted_iso G weight C M B D T U hC hMnat hB hD hT hU
      hTB hUB hTU hBM hnB hnM hCiso hDiso hTiso hUiso H rest hZnat
  refine ⟨M, ?_⟩
  rcases hshape with ⟨he, _, _⟩ | ⟨x, y, hxy, he, _, _, _⟩ |
    ⟨x, y, z, hxy, hxz, hyz, he, _, _, _⟩ |
    ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he, _, _, _⟩
  · obtain ⟨rest⟩ := familyE1_remaining_iso Z hZcard he
    exact Or.inl (assemble familyE1RemainingGraph rest)
  · obtain ⟨rest⟩ := familyE2_remaining_iso Z hZcard x y hxy he
    exact Or.inr (Or.inl (assemble familyE2RemainingGraph rest))
  · obtain ⟨rest⟩ := familyE3_remaining_iso Z hZcard x y z hxy hxz hyz he
    exact Or.inr (Or.inr (Or.inl (assemble familyE3RemainingGraph rest)))
  · obtain ⟨rest⟩ := familyE4_remaining_iso Z hZcard x y z w hxy hxz hxw hyz hyw hzw he
    exact Or.inr (Or.inr (Or.inr (assemble familyE4RemainingGraph rest)))

end SourceRow

end KltDP.LinearAlgebra
