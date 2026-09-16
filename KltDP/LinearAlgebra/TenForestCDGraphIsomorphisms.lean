import KltDP.LinearAlgebra.TenForestGraphIsomorphisms

/-!
# Marked weighted graph isomorphisms for families C and D

The models contain every vertex, including the optional canonical edge
in D2. Actual weights and the classified adjacencies prove that the named
core vertices are distinct. The existing labeled-core construction then
gives bijective, weight-preserving graph isomorphisms.
-/

noncomputable section

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- Two distinct canonical labels can be prepended to an injective family
of heavier vertices: their distinctness follows from actual weights. -/
theorem canonical_pair_cons_injective {V : Type*} {n : ℕ} (weight : V → ℕ)
    (C M : V) (heavy : Fin n → V) (hheavy : Function.Injective heavy)
    (hC : weight C = 2) (hM : weight M = 2) (hCM : C ≠ M)
    (hh : ∀ i, 3 ≤ weight (heavy i)) :
    Function.Injective (Fin.cons C (Fin.cons M heavy)) := by
  have hCout : C ∉ Set.range heavy := by
    rintro ⟨i, hi⟩
    have hw := hh i
    rw [hi, hC] at hw
    omega
  have hMout : M ∉ Set.range heavy := by
    rintro ⟨i, hi⟩
    have hw := hh i
    rw [hi, hM] at hw
    omega
  exact Fin.cons_injective_of_injective
    (by simpa only [Fin.range_cons, Set.mem_insert_iff, not_or] using And.intro hCM hCout)
    (Fin.cons_injective_of_injective hMout hheavy)

/-- The actual six-label core used for both D and E. The distinguished
weight of B2 may be any value at least three. -/
theorem six_source_labels_injective {V : Type*} (weight : V → ℕ)
    (C M B D T U : V) (hC : weight C = 2) (hM : weight M = 2)
    (hB : 3 ≤ weight B) (hD : 3 ≤ weight D)
    (hT : 3 ≤ weight T) (hU : 3 ≤ weight U) (hCM : C ≠ M)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U) :
    Function.Injective (![C, M, B, D, T, U] : Fin 6 → V) := by
  apply canonical_pair_cons_injective weight C M (![B, D, T, U] : Fin 4 → V)
  · simp [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Matrix.range_empty,
      Function.injective_of_subsingleton, hBD, Ne.symm hTB, Ne.symm hUB,
      Ne.symm hTD, Ne.symm hUD, hTU]
  · exact hC
  · exact hM
  · exact hCM
  · intro i
    fin_cases i <;> simp [hB, hD, hT, hU]

/-- Family C: the core is `[C,L,B,D,T,M]`, and the edges are `B-L`
and `D-M`. The complement consists of four isolated canonical vertices. -/
def familyCCoreEdges : Finset (Sym2 (Fin 6)) := {s(2, 1), s(3, 5)}

def familyCCoreWeight : Fin 6 → ℕ := ![2, 2, 3, 3, 3, 2]

def familyCGraph : SimpleGraph (Fin 6 ⊕ Fin 4) :=
  SimpleGraph.fromEdgeSet (familyCCoreEdges : Set (Sym2 (Fin 6))) ⊕g ⊥

def familyCGraphWeight : Fin 6 ⊕ Fin 4 → ℕ :=
  Sum.elim familyCCoreWeight (fun _ => 2)

/-- Family D1: the core is `[C,M,B1,B2,T,U]`, with the edge `C-M`
and four isolated canonical vertices outside it. -/
def familyD1CoreEdges : Finset (Sym2 (Fin 6)) := {s(0, 1)}

def familyD1CoreWeight : Fin 6 → ℕ := ![2, 2, 3, 3, 3, 3]

def familyD1Graph : SimpleGraph (Fin 6 ⊕ Fin 4) :=
  SimpleGraph.fromEdgeSet (familyD1CoreEdges : Set (Sym2 (Fin 6))) ⊕g ⊥

def familyD1GraphWeight : Fin 6 ⊕ Fin 4 → ℕ :=
  Sum.elim familyD1CoreWeight (fun _ => 2)

/-- D2 explicitly includes the actual additional canonical edge `x-y`.
The core labels are `[x,y,C,M,B1,B2,T,U]`. -/
def familyD2CoreEdges : Finset (Sym2 (Fin 8)) := {s(2, 3), s(0, 1)}

def familyD2CoreWeight : Fin 8 → ℕ := ![2, 2, 2, 2, 3, 3, 3, 3]

def familyD2Graph : SimpleGraph (Fin 8 ⊕ Fin 2) :=
  SimpleGraph.fromEdgeSet (familyD2CoreEdges : Set (Sym2 (Fin 8))) ⊕g ⊥

def familyD2GraphWeight : Fin 8 ⊕ Fin 2 → ℕ :=
  Sum.elim familyD2CoreWeight (fun _ => 2)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Family C's actual closed edges and isolated marked C give its complete
marked weighted model. Neighbor data prove that the two canonical leaves
are distinct; no extra vertex-distinctness premise is added. -/
theorem familyC_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C L B D T M : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hL : weight L = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hCiso : ∀ v, ¬ G.Adj C v) (hBL : G.Adj B L) (hDM : G.Adj D M)
    (hnL : G.neighborFinset L = {B})
    (hedges : G.edgeFinset = {s(B, L), s(D, M)})
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2) :
    ∃ f : familyCGraph ≃g G,
      (∀ i, f (Sum.inl i) = (![C, L, B, D, T, M] : Fin 6 → V) i) ∧
      ∀ v, weight (f v) = familyCGraphWeight v := by
  have hCL : C ≠ L := by intro h; subst L; exact hCiso B hBL.symm
  have hCM : C ≠ M := by intro h; subst M; exact hCiso D hDM.symm
  have hLM : L ≠ M := by
    intro h
    subst M
    have hm := (G.mem_neighborFinset L D).mpr hDM.symm
    rw [hnL, Finset.mem_singleton] at hm
    exact hBD hm.symm
  have hCB : C ≠ B := by intro h; have := congrArg weight h; omega
  have hCD : C ≠ D := by intro h; have := congrArg weight h; omega
  have hCT : C ≠ T := by intro h; have := congrArg weight h; omega
  have hLB : L ≠ B := by intro h; have := congrArg weight h; omega
  have hLD : L ≠ D := by intro h; have := congrArg weight h; omega
  have hLT : L ≠ T := by intro h; have := congrArg weight h; omega
  have hMB : M ≠ B := by intro h; have := congrArg weight h; omega
  have hMD : M ≠ D := by intro h; have := congrArg weight h; omega
  have hMT : M ≠ T := by intro h; have := congrArg weight h; omega
  have hinj : Function.Injective (![C, L, B, D, T, M] : Fin 6 → V) := by
    simp [Matrix.vecCons, Fin.cons_injective_iff, Fin.range_cons, Matrix.range_empty,
      Function.injective_of_subsingleton, hCL, hCM, hLM, hCB, hCD, hCT,
      hLB, hLD, hLT, hBD, Ne.symm hTB, Ne.symm hTD,
      Ne.symm hMB, Ne.symm hMD, Ne.symm hMT]
  let e : Fin 6 ↪ V := ⟨![C, L, B, D, T, M], hinj⟩
  have hcount : Fintype.card {v // v ∉ Set.range e} = 4 := by
    rw [card_labeled_complement, hcard]
    norm_num
  have he : G.edgeFinset = familyCCoreEdges.image (Sym2.map e) := by
    simpa only [familyCCoreEdges, Finset.image_insert, Finset.image_singleton,
      Sym2.map_pair_eq] using hedges
  have hw : ∀ i, weight (e i) = familyCCoreWeight i := by
    intro i
    fin_cases i <;> simp [e, familyCCoreWeight, hC, hL, hM, hB, hD, hT]
  have ho : ∀ v, v ∉ Set.range e → weight v = 2 := by
    intro v hv
    apply hother v
    · intro h; exact hv ⟨2, h.symm⟩
    · intro h; exact hv ⟨3, h.symm⟩
    · intro h; exact hv ⟨4, h.symm⟩
  exact exists_weighted_iso_of_edgeFinset_image G weight e familyCCoreEdges
    familyCCoreWeight 4 hcount he hw ho

/-- All vertices of the actual D1 row are included by the resulting
weight-preserving graph isomorphism. -/
theorem familyD1_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M B D T U : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hedges : G.edgeFinset = {s(C, M)})
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2) :
    ∃ f : familyD1Graph ≃g G,
      (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
      ∀ v, weight (f v) = familyD1GraphWeight v := by
  let e : Fin 6 ↪ V := ⟨![C, M, B, D, T, U], six_source_labels_injective
    weight C M B D T U hC hM (by omega) (by omega) (by omega) (by omega)
    hCM.ne hBD hTB hTD hUB hUD hTU⟩
  have hcount : Fintype.card {v // v ∉ Set.range e} = 4 := by
    rw [card_labeled_complement, hcard]
    norm_num
  have he : G.edgeFinset = familyD1CoreEdges.image (Sym2.map e) := by
    simpa only [familyD1CoreEdges, Finset.image_singleton, Sym2.map_pair_eq] using hedges
  have hw : ∀ i, weight (e i) = familyD1CoreWeight i := by
    intro i
    fin_cases i <;> simp [e, familyD1CoreWeight, hC, hM, hB, hD, hT, hU]
  have ho : ∀ v, v ∉ Set.range e → weight v = 2 := by
    intro v hv
    apply hother v
    · intro h; exact hv ⟨2, h.symm⟩
    · intro h; exact hv ⟨3, h.symm⟩
    · intro h; exact hv ⟨4, h.symm⟩
    · intro h; exact hv ⟨5, h.symm⟩
  exact exists_weighted_iso_of_edgeFinset_image G weight e familyD1CoreEdges
    familyD1CoreWeight 4 hcount he hw ho

/-- D2 retains the actual endpoints of its additional canonical edge and
the two actual remaining isolated vertices. -/
theorem familyD2_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (C M B D T U x y : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M) (hxy : G.Adj x y)
    (hx : x ∉ ({C, M, B, D, T, U} : Finset V))
    (hy : y ∉ ({C, M, B, D, T, U} : Finset V))
    (hedges : G.edgeFinset = {s(C, M), s(x, y)})
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2) :
    ∃ f : familyD2Graph ≃g G,
      (∀ i, f (Sum.inl i) = (![x, y, C, M, B, D, T, U] : Fin 8 → V) i) ∧
      ∀ v, weight (f v) = familyD2GraphWeight v := by
  have hx' : x ≠ C ∧ x ≠ M ∧ x ≠ B ∧ x ≠ D ∧ x ≠ T ∧ x ≠ U := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
  have hy' : y ≠ C ∧ y ≠ M ∧ y ≠ B ∧ y ≠ D ∧ y ≠ T ∧ y ≠ U := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hy
  have hx2 := hother x hx'.2.2.1 hx'.2.2.2.1 hx'.2.2.2.2.1 hx'.2.2.2.2.2
  have hy2 := hother y hy'.2.2.1 hy'.2.2.2.1 hy'.2.2.2.2.1 hy'.2.2.2.2.2
  have hbase := six_source_labels_injective weight C M B D T U hC hM
    (by omega) (by omega) (by omega) (by omega) hCM.ne hBD hTB hTD hUB hUD hTU
  have hinj : Function.Injective (![x, y, C, M, B, D, T, U] : Fin 8 → V) := by
    apply Fin.cons_injective_of_injective
    · simp [Matrix.vecCons, Fin.range_cons, Matrix.range_empty, hxy.ne,
        hx'.1, hx'.2.1, hx'.2.2.1, hx'.2.2.2.1, hx'.2.2.2.2.1, hx'.2.2.2.2.2]
    · apply Fin.cons_injective_of_injective
      · simp [Matrix.vecCons, Fin.range_cons, Matrix.range_empty,
          hy'.1, hy'.2.1, hy'.2.2.1, hy'.2.2.2.1, hy'.2.2.2.2.1, hy'.2.2.2.2.2]
      · exact hbase
  let e : Fin 8 ↪ V := ⟨![x, y, C, M, B, D, T, U], hinj⟩
  have hcount : Fintype.card {v // v ∉ Set.range e} = 2 := by
    rw [card_labeled_complement, hcard]
    norm_num
  have he : G.edgeFinset = familyD2CoreEdges.image (Sym2.map e) := by
    simpa only [familyD2CoreEdges, Finset.image_insert, Finset.image_singleton,
      Sym2.map_pair_eq] using hedges
  have hw : ∀ i, weight (e i) = familyD2CoreWeight i := by
    intro i
    fin_cases i <;> simp [e, familyD2CoreWeight, hx2, hy2, hC, hM, hB, hD, hT, hU]
  have ho : ∀ v, v ∉ Set.range e → weight v = 2 := by
    intro v hv
    apply hother v
    · intro h; exact hv ⟨4, h.symm⟩
    · intro h; exact hv ⟨5, h.symm⟩
    · intro h; exact hv ⟨6, h.symm⟩
    · intro h; exact hv ⟨7, h.symm⟩
  exact exists_weighted_iso_of_edgeFinset_image G weight e familyD2CoreEdges
    familyD2CoreWeight 2 hcount he hw ho

/-- The actual C classifier output supplies the two leaves and every
canonical complement weight required by the marked graph isomorphism. -/
theorem CForestRow_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D T : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hBD : B ≠ D)
    (hrows : CForestRow G (fun v => (weight v : ℚ)) coeff C B D T) :
    ∃ L M, ∃ f : familyCGraph ≃g G,
      (∀ i, f (Sum.inl i) = (![C, L, B, D, T, M] : Fin 6 → V) i) ∧
      ∀ v, weight (f v) = familyCGraphWeight v := by
  obtain ⟨L, M, hL, hM, hCiso, _, hBL, hDM, _, hnL, _, _, he, _, hr, _⟩ := hrows
  have hLnat : weight L = 2 := by
    change (weight L : ℚ) = 2 at hL
    exact_mod_cast hL
  have hMnat : weight M = 2 := by
    change (weight M : ℚ) = 2 at hM
    exact_mod_cast hM
  have hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
    intro v hvB hvD hvT
    by_cases hvC : v = C
    · simpa only [hvC] using hC
    by_cases hvL : v = L
    · simpa only [hvL] using hLnat
    by_cases hvM : v = M
    · simpa only [hvM] using hMnat
    · have hh := (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvB, hvL, hvD, hvM, hvT⟩)).1
      change (weight v : ℚ) = 2 at hh
      exact_mod_cast hh
  exact ⟨L, M, familyC_weighted_graph_iso G weight C L B D T M hcard
    hC hLnat hMnat hB hD hT hTB hTD hBD hCiso hBL hDM hnL he hother⟩

/-- Both actual D classifier completions give the corresponding full
marked weighted isomorphisms, including the optional outside edge. -/
theorem DForestRows_weighted_graph_iso (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : V → ℕ) (coeff : V → ℚ) (C B D T U : V) (hcard : Fintype.card V = 10)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hrows : DForestRows G weight coeff C B D T U) :
    ∃ M,
      (∃ f : familyD1Graph ≃g G,
        (∀ i, f (Sum.inl i) = (![C, M, B, D, T, U] : Fin 6 → V) i) ∧
        ∀ v, weight (f v) = familyD1GraphWeight v) ∨
      (∃ x y, ∃ f : familyD2Graph ≃g G,
        (∀ i, f (Sum.inl i) = (![x, y, C, M, B, D, T, U] : Fin 8 → V) i) ∧
        ∀ v, weight (f v) = familyD2GraphWeight v) := by
  obtain ⟨M, hCM, hC, hM, _, _, _, _, _, _, _, _, _, _, hcases⟩ := hrows
  refine ⟨M, ?_⟩
  rcases hcases with ⟨he, _, hr, _⟩ | ⟨x, y, hxy, hx, hy, hx2, hy2, he, _, hr, _⟩
  · have hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2 := by
      intro v hvB hvD hvT hvU
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      by_cases hvM : v = M
      · simpa only [hvM] using hM
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvC, hvM, hvB, hvD, hvT, hvU⟩)).1
    exact Or.inl (familyD1_weighted_graph_iso G weight C M B D T U hcard
      hC hM hB hD hT hU hBD hTB hTD hUB hUD hTU hCM he hother)
  · have hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2 := by
      intro v hvB hvD hvT hvU
      by_cases hvx : v = x
      · simpa only [hvx] using hx2
      by_cases hvy : v = y
      · simpa only [hvy] using hy2
      by_cases hvC : v = C
      · simpa only [hvC] using hC
      by_cases hvM : v = M
      · simpa only [hvM] using hM
      · exact (hr v (by
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hvx, hvy, hvC, hvM, hvB, hvD, hvT, hvU⟩)).1
    exact Or.inr ⟨x, y, familyD2_weighted_graph_iso G weight C M B D T U x y hcard
      hC hM hB hD hT hU hBD hTB hTD hUB hUD hTU hCM hxy hx hy he hother⟩

end KltDP.LinearAlgebra
