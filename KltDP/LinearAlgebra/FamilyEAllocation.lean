import KltDP.LinearAlgebra.FamilyEClassification
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The four actual remaining forests in family E

Deleting the proved closed core edge leaves all six fixed vertices isolated.
Restricting to their actual complement therefore removes no further edges.
The ambient eleven-vertex and three-edge bounds give five remaining vertices
and at most two remaining edges. A graph with that edge allowance is empty,
one edge, a two-edge path, or two disjoint edges. These cases are derived
from its actual edge finset.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Two distinct undirected edges either form a three-vertex path or are
disjoint. This splits their actual endpoint equalities, not graph fixtures. -/
theorem distinct_edge_pair_cases (a b c d : V)
    (hab : a ≠ b) (hcd : c ≠ d) (hedge : s(a, b) ≠ s(c, d)) :
    (∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      ({s(a, b), s(c, d)} : Finset (Sym2 V)) = {s(x, y), s(y, z)}) ∨
    (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) := by
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by intro h; subst d; exact hedge rfl
    exact Or.inl ⟨b, a, d, hab.symm, hbd, hcd,
      by simp only [Sym2.eq_swap]⟩
  by_cases had : a = d
  · subst d
    have hbc : b ≠ c := by
      intro h
      subst c
      exact hedge Sym2.eq_swap
    exact Or.inl ⟨b, a, c, hab.symm, hbc, hcd.symm,
      by simp only [Sym2.eq_swap]⟩
  by_cases hbc : b = c
  · subst c
    have had' : a ≠ d := by intro h; subst d; exact hedge Sym2.eq_swap
    exact Or.inl ⟨a, b, d, hab, had', hcd, rfl⟩
  by_cases hbd : b = d
  · subst d
    exact Or.inl ⟨a, b, c, hab, hac, hcd.symm,
      by simp only [Sym2.eq_swap]⟩
  exact Or.inr ⟨hac, had, hbc, hbd⟩

/-- The four possibilities for the actual edge set of any finite simple
graph with at most two edges. No acyclicity assumption is needed. -/
theorem graph_at_most_two_edge_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedges : G.edgeFinset.card ≤ 2) :
    G.edgeFinset = ∅ ∨
    (∃ x y, x ≠ y ∧ G.edgeFinset = {s(x, y)}) ∨
    (∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ G.edgeFinset = {s(x, y), s(y, z)}) ∨
    (∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
      G.edgeFinset = {s(x, y), s(z, w)}) := by
  rcases G.edgeFinset.eq_empty_or_nonempty with hempty | ⟨edge, hmem⟩
  · exact Or.inl hempty
  rcases eq_singleton_or_pair_of_mem_card_le_two G.edgeFinset edge hmem hedges with
    hsingle | ⟨other, hne, hpair⟩
  · obtain ⟨x, y, hxy⟩ := Sym2.exists.mp
      (show ∃ e : Sym2 V, G.edgeFinset = {e} from ⟨edge, hsingle⟩)
    have hadj : G.Adj x y := by
      have hm : s(x, y) ∈ G.edgeFinset := by rw [hxy]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hm
    exact Or.inr (Or.inl ⟨x, y, hadj.ne, hxy⟩)
  · obtain ⟨a, b, hpair'⟩ := Sym2.exists.mp
      (show ∃ e f : Sym2 V, f ≠ e ∧ G.edgeFinset = {e, f} from ⟨edge, other, hne, hpair⟩)
    obtain ⟨c, d, hne, hpair⟩ := Sym2.exists.mp hpair' 
    have hab : G.Adj a b := by
      have hm : s(a, b) ∈ G.edgeFinset := by rw [hpair]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hm
    have hcd : G.Adj c d := by
      have hm : s(c, d) ∈ G.edgeFinset := by rw [hpair]; simp
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hm
    rcases distinct_edge_pair_cases a b c d hab.ne hcd.ne hne.symm with
      ⟨x, y, z, hxy, hxz, hyz, he⟩ | ⟨hac, had, hbc, hbd⟩
    · exact Or.inr (Or.inr (Or.inl ⟨x, y, z, hxy, hxz, hyz, hpair.trans he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, b, c, d, hab.ne, hac, had, hbc, hbd,
        hcd.ne, hpair⟩))

/-- Deleting a closed edge and all fixed isolated vertices removes exactly
one edge. The remaining graph is induced on the actual complement. -/
theorem closed_edge_complement_edge_count
    (G : SimpleGraph V) [DecidableRel G.Adj] (fixed : Finset V) (B M : V)
    (hBM : G.Adj B M) (hB : B ∈ fixed) (hM : M ∈ fixed)
    (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hfixed : ∀ v ∈ fixed, v ≠ B → v ≠ M → ∀ w, ¬ G.Adj v w) :
    (G.induce {v | v ∉ fixed}).edgeFinset.card = G.edgeFinset.card - 1 := by
  classical
  let H := G.deleteEdges ({s(B, M)} : Finset (Sym2 V))
  have hmem : s(B, M) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hBM
  have hHcount : H.edgeFinset.card = G.edgeFinset.card - 1 := by
    change (G.deleteEdges ({s(B, M)} : Finset (Sym2 V))).edgeFinset.card = _
    rw [SimpleGraph.edgeFinset_deleteEdges, Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hmem]
  have hHfixed : ∀ v ∈ fixed, ∀ w, ¬ H.Adj v w := by
    intro v hv w hadj
    have ha : G.Adj v w ∧ s(v, w) ≠ s(B, M) := by
      simpa only [H, SimpleGraph.deleteEdges_adj, Finset.mem_coe,
        Finset.mem_singleton] using hadj
    by_cases hvB : v = B
    · subst v
      have hw := (G.mem_neighborFinset B w).mpr ha.1
      rw [hnB, Finset.mem_singleton] at hw
      subst w
      exact ha.2 rfl
    by_cases hvM : v = M
    · subst v
      have hw := (G.mem_neighborFinset M w).mpr ha.1
      rw [hnM, Finset.mem_singleton] at hw
      subst w
      exact ha.2 Sym2.eq_swap
    exact hfixed v hv hvB hvM w ha.1
  have hsupp : H.support ⊆ {v | v ∉ fixed} := by
    intro v hv hvin
    obtain ⟨w, hw⟩ := (SimpleGraph.mem_support H).mp hv
    exact hHfixed v hvin w hw
  have hinduce : G.induce {v | v ∉ fixed} = H.induce {v | v ∉ fixed} := by
    ext v w
    have hvB : v.val ≠ B := by intro h; exact v.property (h.symm ▸ hB)
    have hvM : v.val ≠ M := by intro h; exact v.property (h.symm ▸ hM)
    change G.Adj v.val w.val ↔ H.Adj v.val w.val
    simp only [H, SimpleGraph.deleteEdges_adj, Finset.mem_coe, Finset.mem_singleton,
      Sym2.eq_iff, hvB, hvM, false_and, or_self, not_false_eq_true, and_true]
  have hedgeFinset : (G.induce {v | v ∉ fixed}).edgeFinset =
      (H.induce {v | v ∉ fixed}).edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr hinduce
  calc
    (G.induce {v | v ∉ fixed}).edgeFinset.card =
        (H.induce {v | v ∉ fixed}).edgeFinset.card := congrArg Finset.card hedgeFinset
    _ = H.edgeFinset.card := SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp
    _ = G.edgeFinset.card - 1 := hHcount

/-- The four actual edge descriptions and the corresponding numbers of
vertices outside their endpoints. This is an output predicate; no theorem
below assumes that its input graph belongs to one of these cases. -/
def FiveVertexForestShape (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.edgeFinset = ∅ ∨
  (∃ x y, x ≠ y ∧ G.edgeFinset = {s(x, y)} ∧
    (Finset.univ \ ({x, y} : Finset V)).card = 3 ∧
    ∀ v ∉ ({x, y} : Finset V), ∀ w, ¬ G.Adj v w) ∨
  (∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ G.edgeFinset = {s(x, y), s(y, z)} ∧
    (Finset.univ \ ({x, y, z} : Finset V)).card = 2 ∧
    ∀ v ∉ ({x, y, z} : Finset V), ∀ w, ¬ G.Adj v w) ∨
  (∃ x y z w, x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
    G.edgeFinset = {s(x, y), s(z, w)} ∧
    (Finset.univ \ ({x, y, z, w} : Finset V)).card = 1 ∧
    ∀ v ∉ ({x, y, z, w} : Finset V), ∀ u, ¬ G.Adj v u)

/-- Five vertices and at most two edges give exactly the four source
completions, with every omitted vertex proved isolated. -/
theorem five_vertex_two_edge_graph_cases
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 5) (hedges : G.edgeFinset.card ≤ 2) :
    FiveVertexForestShape G := by
  rcases graph_at_most_two_edge_cases G hedges with
    hempty | ⟨x, y, hxy, he⟩ | ⟨x, y, z, hxy, hxz, hyz, he⟩ |
      ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he⟩
  · exact Or.inl hempty
  · refine Or.inr (Or.inl ⟨x, y, hxy, he, ?_, ?_⟩)
    · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard]
      simp [hxy]
    · intro v hv
      have hv' : v ≠ x ∧ v ≠ y := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hv
      have he' : G.edgeFinset = {s(x, y), s(x, y)} := by simpa using he
      exact no_adj_outside_pair_edges G x y x y he' v hv'.1 hv'.2 hv'.1 hv'.2
  · refine Or.inr (Or.inr (Or.inl ⟨x, y, z, hxy, hxz, hyz, he, ?_, ?_⟩))
    · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard]
      simp [hxy, hxz, hyz]
    · intro v hv
      have hv' : v ≠ x ∧ v ≠ y ∧ v ≠ z := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hv
      exact no_adj_outside_pair_edges G x y y z he v hv'.1 hv'.2.1 hv'.2.1 hv'.2.2
  · refine Or.inr (Or.inr (Or.inr
      ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, he, ?_, ?_⟩))
    · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard]
      simp [hxy, hxz, hxw, hyz, hyw, hzw]
    · intro v hv
      have hv' : v ≠ x ∧ v ≠ y ∧ v ≠ z ∧ v ≠ w := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hv
      exact no_adj_outside_pair_edges G x y z w he v hv'.1 hv'.2.1 hv'.2.2.1 hv'.2.2.2

/-- The actual complement of the six family-E fixed vertices has five
canonical vertices and one of the four derived leftover graph shapes.
Its edge count is exactly one below the ambient edge count. -/
theorem familyE_remaining_forest
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B M D T U : V) (hcard : Fintype.card V = 11)
    (hC : weight C = 2) (hB : weight B = 3) (hM : weight M = 2)
    (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hBM : G.Adj B M) (hnB : G.neighborFinset B = {M}) (hnM : G.neighborFinset M = {B})
    (hCiso : ∀ v, ¬ G.Adj C v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (hedges : G.edgeFinset.card ≤ 3)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2) :
    let fixed : Finset V := {C, B, M, D, T, U}
    let Z := G.induce {v | v ∉ fixed}
    fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
      (∀ v : {v | v ∉ fixed}, weight v.val = 2) ∧
      Z.edgeFinset.card = G.edgeFinset.card - 1 ∧ FiveVertexForestShape Z := by
  classical
  let fixed : Finset V := {C, B, M, D, T, U}
  have hCB : C ≠ B := by intro h; have hw := congrArg weight h; rw [hC, hB] at hw; norm_num at hw
  have hCM : C ≠ M := by intro h; subst M; exact hCiso B hBM.symm
  have hCD : C ≠ D := by intro h; have hw := congrArg weight h; rw [hC, hD] at hw; norm_num at hw
  have hCT : C ≠ T := by intro h; have hw := congrArg weight h; rw [hC, hT] at hw; norm_num at hw
  have hCU : C ≠ U := by intro h; have hw := congrArg weight h; rw [hC, hU] at hw; norm_num at hw
  have hBD : B ≠ D := by intro h; have hw := congrArg weight h; rw [hB, hD] at hw; norm_num at hw
  have hMD : M ≠ D := by intro h; have hw := congrArg weight h; rw [hM, hD] at hw; norm_num at hw
  have hMT : M ≠ T := by intro h; have hw := congrArg weight h; rw [hM, hT] at hw; norm_num at hw
  have hMU : M ≠ U := by intro h; have hw := congrArg weight h; rw [hM, hU] at hw; norm_num at hw
  have hfixedCard : fixed.card = 6 := by
    simp [fixed, hCB, hCM, hCD, hCT, hCU, hBM.ne, hBD, Ne.symm hTB, Ne.symm hUB,
      hMD, hMT, hMU, Ne.symm hTD, Ne.symm hUD, hTU]
  have hremaining : Fintype.card {v | v ∉ fixed} = 5 := by
    calc
      _ = (Finset.univ \ fixed).card :=
        Fintype.card_of_subtype _ (fun v => by simp)
      _ = 5 := by
        rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hfixedCard]
  have hcanonical : ∀ v : {v | v ∉ fixed}, weight v.val = 2 := by
    intro v
    apply hother v.val
    all_goals intro h; exact v.property (by simp [fixed, h])
  have hfixedIso : ∀ v ∈ fixed, v ≠ B → v ≠ M → ∀ w, ¬ G.Adj v w := by
    intro v hv hvB hvM
    simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hCiso
    · exact (hvB rfl).elim
    · exact (hvM rfl).elim
    · exact hDiso
    · exact hTiso
    · exact hUiso
  have hcount := closed_edge_complement_edge_count G fixed B M hBM
    (by simp [fixed]) (by simp [fixed]) hnB hnM hfixedIso
  have hremainingEdges : (G.induce {v | v ∉ fixed}).edgeFinset.card ≤ 2 := by
    rw [hcount]
    omega
  exact ⟨hfixedCard, hremaining, hcanonical, hcount,
    five_vertex_two_edge_graph_cases _ hremaining hremainingEdges⟩

/-- Full family-E graph exhaustion from the ambient separated-source
hypotheses: the actual fixed components, the four remaining canonical
completions, and the source scalar values are all conclusions. -/
theorem familyE_complete_forest
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T U : V)
    (hcard : Fintype.card V = 11)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hedges : G.edgeFinset.card ≤ 3)
    (hB : weight B = 3) (hD : weight D = 4) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hUsingle : ∀ v, G.Reachable U v → v ≠ U → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2)
    (hvolume : 0 < -2 + dotProduct (fun i => weight i - 2) coeff)
    (hbudget : -2 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-2 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃ M, weight M = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
      G.neighborFinset M = {B} ∧
      (∀ v, G.Reachable B v ↔ v = B ∨ v = M) ∧
      (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 10 ∧
      -2 + dotProduct (fun i => weight i - 2) coeff = 1 / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 23 / 20 ∧
      (let fixed : Finset V := {C, B, M, D, T, U}
       let Z := G.induce {v | v ∉ fixed}
       fixed.card = 6 ∧ Fintype.card {v | v ∉ fixed} = 5 ∧
         (∀ v : {v | v ∉ fixed}, weight v.val = 2) ∧
         Z.edgeFinset.card = G.edgeFinset.card - 1 ∧ FiveVertexForestShape Z) := by
  obtain ⟨hCiso, hDiso, hTiso, hUiso, ⟨M, hM, hBM, hnB, hnM, hreach⟩,
      hell, hvol, hg⟩ := beta_four_two_extra_forest_fixed_components G weight coeff C B D T U
    hA hG hrow hedges hB hD hT hU hTB hTD hUB hUD hTU
    hcanonical hBsingle hDsingle hTsingle hUsingle hother hvolume hbudget hprojection
  exact ⟨M, hM, hBM, hnB, hnM, hreach, hCiso, hDiso, hTiso, hUiso, hell, hvol, hg,
    familyE_remaining_forest G weight C B M D T U hcard
      (hcanonical C (.refl C)) hB hM hD hT hU hTB hTD hUB hUD hTU
      hBM hnB hnM hCiso hDiso hTiso hUiso hedges hother⟩

end KltDP.LinearAlgebra
