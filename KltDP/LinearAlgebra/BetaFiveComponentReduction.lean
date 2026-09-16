import KltDP.LinearAlgebra.BetaFiveCoreIsolation
import KltDP.LinearAlgebra.BetaFiveTreeExclusion
import KltDP.LinearAlgebra.FamilyCClassification

/-!
# Excluding beta five from actual ambient source equations

The distinguished core vertices are first proved isolated using their
actual row equations and positive length. Their Green entries are then
derived. The actual marked boundary must occur in C's canonical component,
so that component consumes an edge of the ambient four-edge budget.

One and two actual extra components are excluded by the already proved
arbitrary-tree charge bounds. All component budgets and scalar identities
are derived here; neither isolation nor a charge table is an assumption.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An actual edge at a root is also an actual edge of its induced
reachable component. -/
theorem graph_component_edge_card_pos_of_adj
    (G : SimpleGraph V) [DecidableRel G.Adj] (root u : V)
    [DecidablePred (G.Reachable root)] (h : G.Adj root u) :
    0 < (G.induce {v | G.Reachable root v}).edgeFinset.card := by
  let root' : {v | G.Reachable root v} := ⟨root, SimpleGraph.Reachable.refl root⟩
  let u' : {v | G.Reachable root v} := ⟨u, h.reachable⟩
  apply Finset.card_pos.mpr
  refine ⟨s(root', u'), ?_⟩
  change s(root', u') ∈ (G.induce {v | G.Reachable root v}).edgeFinset
  simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
    (show (G.induce {v | G.Reachable root v}).Adj root' u' from h)

/-- The original beta-five source definitions specialize to the isolated
core scalars. The boundary edge is recovered at C, since the other two
marked vertices are proved isolated. The extra set is an actual finite
set of noncore weight-three vertices. -/
theorem beta_five_source_component_values
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight coeff : V → ℚ)
    (C B D : V) (extras : Finset V)
    (hA : IsUnit (graphWeightMatrix G weight))
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ v, 0 ≤ coeff v)
    (hB : weight B = 3) (hD : weight D = 5)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hextras : ∀ t ∈ extras, t ≠ B ∧ t ≠ D ∧ weight t = 3)
    (hsingle : ∀ t ∈ extras, ∀ v, G.Reachable t v → v ≠ t → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ∉ extras → weight v = 2)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v) :
    (∀ v, ¬ G.Adj B v) ∧ (∀ v, ¬ G.Adj D v) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 15 ∧
      -3 + dotProduct (fun i => weight i - 2) coeff =
        (∑ t ∈ extras, (graphWeightMatrix G weight)⁻¹ t t) - 13 / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) =
        (graphWeightMatrix G weight)⁻¹ C C + 8 / 15 ∧
      ∃ v, G.Adj C v := by
  obtain ⟨hBi, hDi, hb, hd, _, _⟩ := beta_five_core_source_rigidity
    G weight coeff C B D hrow hcoeff hB hD hlength hBsingle hDsingle
  have hBgreen := graph_single_source_coefficient G weight coeff hA hrow B hBsingle
  have hDgreen := graph_single_source_coefficient G weight coeff hA hrow D hDsingle
  rw [hB] at hBgreen
  rw [hD] at hDgreen
  have hbb : (graphWeightMatrix G weight)⁻¹ B B = 1 / 3 := by
    linarith only [hb, hBgreen]
  have hdd : (graphWeightMatrix G weight)⁻¹ D D = 1 / 5 := by
    linarith only [hd, hDgreen]
  have hCB : ¬ G.Reachable C B := by
    intro h
    have hw := hcanonical B h
    rw [hB] at hw
    norm_num at hw
  have hCD : ¬ G.Reachable C D := by
    intro h
    have hw := hcanonical D h
    rw [hD] at hw
    norm_num at hw
  have hBDne : B ≠ D := by intro h; have := congrArg weight h; linarith
  have hBD : ¬ G.Reachable B D := by
    intro h
    have hw := hBsingle D h hBDne.symm
    rw [hD] at hw
    norm_num at hw
  obtain ⟨hl, hv, hg⟩ := separated_graph_block_identities G weight coeff C B D extras 5
    hA hrow hB hD (by norm_num) hCB hCD hBD hcanonical hBsingle hDsingle
    hextras hsingle hother
  rw [hbb, hdd] at hl hv hg
  norm_num at hl hv hg
  refine ⟨hBi, hDi, ?_, ?_, ?_, ?_⟩
  · linarith only [hl]
  · linarith only [hv]
  · linarith only [hg]
  · obtain ⟨v, hC | hB | hD⟩ := hboundary
    · exact ⟨v, hC⟩
    · exact (hBi v hB).elim
    · exact (hDi v hD).elim

/-- The actual one-extra beta-five configuration is impossible. The edge
at C leaves at most three edges for the extra's actual tree component. -/
theorem beta_five_one_extra_forest_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T : V)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ v, 0 ≤ coeff v) (hedges : G.edgeFinset.card ≤ 4)
    (hB : weight B = 3) (hD : weight D = 5) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hvolume : 0 < -3 + dotProduct (fun i => weight i - 2) coeff)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v) : False := by
  obtain ⟨_, _, _, hv, _, u, hCu⟩ := beta_five_source_component_values
    G weight coeff C B D {T} hA hrow hcoeff hB hD hcanonical hBsingle hDsingle
    (fun t ht => by
      have heq := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hTB, hTD, hT⟩)
    (fun t ht => by
      have heq := Finset.mem_singleton.mp ht
      subst t
      exact hTsingle)
    (fun i hiB hiD hiT => hother i hiB hiD
      (by simpa only [Finset.mem_singleton] using hiT)) hlength hboundary
  simp only [Finset.sum_singleton] at hv
  have hCT : ¬ G.Reachable C T := by
    intro h
    have hw := hcanonical T h
    rw [hT] at hw
    norm_num at hw
  have hTC : ¬ G.Reachable T C := fun h => hCT h.symm
  have hseparate : ∀ i j : Fin 2, i ≠ j →
      ¬ G.Reachable (![C, T] i) (![C, T] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hsum := sum_component_edgeFinset_card_le G (![C, T]) hseparate
  have hbudget : (G.induce {v | G.Reachable C v}).edgeFinset.card +
      (G.induce {v | G.Reachable T v}).edgeFinset.card ≤ 4 := by
    simpa [Fin.sum_univ_succ] using hsum.trans hedges
  have hCpos := graph_component_edge_card_pos_of_adj G C u hCu
  have hnegative := betaFive_one_extra_volume_neg
    (G.induce {v | G.Reachable T v}) ⟨T, SimpleGraph.Reachable.refl T⟩
    (graph_reachable_component_isTree G T hG) (by omega)
  rw [graph_single_root_component_green G weight T 3 hA hT hTsingle] at hnegative
  linarith only [hv, hvolume, hnegative]

set_option maxHeartbeats 400000 in
/-- The actual two-extra beta-five configuration is impossible. Every
component edge allowance and every scalar specialization is derived from
the ambient data and the original projection equation. -/
theorem beta_five_two_extra_forest_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T U : V)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hcoeff : ∀ v, 0 ≤ coeff v) (hedges : G.edgeFinset.card ≤ 4)
    (hB : weight B = 3) (hD : weight D = 5) (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hUsingle : ∀ v, G.Reachable U v → v ≠ U → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → v ≠ U → weight v = 2)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hvolume : 0 < -3 + dotProduct (fun i => weight i - 2) coeff)
    (hboundary : ∃ v, G.Adj C v ∨ G.Adj B v ∨ G.Adj D v)
    (hprojection :
      (-3 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) : False := by
  have hextras : ∀ t ∈ ({T, U} : Finset V), t ≠ B ∧ t ≠ D ∧ weight t = 3 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨hTB, hTD, hT⟩
    · have heq := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hUB, hUD, hU⟩
  have hsingle : ∀ t ∈ ({T, U} : Finset V),
      ∀ v, G.Reachable t v → v ≠ t → weight v = 2 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hTsingle
    · have heq := Finset.mem_singleton.mp ht
      subst t
      exact hUsingle
  have hother' : ∀ v, v ≠ B → v ≠ D → v ∉ ({T, U} : Finset V) → weight v = 2 := by
    intro v hvB hvD hv
    have hvT : v ≠ T := by intro h; subst v; simp at hv
    have hvU : v ≠ U := by intro h; subst v; simp at hv
    exact hother v hvB hvD hvT hvU
  obtain ⟨_, _, hl, hv, hg, u, hCu⟩ := beta_five_source_component_values
    G weight coeff C B D {T, U} hA hrow hcoeff hB hD hcanonical hBsingle hDsingle
    hextras hsingle hother' hlength hboundary
  simp only [Finset.sum_insert (by simp [hTU] : T ∉ ({U} : Finset V)),
    Finset.sum_singleton] at hv
  have hCT : ¬ G.Reachable C T := by
    intro h
    have hw := hcanonical T h
    rw [hT] at hw
    norm_num at hw
  have hCU : ¬ G.Reachable C U := by
    intro h
    have hw := hcanonical U h
    rw [hU] at hw
    norm_num at hw
  have hTU' : ¬ G.Reachable T U := by
    intro h
    have hw := hTsingle U h hTU.symm
    rw [hU] at hw
    norm_num at hw
  have hTC : ¬ G.Reachable T C := fun h => hCT h.symm
  have hUC : ¬ G.Reachable U C := fun h => hCU h.symm
  have hUT : ¬ G.Reachable U T := fun h => hTU' h.symm
  have hseparate : ∀ i j : Fin 3, i ≠ j →
      ¬ G.Reachable (![C, T, U] i) (![C, T, U] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hij rfl).elim
      | exact hCT
      | exact hCU
      | exact hTC
      | exact hTU'
      | exact hUC
      | exact hUT
  have hsum := sum_component_edgeFinset_card_le G (![C, T, U]) hseparate
  have hbudget : (G.induce {v | G.Reachable C v}).edgeFinset.card +
      (G.induce {v | G.Reachable T v}).edgeFinset.card +
      (G.induce {v | G.Reachable U v}).edgeFinset.card ≤ 4 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum.trans hedges
  have hgreenC := graph_single_root_component_green G weight C 2 hA
    (hcanonical C (SimpleGraph.Reachable.refl C)) (fun v hv _ => hcanonical v hv)
  have hgreenT := graph_single_root_component_green G weight T 3 hA hT hTsingle
  have hgreenU := graph_single_root_component_green G weight U 3 hA hU hUsingle
  have hscalarprojection :
      ((graphWeightMatrix G weight)⁻¹ T T + (graphWeightMatrix G weight)⁻¹ U U - 13 / 15) *
        ((graphWeightMatrix G weight)⁻¹ C C + 8 / 15 - 1) = (1 / 15 : ℚ)^2 :=
    (congrArg₂ (fun v g : ℚ => v * (g - 1)) hv hg).symm.trans
      (hprojection.trans (congrArg (fun ell : ℚ => ell^2) hl))
  apply betaFive_two_extra_trees_impossible
    (G.induce {v | G.Reachable C v})
    (G.induce {v | G.Reachable T v})
    (G.induce {v | G.Reachable U v})
    ⟨C, SimpleGraph.Reachable.refl C⟩ ⟨T, SimpleGraph.Reachable.refl T⟩
    ⟨U, SimpleGraph.Reachable.refl U⟩
    (graph_reachable_component_isTree G C hG)
    (graph_reachable_component_isTree G T hG)
    (graph_reachable_component_isTree G U hG)
    (graph_component_edge_card_pos_of_adj G C u hCu) hbudget
  · rw [hgreenT, hgreenU, ← hv]
    exact hvolume
  · rw [hgreenC, hgreenT, hgreenU]
    exact hscalarprojection

end KltDP.LinearAlgebra
