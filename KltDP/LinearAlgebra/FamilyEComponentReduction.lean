import KltDP.LinearAlgebra.FamilyEScalarExclusion
import KltDP.LinearAlgebra.FamilyCClassification

/-!
# Beta-four restrictions in the ambient weighted forest

The one-extra impossibility and initial two-extra core restriction are
proved from the ambient row equation and ambient edge count. Component
Green entries, pairwise component separation, and the component charge cap
are derived. No finite rooted shape or component energy bound is supplied
as a hypothesis.

The canonical C-component and one higher-weight vertex per other component
are the earlier separation conclusions of manuscript Lemma 9.2. They are
stated here on actual reachable vertices. Realizing these data from the
geometric single-residue configuration remains a separate adapter.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

/-- Distinct noncanonical sources cannot share a component when all other
vertices in the first source's actual component have weight two. -/
theorem graph_single_sources_not_reachable
    {V : Type*} (G : SimpleGraph V) (weight : V → ℚ) (root other : V)
    (hne : root ≠ other)
    (hsingle : ∀ v, G.Reachable root v → v ≠ root → weight v = 2)
    (hother : weight other ≠ 2) : ¬ G.Reachable root other := by
  intro hreach
  exact hother (hsingle other hreach hne.symm)

/-- The actual edge budget for any finite collection of distinct single
sources follows from their weights and the ambient graph. -/
theorem graph_single_source_component_edge_budget
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (roots : I → V) [∀ i, DecidablePred (G.Reachable (roots i))]
    (hinjective : Function.Injective roots)
    (hnoncanonical : ∀ i, weight (roots i) ≠ 2)
    (hsingle : ∀ i v, G.Reachable (roots i) v → v ≠ roots i → weight v = 2) :
    (∑ i, (G.induce {v | G.Reachable (roots i) v}).edgeFinset.card) ≤
      G.edgeFinset.card := by
  apply sum_component_edgeFinset_card_le G roots
  intro i j hij
  exact graph_single_sources_not_reachable G weight (roots i) (roots j)
    (fun h => hij (hinjective h)) (hsingle i) (hnoncanonical j)

private theorem familyE_three_roots_injective
    {V : Type*} (B D T : V) (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D) :
    Function.Injective (![B, D, T] : Fin 3 → V) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.cons_val_zero', Matrix.cons_val_succ']

private theorem familyE_four_roots_injective
    {V : Type*} (B D T U : V) (hBD : B ≠ D)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U) :
    Function.Injective (![B, D, T, U] : Fin 4 → V) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.cons_val_zero', Matrix.cons_val_succ']

/-- An edge-free actual reachable component gives ambient isolation. -/
theorem graph_component_edgeFinset_empty_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    [DecidablePred (G.Reachable root)]
    (hempty : (G.induce {v | G.Reachable root v}).edgeFinset = ∅) :
    ∀ v, ¬ G.Adj root v := by
  have hbot : G.induce {v | G.Reachable root v} = ⊥ :=
    SimpleGraph.edgeFinset_eq_empty.mp hempty
  intro v hv
  have hinside : (G.induce {w | G.Reachable root w}).Adj
      ⟨root, SimpleGraph.Reachable.refl root⟩ ⟨v, hv.reachable⟩ := hv
  rw [hbot] at hinside
  exact hinside

section AmbientForest

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem familyE_three_sum (f : V → ℕ) (B D T : V) :
    (∑ i : Fin 3, f (![B, D, T] i)) = f B + f D + f T := by
  exact Fin.sum_univ_three (fun i => f (![B, D, T] i))

private theorem familyE_four_sum (f : V → ℕ) (B D T U : V) :
    (∑ i : Fin 4, f (![B, D, T, U] i)) = f B + f D + f T + f U := by
  exact Fin.sum_univ_four (fun i => f (![B, D, T, U] i))

/- Scalar normalization is deliberately proved before substituting graph
inverse entries. This keeps arithmetic reflection from unfolding inverse,
finite component, or reachability-instance expressions. -/
private theorem familyE_scalar_length (pair b d : ℚ)
    (hl : 1 - pair = 2 / 4 - 1 / 3 - (b - 1 / 3) - (4 - 2) * (d - 1 / 4))
    (hpos : 0 < 1 - pair) :
    (b - 1 / 3) + 2 * (d - 1 / 4) < 1 / 6 := by
  linarith only [hl, hpos]

private theorem familyE_scalar_one_extra_false (source b d t : ℚ)
    (hv : 2 - 4 + source =
      -5 / 3 + 4 / 4 + (b - 1 / 3) + (4 - 2)^2 * (d - 1 / 4) + t)
    (hpos : 0 < -2 + source)
    (hbound : -2 / 3 + (b - 1 / 3) + 4 * (d - 1 / 4) + t ≤ 0) : False := by
  linarith only [hv, hpos, hbound]

private theorem familyE_scalar_two_extra_cap (pair source b d t u : ℚ)
    (hl : 1 - pair = 2 / 4 - 1 / 3 - (b - 1 / 3) - (4 - 2) * (d - 1 / 4))
    (hv : 2 - 4 + source =
      -5 / 3 + 4 / 4 + (b - 1 / 3) + (4 - 2)^2 * (d - 1 / 4) + (t + u))
    (hbudget : -2 + source ≤ 1 - pair) :
    t + u + 2 * (b - 1 / 3) + 6 * (d - 1 / 4) ≤ 5 / 6 := by
  linarith only [hl, hv, hbudget]

private theorem familyE_length_transport (b d b' d' : ℚ)
    (hb : b = b') (hd : d = d')
    (h : (b' - 1 / 3) + 2 * (d' - 1 / 4) < 1 / 6) :
    (b - 1 / 3) + 2 * (d - 1 / 4) < 1 / 6 := by
  simpa only [hb, hd] using h

private theorem familyE_nonpositive_transport (b d t b' d' t' : ℚ)
    (hb : b = b') (hd : d = d') (ht : t = t')
    (h : -2 / 3 + (b - 1 / 3) + 4 * (d - 1 / 4) + t ≤ 0) :
    -2 / 3 + (b' - 1 / 3) + 4 * (d' - 1 / 4) + t' ≤ 0 := by
  simpa only [hb, hd, ht] using h

private theorem familyE_cap_transport (b d t u b' d' t' u' : ℚ)
    (hb : b = b') (hd : d = d') (ht : t = t') (hu : u = u')
    (h : t' + u' + 2 * (b' - 1 / 3) + 6 * (d' - 1 / 4) ≤ 5 / 6) :
    t + u + 2 * (b - 1 / 3) + 6 * (d - 1 / 4) ≤ 5 / 6 := by
  simpa only [hb, hd, ht, hu] using h

set_option maxHeartbeats 1200000 in
/-- The beta-four one-extra configuration cannot have both positive length
and positive square. The component budget and discrepancy bound are derived
from the ambient forest, its exact row equation, and the displayed positive
quantities; they are not extra component-level assumptions. -/
theorem beta_four_one_extra_forest_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T : V)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hrow : graphWeightMatrix G weight *ᵥ coeff = fun i => weight i - 2)
    (hedges : G.edgeFinset.card ≤ 3)
    (hB : weight B = 3) (hD : weight D = 4) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hcanonical : ∀ v, G.Reachable C v → weight v = 2)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2)
    (hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff)
    (hvolume : 0 < -2 + dotProduct (fun i => weight i - 2) coeff) : False := by
  let A : Matrix V V ℚ := graphWeightMatrix G weight
  let GB : SimpleGraph {v | G.Reachable B v} := G.induce {v | G.Reachable B v}
  let GD : SimpleGraph {v | G.Reachable D v} := G.induce {v | G.Reachable D v}
  let GT : SimpleGraph {v | G.Reachable T v} := G.induce {v | G.Reachable T v}
  let rB : {v | G.Reachable B v} := ⟨B, SimpleGraph.Reachable.refl B⟩
  let rD : {v | G.Reachable D v} := ⟨D, SimpleGraph.Reachable.refl D⟩
  let rT : {v | G.Reachable T v} := ⟨T, SimpleGraph.Reachable.refl T⟩
  have hBDne : B ≠ D := by
    intro h
    have hw := congrArg weight h
    rw [hB, hD] at hw
    norm_num at hw
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
  have hBD := graph_single_sources_not_reachable G weight B D hBDne hBsingle
    (by rw [hD]; norm_num)
  have hextras : ∀ t ∈ ({T} : Finset V), t ≠ B ∧ t ≠ D ∧ weight t = 3 := by
    intro t ht
    have htT := Finset.mem_singleton.mp ht
    subst t
    exact ⟨hTB, hTD, hT⟩
  have hsingle : ∀ t ∈ ({T} : Finset V),
      ∀ v, G.Reachable t v → v ≠ t → weight v = 2 := by
    intro t ht
    have htT := Finset.mem_singleton.mp ht
    subst t
    exact hTsingle
  have hother' : ∀ v, v ≠ B → v ≠ D → v ∉ ({T} : Finset V) → weight v = 2 := by
    intro v hvB hvD hvT
    exact hother v hvB hvD (by simpa only [Finset.mem_singleton] using hvT)
  obtain ⟨hl, hv, _⟩ := separated_graph_block_identities G weight coeff C B D {T}
    4 hA hrow hB hD (by norm_num) hCB hCD hBD hcanonical hBsingle hDsingle
    hextras hsingle hother'
  simp only [Finset.sum_singleton] at hv
  have hnoncanonical : ∀ i : Fin 3, weight (![B, D, T] i) ≠ 2 := by
    intro i
    fin_cases i <;> norm_num [hB, hD, hT]
  have hsources : ∀ i : Fin 3, ∀ v,
      G.Reachable (![B, D, T] i) v → v ≠ ![B, D, T] i → weight v = 2 := by
    intro i
    fin_cases i
    · simpa using hBsingle
    · simpa using hDsingle
    · simpa using hTsingle
  have hsum := graph_single_source_component_edge_budget G weight (![B, D, T])
    (familyE_three_roots_injective B D T hBDne hTB hTD) hnoncanonical hsources
  have hbudget : GB.edgeFinset.card + GD.edgeFinset.card + GT.edgeFinset.card ≤ 3 := by
    calc
      _ = ∑ i : Fin 3, (G.induce {v | G.Reachable (![B, D, T] i) v}).edgeFinset.card :=
        (familyE_three_sum (fun root =>
          (G.induce {v | G.Reachable root v}).edgeFinset.card) B D T).symm
      _ ≤ 3 := hsum.trans hedges
  have hgreenB : rootedTreeGreen GB rB 3 = A⁻¹ B B :=
    graph_single_root_component_green G weight B 3 hA hB hBsingle
  have hgreenD : rootedTreeGreen GD rD 4 = A⁻¹ D D :=
    graph_single_root_component_green G weight D 4 hA hD hDsingle
  have hgreenT : rootedTreeGreen GT rT 3 = A⁻¹ T T :=
    graph_single_root_component_green G weight T 3 hA hT hTsingle
  have hlengthCap := familyE_scalar_length
    (dotProduct (threeMarkedSource C B D) coeff) (A⁻¹ B B) (A⁻¹ D D) hl hlength
  have hcomponentLength :
      (rootedTreeGreen GB rB 3 - 1 / 3) +
        2 * (rootedTreeGreen GD rD 4 - 1 / 4) < 1 / 6 :=
    familyE_length_transport _ _ _ _ hgreenB hgreenD hlengthCap
  have hnonpositive : -2 / 3 + (rootedTreeGreen GB rB 3 - 1 / 3) +
      4 * (rootedTreeGreen GD rD 4 - 1 / 4) + rootedTreeGreen GT rT 3 ≤ 0 :=
    (betaFour_one_extra_trees_nonpositive GB GD GT rB rD rT
    (graph_reachable_component_isTree G B hG)
    (graph_reachable_component_isTree G D hG)
    (graph_reachable_component_isTree G T hG) hbudget hcomponentLength).2.2
  have hfullNonpositive := familyE_nonpositive_transport _ _ _ _ _ _
    hgreenB hgreenD hgreenT hnonpositive
  exact familyE_scalar_one_extra_false (dotProduct (fun i => weight i - 2) coeff)
    (A⁻¹ B B) (A⁻¹ D D) (A⁻¹ T T) hv hvolume hfullNonpositive

set_option maxHeartbeats 1200000 in
/-- In the beta-four two-extra case the ambient v ≤ ell inequality forces
an isolated weight-four core and either an isolated weight-three core or
one actual closed edge from it to a weight-two leaf. The ambient row equation
supplies the full component cap, and the forest supplies all four trees and
their combined edge allowance. -/
theorem beta_four_two_extra_forest_core_restriction
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight coeff : V → ℚ) (C B D T U : V)
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
    (hbudget : -2 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff) :
    (∀ v, ¬ G.Adj D v) ∧
      ((∀ v, ¬ G.Adj B v) ∨
        ∃ M, weight M = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
          G.neighborFinset M = {B} ∧
          ∀ v, G.Reachable B v ↔ v = B ∨ v = M) := by
  let A : Matrix V V ℚ := graphWeightMatrix G weight
  let GB : SimpleGraph {v | G.Reachable B v} := G.induce {v | G.Reachable B v}
  let GD : SimpleGraph {v | G.Reachable D v} := G.induce {v | G.Reachable D v}
  let GT : SimpleGraph {v | G.Reachable T v} := G.induce {v | G.Reachable T v}
  let GU : SimpleGraph {v | G.Reachable U v} := G.induce {v | G.Reachable U v}
  let rB : {v | G.Reachable B v} := ⟨B, SimpleGraph.Reachable.refl B⟩
  let rD : {v | G.Reachable D v} := ⟨D, SimpleGraph.Reachable.refl D⟩
  let rT : {v | G.Reachable T v} := ⟨T, SimpleGraph.Reachable.refl T⟩
  let rU : {v | G.Reachable U v} := ⟨U, SimpleGraph.Reachable.refl U⟩
  have hBDne : B ≠ D := by
    intro h
    have hw := congrArg weight h
    rw [hB, hD] at hw
    norm_num at hw
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
  have hBD := graph_single_sources_not_reachable G weight B D hBDne hBsingle
    (by rw [hD]; norm_num)
  have hextras : ∀ t ∈ ({T, U} : Finset V), t ≠ B ∧ t ≠ D ∧ weight t = 3 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨hTB, hTD, hT⟩
    · have htU := Finset.mem_singleton.mp ht
      subst t
      exact ⟨hUB, hUD, hU⟩
  have hsingle : ∀ t ∈ ({T, U} : Finset V),
      ∀ v, G.Reachable t v → v ≠ t → weight v = 2 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hTsingle
    · have htU := Finset.mem_singleton.mp ht
      subst t
      exact hUsingle
  have hother' : ∀ v, v ≠ B → v ≠ D → v ∉ ({T, U} : Finset V) → weight v = 2 := by
    intro v hvB hvD hv
    have hvT : v ≠ T := by intro h; subst v; simp at hv
    have hvU : v ≠ U := by intro h; subst v; simp at hv
    exact hother v hvB hvD hvT hvU
  obtain ⟨hl, hv, _⟩ := separated_graph_block_identities G weight coeff C B D {T, U}
    4 hA hrow hB hD (by norm_num) hCB hCD hBD hcanonical hBsingle hDsingle
    hextras hsingle hother'
  simp only [Finset.sum_insert (by simp [hTU] : T ∉ ({U} : Finset V)),
    Finset.sum_singleton] at hv
  have hcap :
      A⁻¹ T T + A⁻¹ U U + 2 * (A⁻¹ B B - 1 / 3) + 6 * (A⁻¹ D D - 1 / 4) ≤ 5 / 6 :=
    familyE_scalar_two_extra_cap (dotProduct (threeMarkedSource C B D) coeff)
      (dotProduct (fun i => weight i - 2) coeff)
      (A⁻¹ B B) (A⁻¹ D D) (A⁻¹ T T) (A⁻¹ U U) hl hv hbudget
  have hnoncanonical : ∀ i : Fin 4, weight (![B, D, T, U] i) ≠ 2 := by
    intro i
    fin_cases i <;> norm_num [hB, hD, hT, hU]
  have hsources : ∀ i : Fin 4, ∀ v,
      G.Reachable (![B, D, T, U] i) v → v ≠ ![B, D, T, U] i → weight v = 2 := by
    intro i
    fin_cases i
    · simpa using hBsingle
    · simpa using hDsingle
    · simpa using hTsingle
    · simpa using hUsingle
  have hsum := graph_single_source_component_edge_budget G weight (![B, D, T, U])
    (familyE_four_roots_injective B D T U hBDne hTB hTD hUB hUD hTU)
    hnoncanonical hsources
  have hedgeBudget : GB.edgeFinset.card + GD.edgeFinset.card +
      GT.edgeFinset.card + GU.edgeFinset.card ≤ 3 := by
    calc
      _ = ∑ i : Fin 4, (G.induce {v | G.Reachable (![B, D, T, U] i) v}).edgeFinset.card :=
        (familyE_four_sum (fun root =>
          (G.induce {v | G.Reachable root v}).edgeFinset.card) B D T U).symm
      _ ≤ 3 := hsum.trans hedges
  have hgreenB : rootedTreeGreen GB rB 3 = A⁻¹ B B :=
    graph_single_root_component_green G weight B 3 hA hB hBsingle
  have hgreenD : rootedTreeGreen GD rD 4 = A⁻¹ D D :=
    graph_single_root_component_green G weight D 4 hA hD hDsingle
  have hgreenT : rootedTreeGreen GT rT 3 = A⁻¹ T T :=
    graph_single_root_component_green G weight T 3 hA hT hTsingle
  have hgreenU : rootedTreeGreen GU rU 3 = A⁻¹ U U :=
    graph_single_root_component_green G weight U 3 hA hU hUsingle
  have hcomponentCap :
      rootedTreeGreen GT rT 3 + rootedTreeGreen GU rU 3 +
        2 * (rootedTreeGreen GB rB 3 - 1 / 3) +
        6 * (rootedTreeGreen GD rD 4 - 1 / 4) ≤ 5 / 6 :=
    familyE_cap_transport _ _ _ _ _ _ _ _ hgreenB hgreenD hgreenT hgreenU hcap
  obtain ⟨hDempty, hBshape⟩ := betaFour_two_extra_trees_core_restriction GB GD GT GU
    rB rD rT rU
    (graph_reachable_component_isTree G B hG)
    (graph_reachable_component_isTree G D hG)
    (graph_reachable_component_isTree G T hG)
    (graph_reachable_component_isTree G U hG) hedgeBudget hcomponentCap
  refine ⟨graph_component_edgeFinset_empty_isolated G D hDempty, ?_⟩
  rcases hBshape with hempty | ⟨e, _⟩
  · exact Or.inl (graph_component_edgeFinset_empty_isolated G B hempty)
  · obtain ⟨M, hadj, hBneighbors, hMneighbors, hreach⟩ :=
      component_iso_edge_has_mutual_singleton_neighbors G B e
    exact Or.inr ⟨M, hBsingle M hadj.reachable hadj.ne.symm,
      hadj, hBneighbors, hMneighbors, hreach⟩

end AmbientForest

end KltDP.LinearAlgebra
