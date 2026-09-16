import KltDP.LinearAlgebra.FamilyEComponentReduction

/-!
# Fixed components of family E from actual forest data

The beta-four two-extra case has exactly one fixed-component allocation:
C, D and the two extras are isolated, while B has one weight-two leaf.
The finite arithmetic uses the previously proved eight rooted shapes;
the actual-tree and ambient-forest statements derive those shapes by
proved graph isomorphisms and identify their actual inverse entries.

No shape, table membership, component cap, or component inverse identity
is assumed about the ambient graph. The remaining five-vertex canonical
forest, which gives four completions E1--E4, is handled separately.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph
open scoped BigOperators

private theorem familyE_green_point (b : ℚ) :
    rootedBlockGreen (.arms .point) b = 1 / b := by
  norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]

private theorem familyE_green_endEdge_three :
    rootedBlockGreen (.arms .endEdge) 3 = 2 / 5 := by
  norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]

set_option maxHeartbeats 1200000 in
/-- The cap in the one-leaf core branch forces both extra choices to be
points, by checking all their proved root Green values. -/
theorem betaFour_extra_choices_of_small_sum (extra first : RootedBlockChoice)
    (hcap : rootedBlockGreen extra 3 + rootedBlockGreen first 3 ≤ 7 / 10) :
    extra = .arms .point ∧ first = .arms .point := by
  rcases (exists_rootedBlockChoice (fun choice => extra = choice)).mp ⟨extra, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (exists_rootedBlockChoice (fun choice => first = choice)).mp ⟨first, rfl⟩ with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator] at hcap ⊢

/-- Only the isolated canonical choice has diagonal inverse entry one half. -/
theorem canonical_rooted_choice_of_green_half (choice : RootedBlockChoice)
    (hgreen : rootedBlockGreen choice 2 = 1 / 2) : choice = .arms .point := by
  rcases (exists_rootedBlockChoice (fun c => choice = c)).mp ⟨choice, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator] at hgreen ⊢

set_option maxHeartbeats 4000000 in
/-- Isolated cores leave no possible actual rooted-choice allocation to C
and the two extras under the full scalar conditions. All canonical root
positions are tested, so a separate leaf hypothesis is unnecessary here. -/
theorem betaFour_isolated_core_choices_impossible
    (canonical extra first : RootedBlockChoice)
    (hedges : rootedBlockEdges canonical + rootedBlockEdges extra +
      rootedBlockEdges first ≤ 3)
    (hvolume : 0 < -2 / 3 + rootedBlockGreen extra 3 + rootedBlockGreen first 3)
    (hbudget : -2 / 3 + rootedBlockGreen extra 3 + rootedBlockGreen first 3 ≤ 1 / 6)
    (hprojection :
      (-2 / 3 + rootedBlockGreen extra 3 + rootedBlockGreen first 3) *
        (rootedBlockGreen canonical 2 - 5 / 12) = (1 / 6 : ℚ)^2) : False := by
  rcases (exists_rootedBlockChoice (fun choice => canonical = choice)).mp
      ⟨canonical, rfl⟩ with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (exists_rootedBlockChoice (fun choice => extra = choice)).mp ⟨extra, rfl⟩ with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (exists_rootedBlockChoice (fun choice => first = choice)).mp ⟨first, rfl⟩ with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
      rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]
      at hedges hvolume hbudget hprojection

/-- The full fixed-component classification of beta four with two extras.
The initial two-core restriction is reused before the remaining small
canonical and extra-component cases are eliminated. -/
theorem betaFour_two_extra_rooted_choices
    (canonical left right extra first : RootedBlockChoice)
    (hedges : rootedBlockEdges canonical + rootedBlockEdges left +
      rootedBlockEdges right + rootedBlockEdges extra + rootedBlockEdges first ≤ 3)
    (hvolume : 0 < -2 / 3 + (rootedBlockGreen left 3 - 1 / 3) +
      4 * (rootedBlockGreen right 4 - 1 / 4) +
      rootedBlockGreen extra 3 + rootedBlockGreen first 3)
    (hbudget : -2 / 3 + (rootedBlockGreen left 3 - 1 / 3) +
      4 * (rootedBlockGreen right 4 - 1 / 4) +
      rootedBlockGreen extra 3 + rootedBlockGreen first 3 ≤
      1 / 6 - (rootedBlockGreen left 3 - 1 / 3) -
        2 * (rootedBlockGreen right 4 - 1 / 4))
    (hprojection :
      (-2 / 3 + (rootedBlockGreen left 3 - 1 / 3) +
        4 * (rootedBlockGreen right 4 - 1 / 4) +
        rootedBlockGreen extra 3 + rootedBlockGreen first 3) *
        (rootedBlockGreen canonical 2 - 5 / 12 +
          (rootedBlockGreen left 3 - 1 / 3) + (rootedBlockGreen right 4 - 1 / 4)) =
        (1 / 6 - (rootedBlockGreen left 3 - 1 / 3) -
          2 * (rootedBlockGreen right 4 - 1 / 4))^2) :
    canonical = .arms .point ∧ left = .arms .endEdge ∧ right = .arms .point ∧
      extra = .arms .point ∧ first = .arms .point := by
  have hlowExtra := rootedBlockGreen_three_lower extra
  have hlowFirst := rootedBlockGreen_three_lower first
  have hcap : rootedBlockGreen extra 3 + rootedBlockGreen first 3 +
      2 * (rootedBlockGreen left 3 - 1 / 3) +
      6 * (rootedBlockGreen right 4 - 1 / 4) ≤ 5 / 6 := by
    linarith only [hbudget]
  have hcore : 2 * (rootedBlockGreen left 3 - 1 / 3) +
      6 * (rootedBlockGreen right 4 - 1 / 4) ≤ 1 / 6 := by
    linarith only [hcap, hlowExtra, hlowFirst]
  obtain ⟨rfl, hleft⟩ := betaFour_two_extra_core_choices left right hcore
  rcases hleft with rfl | rfl
  · exfalso
    have hedge' : rootedBlockEdges canonical + rootedBlockEdges extra +
        rootedBlockEdges first ≤ 3 := by
      simpa [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ] using hedges
    norm_num [familyE_green_point] at hvolume hbudget hprojection
    exact betaFour_isolated_core_choices_impossible canonical extra first
      hedge' (by linarith only [hvolume]) (by linarith only [hbudget])
      (by nlinarith only [hprojection])
  · have hsum : rootedBlockGreen extra 3 + rootedBlockGreen first 3 ≤ 7 / 10 := by
      norm_num [familyE_green_point, familyE_green_endEdge_three] at hcap
      linarith only [hcap]
    obtain ⟨rfl, rfl⟩ := betaFour_extra_choices_of_small_sum extra first hsum
    have hhalf : rootedBlockGreen canonical 2 = 1 / 2 := by
      norm_num [familyE_green_point, familyE_green_endEdge_three] at hprojection
      nlinarith only [hprojection]
    exact ⟨canonical_rooted_choice_of_green_half canonical hhalf, rfl, rfl, rfl, rfl⟩

/-- Transport a proved rooted inverse value from an actual graph
isomorphism. The b=2 branch uses the canonical specialization of the
matrix formulas; b>=3 uses their general theorem. -/
theorem rootedTreeGreen_of_iso_at_two_or_ge_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (root : V)
    {choice : RootedBlockChoice} (e : G ≃g rootedBlockGraph choice)
    (hroot : e root = rootedBlockRoot choice) (b : ℚ) (hb : b = 2 ∨ 3 ≤ b) :
    rootedTreeGreen G root b = rootedBlockGreen choice b := by
  change (rootedGraphMatrix G root b)⁻¹ root root = _
  rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot b,
    ← rootedBlockMatrixAt_eq_graph]
  rcases hb with rfl | hb
  · exact rootedBlockMatrixAt_inverse_root_two choice
  · exact rootedBlockMatrixAt_inverse_root choice hb

/-- The unique fixed allocation for five actual rooted component trees.
The combined budget concerns their actual edge counts. Graph isomorphisms
and exact inverse entries are derived for every component. -/
theorem beta_four_two_extra_actual_trees
    {VC VB VD VT VU : Type*}
    [Fintype VC] [Fintype VB] [Fintype VD] [Fintype VT] [Fintype VU]
    [DecidableEq VC] [DecidableEq VB] [DecidableEq VD] [DecidableEq VT] [DecidableEq VU]
    (GC : SimpleGraph VC) (GB : SimpleGraph VB) (GD : SimpleGraph VD)
    (GT : SimpleGraph VT) (GU : SimpleGraph VU)
    [DecidableRel GC.Adj] [DecidableRel GB.Adj] [DecidableRel GD.Adj]
    [DecidableRel GT.Adj] [DecidableRel GU.Adj]
    (C : VC) (B : VB) (D : VD) (T : VT) (U : VU)
    (hC : GC.IsTree) (hB : GB.IsTree) (hD : GD.IsTree) (hT : GT.IsTree) (hU : GU.IsTree)
    (hedges : GC.edgeFinset.card + GB.edgeFinset.card + GD.edgeFinset.card +
      GT.edgeFinset.card + GU.edgeFinset.card ≤ 3)
    (hvolume : 0 < -2 / 3 + (rootedTreeGreen GB B 3 - 1 / 3) +
      4 * (rootedTreeGreen GD D 4 - 1 / 4) +
      rootedTreeGreen GT T 3 + rootedTreeGreen GU U 3)
    (hbudget : -2 / 3 + (rootedTreeGreen GB B 3 - 1 / 3) +
      4 * (rootedTreeGreen GD D 4 - 1 / 4) +
      rootedTreeGreen GT T 3 + rootedTreeGreen GU U 3 ≤
      1 / 6 - (rootedTreeGreen GB B 3 - 1 / 3) - 2 * (rootedTreeGreen GD D 4 - 1 / 4))
    (hprojection :
      (-2 / 3 + (rootedTreeGreen GB B 3 - 1 / 3) +
        4 * (rootedTreeGreen GD D 4 - 1 / 4) +
        rootedTreeGreen GT T 3 + rootedTreeGreen GU U 3) *
        (rootedTreeGreen GC C 2 - 5 / 12 +
          (rootedTreeGreen GB B 3 - 1 / 3) + (rootedTreeGreen GD D 4 - 1 / 4)) =
        (1 / 6 - (rootedTreeGreen GB B 3 - 1 / 3) -
          2 * (rootedTreeGreen GD D 4 - 1 / 4))^2) :
    (∃ e : GC ≃g rootedBlockGraph (.arms .point), e C = rootedBlockRoot (.arms .point)) ∧
    (∃ e : GB ≃g rootedBlockGraph (.arms .endEdge), e B = rootedBlockRoot (.arms .endEdge)) ∧
    (∃ e : GD ≃g rootedBlockGraph (.arms .point), e D = rootedBlockRoot (.arms .point)) ∧
    (∃ e : GT ≃g rootedBlockGraph (.arms .point), e T = rootedBlockRoot (.arms .point)) ∧
    (∃ e : GU ≃g rootedBlockGraph (.arms .point), e U = rootedBlockRoot (.arms .point)) := by
  obtain ⟨c, ec, hec⟩ := smallRootedTree_classification hC (by omega) C
  obtain ⟨b, eb, heb⟩ := smallRootedTree_classification hB (by omega) B
  obtain ⟨d, ed, hed⟩ := smallRootedTree_classification hD (by omega) D
  obtain ⟨t, et, het⟩ := smallRootedTree_classification hT (by omega) T
  obtain ⟨u, eu, heu⟩ := smallRootedTree_classification hU (by omega) U
  have hc := rootedTreeGreen_of_iso_at_two_or_ge_three C ec hec 2 (Or.inl rfl)
  have hb := rootedTreeGreen_of_iso_at_two_or_ge_three B eb heb 3 (Or.inr (le_refl 3))
  have hd := rootedTreeGreen_of_iso_at_two_or_ge_three D ed hed 4 (Or.inr (by norm_num))
  have ht := rootedTreeGreen_of_iso_at_two_or_ge_three T et het 3 (Or.inr (le_refl 3))
  have hu := rootedTreeGreen_of_iso_at_two_or_ge_three U eu heu 3 (Or.inr (le_refl 3))
  have hcounts : rootedBlockEdges c + rootedBlockEdges b + rootedBlockEdges d +
      rootedBlockEdges t + rootedBlockEdges u ≤ 3 := by
    simpa only [rootedBlockEdges_eq_of_iso ec, rootedBlockEdges_eq_of_iso eb,
      rootedBlockEdges_eq_of_iso ed, rootedBlockEdges_eq_of_iso et,
      rootedBlockEdges_eq_of_iso eu] using hedges
  rw [hb, hd, ht, hu] at hvolume hbudget
  rw [hc, hb, hd, ht, hu] at hprojection
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
    betaFour_two_extra_rooted_choices c b d t u hcounts hvolume hbudget hprojection
  exact ⟨⟨ec, hec⟩, ⟨eb, heb⟩, ⟨ed, hed⟩, ⟨et, het⟩, ⟨eu, heu⟩⟩

private theorem familyE_five_roots_injective
    {V : Type*} (C B D T U : V)
    (hCB : C ≠ B) (hCD : C ≠ D) (hCT : C ≠ T) (hCU : C ≠ U) (hBD : B ≠ D)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U) :
    Function.Injective (![C, B, D, T, U] : Fin 5 → V) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.cons_val_zero', Matrix.cons_val_succ']

/-- Complete fixed components and all three scalar values in the actual
beta-four two-extra forest. Canonical and single-source component properties
are the preceding separation conclusions. Shape membership, the component
edge budget and all scalar identities are derived here from the actual graph
and its row equation. Neither a root-degree nor core-boundary premise is
needed for this stronger finite classification. -/
theorem beta_four_two_extra_forest_fixed_components
    {V : Type*} [Fintype V] [DecidableEq V]
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
    (hvolume : 0 < -2 + dotProduct (fun i => weight i - 2) coeff)
    (hbudget : -2 + dotProduct (fun i => weight i - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-2 + dotProduct (fun i => weight i - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj D v) ∧
      (∀ v, ¬ G.Adj T v) ∧ (∀ v, ¬ G.Adj U v) ∧
      (∃ M, weight M = 2 ∧ G.Adj B M ∧ G.neighborFinset B = {M} ∧
        G.neighborFinset M = {B} ∧
        ∀ v, G.Reachable B v ↔ v = B ∨ v = M) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 10 ∧
      -2 + dotProduct (fun i => weight i - 2) coeff = 1 / 15 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G weight)⁻¹ *ᵥ threeMarkedSource C B D) = 23 / 20 := by
  have hC : weight C = 2 := hcanonical C (.refl C)
  have hCBne : C ≠ B := by intro h; have hw := congrArg weight h; rw [hC, hB] at hw; norm_num at hw
  have hCDne : C ≠ D := by intro h; have hw := congrArg weight h; rw [hC, hD] at hw; norm_num at hw
  have hCTne : C ≠ T := by intro h; have hw := congrArg weight h; rw [hC, hT] at hw; norm_num at hw
  have hCUne : C ≠ U := by intro h; have hw := congrArg weight h; rw [hC, hU] at hw; norm_num at hw
  have hBDne : B ≠ D := by intro h; have hw := congrArg weight h; rw [hB, hD] at hw; norm_num at hw
  have hCB := graph_single_sources_not_reachable G weight C B hCBne
    (fun v hv _ => hcanonical v hv) (by rw [hB]; norm_num)
  have hCD := graph_single_sources_not_reachable G weight C D hCDne
    (fun v hv _ => hcanonical v hv) (by rw [hD]; norm_num)
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
  obtain ⟨hl, hv, hg⟩ := separated_graph_block_identities G weight coeff C B D {T, U}
    4 hA hrow hB hD (by norm_num) hCB hCD hBD hcanonical hBsingle hDsingle
    hextras hsingle hother'
  simp only [Finset.sum_insert (by simp [hTU] : T ∉ ({U} : Finset V)),
    Finset.sum_singleton] at hv
  norm_num at hl hv hg
  have hinjective := familyE_five_roots_injective C B D T U hCBne hCDne hCTne hCUne
    hBDne hTB hTD hUB hUD hTU
  have hnoncanonical : ∀ i : Fin 5, i ≠ 0 → weight (![C, B, D, T, U] i) ≠ 2 := by
    intro i hi
    fin_cases i <;> norm_num [hC, hB, hD, hT, hU] at hi ⊢
  have hsources : ∀ i : Fin 5, ∀ v,
      G.Reachable (![C, B, D, T, U] i) v → v ≠ ![C, B, D, T, U] i → weight v = 2 := by
    intro i
    fin_cases i
    · simpa using (fun v hv (_ : v ≠ C) => hcanonical v hv)
    · simpa using hBsingle
    · simpa using hDsingle
    · simpa using hTsingle
    · simpa using hUsingle
  have hseparate : ∀ i j : Fin 5, i ≠ j →
      ¬ G.Reachable (![C, B, D, T, U] i) (![C, B, D, T, U] j) := by
    intro i j hij hreach
    by_cases hj : j = 0
    · subst j
      exact hnoncanonical i hij (hcanonical _ hreach.symm)
    · exact hnoncanonical j hj
        (hsources i _ hreach (fun he => hij (hinjective he.symm)))
  have hsum := sum_component_edgeFinset_card_le G (![C, B, D, T, U]) hseparate
  have hedgeBudget :
      (G.induce {v | G.Reachable C v}).edgeFinset.card +
      (G.induce {v | G.Reachable B v}).edgeFinset.card +
      (G.induce {v | G.Reachable D v}).edgeFinset.card +
      (G.induce {v | G.Reachable T v}).edgeFinset.card +
      (G.induce {v | G.Reachable U v}).edgeFinset.card ≤ 3 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum.trans hedges
  have hgreenC := graph_single_root_component_green G weight C 2 hA hC
    (fun v hv _ => hcanonical v hv)
  have hgreenB := graph_single_root_component_green G weight B 3 hA hB hBsingle
  have hgreenD := graph_single_root_component_green G weight D 4 hA hD hDsingle
  have hgreenT := graph_single_root_component_green G weight T 3 hA hT hTsingle
  have hgreenU := graph_single_root_component_green G weight U 3 hA hU hUsingle
  have hchoices := beta_four_two_extra_actual_trees _ _ _ _ _
    ⟨C, SimpleGraph.Reachable.refl C⟩ ⟨B, SimpleGraph.Reachable.refl B⟩
    ⟨D, SimpleGraph.Reachable.refl D⟩ ⟨T, SimpleGraph.Reachable.refl T⟩
    ⟨U, SimpleGraph.Reachable.refl U⟩
    (graph_reachable_component_isTree G C hG)
    (graph_reachable_component_isTree G B hG)
    (graph_reachable_component_isTree G D hG)
    (graph_reachable_component_isTree G T hG)
    (graph_reachable_component_isTree G U hG) hedgeBudget
  obtain ⟨⟨ec, hec⟩, ⟨eb, heb⟩, ⟨ed, hed⟩, ⟨et, het⟩, ⟨eu, heu⟩⟩ :=
    hchoices (by
      rw [hgreenB, hgreenD, hgreenT, hgreenU]
      linarith only [hv, hvolume]) (by
      rw [hgreenB, hgreenD, hgreenT, hgreenU]
      linarith only [hl, hv, hbudget]) (by
      rw [hgreenC, hgreenB, hgreenD, hgreenT, hgreenU]
      rw [hl, hv, hg] at hprojection
      nlinarith only [hprojection])
  have hcval := rootedTreeGreen_of_iso_at_two_or_ge_three
    ⟨C, SimpleGraph.Reachable.refl C⟩ ec hec 2 (Or.inl rfl)
  have hbval := rootedTreeGreen_of_iso_at_two_or_ge_three
    ⟨B, SimpleGraph.Reachable.refl B⟩ eb heb 3 (Or.inr (le_refl 3))
  have hdval := rootedTreeGreen_of_iso_at_two_or_ge_three
    ⟨D, SimpleGraph.Reachable.refl D⟩ ed hed 4 (Or.inr (by norm_num))
  have htval := rootedTreeGreen_of_iso_at_two_or_ge_three
    ⟨T, SimpleGraph.Reachable.refl T⟩ et het 3 (Or.inr (le_refl 3))
  have huval := rootedTreeGreen_of_iso_at_two_or_ge_three
    ⟨U, SimpleGraph.Reachable.refl U⟩ eu heu 3 (Or.inr (le_refl 3))
  rw [hgreenC] at hcval
  rw [hgreenB] at hbval
  rw [hgreenD] at hdval
  rw [hgreenT] at htval
  rw [hgreenU] at huval
  norm_num [familyE_green_point, familyE_green_endEdge_three] at hcval hbval hdval htval huval
  rw [hbval, hdval] at hl
  rw [hbval, hdval, htval, huval] at hv
  rw [hcval, hbval, hdval] at hg
  norm_num at hl hv hg
  obtain ⟨M, hadj, hnB, hnM, hreach⟩ :=
    component_iso_edge_has_mutual_singleton_neighbors G B eb
  exact ⟨component_iso_point_isolated G C ec, component_iso_point_isolated G D ed,
    component_iso_point_isolated G T et, component_iso_point_isolated G U eu,
    ⟨M, hBsingle M hadj.reachable hadj.ne.symm, hadj, hnB, hnM, hreach⟩,
    hl, hv, hg⟩

end KltDP.LinearAlgebra
