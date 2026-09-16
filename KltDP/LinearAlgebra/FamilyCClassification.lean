import KltDP.LinearAlgebra.RootedTreeBudgets
import KltDP.LinearAlgebra.SeparatedBlockScalars
import KltDP.LinearAlgebra.CanonicalGreenClosedEdge
import KltDP.LinearAlgebra.GraphComponentEdgeBudget
import KltDP.LinearAlgebra.SingleExtraAllocation

/-!
# The four rooted components in family C

The beta-three, one-extra scalar identity from manuscript Lemma 9.2 has
exactly one solution among four actual rooted tree components sharing at
most two edges. The canonical component is a point; each distinguished
weight-three component is an edge rooted at its weight-three vertex; and
the extra weight-three component is a point.

The arbitrary-tree theorem derives the four shape choices and their inverse
entries from graph isomorphisms. It does not assume membership in family C.
The total edge budget refers to the actual four graphs. Transporting that
budget and the scalar identity from a larger weighted forest is a separate
adapter obligation; the scalar identity itself is derived in
`SeparatedBlockScalars` from the projection identity.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

/-- The two-edge bound leaves four of the eight proved rooted shapes. -/
theorem rootedBlock_two_edge_cases (choice : RootedBlockChoice)
    (hedges : rootedBlockEdges choice ≤ 2) :
    choice = .arms .point ∨ choice = .arms .endEdge ∨
      choice = .arms .endTwo ∨ choice = .arms .middleTwo := by
  cases choice with
  | arms shape =>
    cases shape <;>
      norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ] at hedges ⊢
  | leafStar => norm_num [rootedBlockEdges] at hedges

set_option maxHeartbeats 2000000 in
/-- Exact shape allocation for the beta-three, one-extra scalar identity.
All entries are the already proved rational formulas for actual matrices.
Neither positivity nor the core-boundary condition is required at this step. -/
theorem beta_three_one_extra_rooted_choices
    (canonical left right extra : RootedBlockChoice)
    (hbudget : rootedBlockEdges canonical + rootedBlockEdges left +
      rootedBlockEdges right + rootedBlockEdges extra ≤ 2)
    (hidentity :
      (rootedBlockGreen left 3 + rootedBlockGreen right 3 - 2 / 3) *
          (rootedBlockGreen canonical 2 + 1 / 3) +
        (rootedBlockGreen extra 3 - 1 / 3) *
          (rootedBlockGreen canonical 2 - 1 / 3 +
            (rootedBlockGreen left 3 + rootedBlockGreen right 3 - 2 / 3)) = 1 / 9) :
    canonical = .arms .point ∧ left = .arms .endEdge ∧
      right = .arms .endEdge ∧ extra = .arms .point := by
  have hc : rootedBlockEdges canonical ≤ 2 := by omega
  have hl : rootedBlockEdges left ≤ 2 := by omega
  have hr : rootedBlockEdges right ≤ 2 := by omega
  have ht : rootedBlockEdges extra ≤ 2 := by omega
  rcases rootedBlock_two_edge_cases canonical hc with rfl | rfl | rfl | rfl <;>
    rcases rootedBlock_two_edge_cases left hl with rfl | rfl | rfl | rfl <;>
    rcases rootedBlock_two_edge_cases right hr with rfl | rfl | rfl | rfl <;>
    rcases rootedBlock_two_edge_cases extra ht with rfl | rfl | rfl | rfl <;>
    norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
      rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator] at hbudget hidentity ⊢

private theorem familyC_green_two_of_iso
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (root : V)
    {choice : RootedBlockChoice} (e : G ≃g rootedBlockGraph choice)
    (hroot : e root = rootedBlockRoot choice) :
    rootedTreeGreen G root 2 = rootedBlockGreen choice 2 := by
  change (rootedGraphMatrix G root (2 : ℚ))⁻¹ root root = _
  rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot (2 : ℚ),
    ← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root_two]

private theorem familyC_green_three_of_iso
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (root : V)
    {choice : RootedBlockChoice} (e : G ≃g rootedBlockGraph choice)
    (hroot : e root = rootedBlockRoot choice) :
    rootedTreeGreen G root 3 = rootedBlockGreen choice 3 := by
  change (rootedGraphMatrix G root (3 : ℚ))⁻¹ root root = _
  rw [rootedGraphMatrix_inverse_root_eq e root (rootedBlockRoot choice) hroot (3 : ℚ),
    ← rootedBlockMatrixAt_eq_graph, rootedBlockMatrixAt_inverse_root choice (le_refl 3)]

/-- The unique allocation, for arbitrary actual rooted trees. The conclusion
contains root-preserving graph isomorphisms, and thus specifies the component
shapes themselves rather than only their inverse entries. -/
theorem beta_three_one_extra_actual_trees
    {VC VB VD VT : Type*}
    [Fintype VC] [Fintype VB] [Fintype VD] [Fintype VT]
    [DecidableEq VC] [DecidableEq VB] [DecidableEq VD] [DecidableEq VT]
    (GC : SimpleGraph VC) (GB : SimpleGraph VB)
    (GD : SimpleGraph VD) (GT : SimpleGraph VT)
    [DecidableRel GC.Adj] [DecidableRel GB.Adj]
    [DecidableRel GD.Adj] [DecidableRel GT.Adj]
    (C : VC) (B : VB) (D : VD) (T : VT)
    (hC : GC.IsTree) (hB : GB.IsTree) (hD : GD.IsTree) (hT : GT.IsTree)
    (hbudget : GC.edgeFinset.card + GB.edgeFinset.card +
      GD.edgeFinset.card + GT.edgeFinset.card ≤ 2)
    (hidentity :
      (rootedTreeGreen GB B 3 + rootedTreeGreen GD D 3 - 2 / 3) *
          (rootedTreeGreen GC C 2 + 1 / 3) +
        (rootedTreeGreen GT T 3 - 1 / 3) *
          (rootedTreeGreen GC C 2 - 1 / 3 +
            (rootedTreeGreen GB B 3 + rootedTreeGreen GD D 3 - 2 / 3)) = 1 / 9) :
    (∃ e : GC ≃g rootedBlockGraph (.arms .point),
      e C = rootedBlockRoot (.arms .point)) ∧
    (∃ e : GB ≃g rootedBlockGraph (.arms .endEdge),
      e B = rootedBlockRoot (.arms .endEdge)) ∧
    (∃ e : GD ≃g rootedBlockGraph (.arms .endEdge),
      e D = rootedBlockRoot (.arms .endEdge)) ∧
    (∃ e : GT ≃g rootedBlockGraph (.arms .point),
      e T = rootedBlockRoot (.arms .point)) := by
  obtain ⟨c, ec, hec⟩ := smallRootedTree_classification hC (by omega) C
  obtain ⟨b, eb, heb⟩ := smallRootedTree_classification hB (by omega) B
  obtain ⟨d, ed, hed⟩ := smallRootedTree_classification hD (by omega) D
  obtain ⟨t, et, het⟩ := smallRootedTree_classification hT (by omega) T
  have hc := familyC_green_two_of_iso C ec hec
  have hb := familyC_green_three_of_iso B eb heb
  have hd := familyC_green_three_of_iso D ed hed
  have ht := familyC_green_three_of_iso T et het
  have hcounts : rootedBlockEdges c + rootedBlockEdges b +
      rootedBlockEdges d + rootedBlockEdges t ≤ 2 := by
    simpa only [rootedBlockEdges_eq_of_iso ec, rootedBlockEdges_eq_of_iso eb,
      rootedBlockEdges_eq_of_iso ed, rootedBlockEdges_eq_of_iso et] using hbudget
  rw [hc, hb, hd, ht] at hidentity
  obtain ⟨hc', hb', hd', ht'⟩ :=
    beta_three_one_extra_rooted_choices c b d t hcounts hidentity
  subst c
  subst b
  subst d
  subst t
  exact ⟨⟨ec, hec⟩, ⟨eb, heb⟩, ⟨ed, hed⟩, ⟨et, het⟩⟩

/-- The admitted four shapes really satisfy both the two-edge budget and
the scalar identity. This is the converse arithmetic witness; the existing
rooted-tree realization theorem supplies their actual positive definiteness. -/
theorem familyC_listed_identity :
    rootedBlockEdges (.arms .point) + rootedBlockEdges (.arms .endEdge) +
        rootedBlockEdges (.arms .endEdge) + rootedBlockEdges (.arms .point) = 2 ∧
      (rootedBlockGreen (.arms .endEdge) 3 + rootedBlockGreen (.arms .endEdge) 3 - 2 / 3) *
          (rootedBlockGreen (.arms .point) 2 + 1 / 3) +
        (rootedBlockGreen (.arms .point) 3 - 1 / 3) *
          (rootedBlockGreen (.arms .point) 2 - 1 / 3 +
            (rootedBlockGreen (.arms .endEdge) 3 +
              rootedBlockGreen (.arms .endEdge) 3 - 2 / 3)) = 1 / 9 := by
  norm_num [rootedBlockEdges, rootedArmLengths, Fin.sum_univ_succ,
    rootedBlockGreen, rootedArmGreenNumerator, rootedArmDenominator]

/-- An actual component with one possible noncanonical weight has the
rooted-matrix Green entry used in the four-tree theorem. The equality is
proved by restricting the full inverse to the actual component. -/
theorem graph_single_root_component_green
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (root : V) [DecidablePred (G.Reachable root)] (b : ℚ)
    (hA : IsUnit (graphWeightMatrix G weight)) (hroot : weight root = b)
    (hother : ∀ v, G.Reachable root v → v ≠ root → weight v = 2) :
    rootedTreeGreen (G.induce {v | G.Reachable root v})
        ⟨root, SimpleGraph.Reachable.refl root⟩ b =
      (graphWeightMatrix G weight)⁻¹ root root := by
  classical
  let root' : {v | G.Reachable root v} := ⟨root, SimpleGraph.Reachable.refl root⟩
  have hweight (v : {v | G.Reachable root v}) :
      weight v.val = if v = root' then b else 2 := by
    by_cases hv : v = root'
    · subst v
      simpa only [root', if_pos rfl] using hroot
    · have hv' : v.val ≠ root := by
        intro h
        exact hv (Subtype.ext h)
      rw [if_neg hv, hother v.val v.property hv']
  have hmatrix : graphWeightMatrix (G.induce {v | G.Reachable root v})
      (fun v => weight v.val) =
      rootedGraphMatrix (G.induce {v | G.Reachable root v}) root' b := by
    ext i j
    simp only [graphWeightMatrix_apply, rootedGraphMatrix, hweight]
  have hentry := congrArg (fun M => M root' root')
    (graph_component_inverse_eq G weight root hA)
  rw [hmatrix] at hentry
  exact hentry

/-- The arbitrary-tree result applied to actual reachable components of
one weighted forest. The edge budget is the sum of those actual component
edge cardinalities; no component shape is an input. -/
theorem beta_three_one_extra_forest_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B D T : V)
    [DecidablePred (G.Reachable C)] [DecidablePred (G.Reachable B)]
    [DecidablePred (G.Reachable D)] [DecidablePred (G.Reachable T)]
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hC : ∀ v, G.Reachable C v → weight v = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hbudget :
      (G.induce {v | G.Reachable C v}).edgeFinset.card +
      (G.induce {v | G.Reachable B v}).edgeFinset.card +
      (G.induce {v | G.Reachable D v}).edgeFinset.card +
      (G.induce {v | G.Reachable T v}).edgeFinset.card ≤ 2)
    (hidentity :
      ((graphWeightMatrix G weight)⁻¹ B B + (graphWeightMatrix G weight)⁻¹ D D - 2 / 3) *
          ((graphWeightMatrix G weight)⁻¹ C C + 1 / 3) +
        ((graphWeightMatrix G weight)⁻¹ T T - 1 / 3) *
          ((graphWeightMatrix G weight)⁻¹ C C - 1 / 3 +
            ((graphWeightMatrix G weight)⁻¹ B B +
              (graphWeightMatrix G weight)⁻¹ D D - 2 / 3)) = 1 / 9) :
    (∃ e : G.induce {v | G.Reachable C v} ≃g rootedBlockGraph (.arms .point),
      e ⟨C, SimpleGraph.Reachable.refl C⟩ = rootedBlockRoot (.arms .point)) ∧
    (∃ e : G.induce {v | G.Reachable B v} ≃g rootedBlockGraph (.arms .endEdge),
      e ⟨B, SimpleGraph.Reachable.refl B⟩ = rootedBlockRoot (.arms .endEdge)) ∧
    (∃ e : G.induce {v | G.Reachable D v} ≃g rootedBlockGraph (.arms .endEdge),
      e ⟨D, SimpleGraph.Reachable.refl D⟩ = rootedBlockRoot (.arms .endEdge)) ∧
    (∃ e : G.induce {v | G.Reachable T v} ≃g rootedBlockGraph (.arms .point),
      e ⟨T, SimpleGraph.Reachable.refl T⟩ = rootedBlockRoot (.arms .point)) := by
  apply beta_three_one_extra_actual_trees _ _ _ _
    ⟨C, SimpleGraph.Reachable.refl C⟩ ⟨B, SimpleGraph.Reachable.refl B⟩
    ⟨D, SimpleGraph.Reachable.refl D⟩ ⟨T, SimpleGraph.Reachable.refl T⟩
    (graph_reachable_component_isTree G C hG)
    (graph_reachable_component_isTree G B hG)
    (graph_reachable_component_isTree G D hG)
    (graph_reachable_component_isTree G T hG) hbudget
  rw [graph_single_root_component_green G weight C 2 hA
      (hC C (SimpleGraph.Reachable.refl C)) (fun v hv _ => hC v hv),
    graph_single_root_component_green G weight B 3 hA hB hBsingle,
    graph_single_root_component_green G weight D 3 hA hD hDsingle,
    graph_single_root_component_green G weight T 3 hA hT hTsingle]
  exact hidentity

/-- A component isomorphic to the single-vertex graph is isolated in the
ambient graph. This uses actual degree transport and component closure. -/
theorem component_iso_point_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V)
    [DecidablePred (G.Reachable root)]
    (e : G.induce {v | G.Reachable root v} ≃g rootedBlockGraph (.arms .point)) :
    ∀ v, ¬ G.Adj root v := by
  classical
  have hlisted : ∀ v, (rootedBlockGraph (.arms .point)).degree v = 0 := by decide
  have hinside : (G.induce {v | G.Reachable root v}).degree
      ⟨root, SimpleGraph.Reachable.refl root⟩ = 0 := by
    calc
      _ = (rootedBlockGraph (.arms .point)).degree
          (e ⟨root, SimpleGraph.Reachable.refl root⟩) := by
        simpa only [SimpleGraph.card_neighborSet_eq_degree] using
          Fintype.card_congr (e.mapNeighborSet ⟨root, SimpleGraph.Reachable.refl root⟩)
      _ = 0 := hlisted _
  have hneighbors : G.neighborSet root ⊆ {v | G.Reachable root v} := by
    intro v hv
    exact hv.reachable
  have hdegree : G.degree root = 0 :=
    (G.degree_induce_of_neighborSet_subset
      (v := ⟨root, SimpleGraph.Reachable.refl root⟩) hneighbors).symm.trans hinside
  have hempty : G.neighborFinset root = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree
  intro v hv
  have hmem := (G.mem_neighborFinset root v).mpr hv
  simpa only [hempty, Finset.not_mem_empty] using hmem

/-- Family C's actual fixed components, derived from a global two-edge
bound. Pairwise nonreachability refers to the four actual distinguished
roots, and the component edge budget is proved from that separation. -/
theorem beta_three_one_extra_forest_fixed_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G.Reachable]
    (weight : V → ℚ) (C B D T : V)
    (hA : IsUnit (graphWeightMatrix G weight)) (hG : G.IsAcyclic)
    (hC : ∀ v, G.Reachable C v → weight v = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hBsingle : ∀ v, G.Reachable B v → v ≠ B → weight v = 2)
    (hDsingle : ∀ v, G.Reachable D v → v ≠ D → weight v = 2)
    (hTsingle : ∀ v, G.Reachable T v → v ≠ T → weight v = 2)
    (hseparate : ∀ i j : Fin 4, i ≠ j →
      ¬ G.Reachable (![C, B, D, T] i) (![C, B, D, T] j))
    (hedges : G.edgeFinset.card ≤ 2)
    (hidentity :
      ((graphWeightMatrix G weight)⁻¹ B B + (graphWeightMatrix G weight)⁻¹ D D - 2 / 3) *
          ((graphWeightMatrix G weight)⁻¹ C C + 1 / 3) +
        ((graphWeightMatrix G weight)⁻¹ T T - 1 / 3) *
          ((graphWeightMatrix G weight)⁻¹ C C - 1 / 3 +
            ((graphWeightMatrix G weight)⁻¹ B B +
              (graphWeightMatrix G weight)⁻¹ D D - 2 / 3)) = 1 / 9) :
    (∀ v, ¬ G.Adj C v) ∧ (∀ v, ¬ G.Adj T v) ∧
      ∃ L M, weight L = 2 ∧ weight M = 2 ∧ G.Adj B L ∧ G.Adj D M ∧
        G.neighborFinset B = {L} ∧ G.neighborFinset L = {B} ∧
        G.neighborFinset D = {M} ∧ G.neighborFinset M = {D} ∧
        (∀ v, G.Reachable B v ↔ v = B ∨ v = L) ∧
        (∀ v, G.Reachable D v ↔ v = D ∨ v = M) := by
  have hsum := sum_component_edgeFinset_card_le G (![C, B, D, T]) hseparate
  have hbudget :
      (G.induce {v | G.Reachable C v}).edgeFinset.card +
      (G.induce {v | G.Reachable B v}).edgeFinset.card +
      (G.induce {v | G.Reachable D v}).edgeFinset.card +
      (G.induce {v | G.Reachable T v}).edgeFinset.card ≤ 2 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum.trans hedges
  obtain ⟨⟨ec, _⟩, ⟨eb, _⟩, ⟨ed, _⟩, ⟨et, _⟩⟩ :=
    beta_three_one_extra_forest_components G weight C B D T hA hG hC hB hD hT
      hBsingle hDsingle hTsingle hbudget hidentity
  obtain ⟨L, hBL, hnB, hnL, hrB⟩ :=
    component_iso_edge_has_mutual_singleton_neighbors G B eb
  obtain ⟨M, hDM, hnD, hnM, hrD⟩ :=
    component_iso_edge_has_mutual_singleton_neighbors G D ed
  exact ⟨component_iso_point_isolated G C ec, component_iso_point_isolated G T et,
    L, M, hBsingle L hBL.reachable (Ne.symm hBL.ne),
    hDsingle M hDM.reachable (Ne.symm hDM.ne), hBL, hDM, hnB, hnL, hnD, hnM, hrB, hrD⟩

/-- The two fixed family-C edges exhaust the global edge budget. On the
source's ten actual vertices the complement of the six fixed vertices is
therefore exactly four isolated canonical vertices. -/
theorem familyC_remaining_vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ)
    (C B L D M T : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hL : weight L = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hCiso : ∀ v, ¬ G.Adj C v) (hTiso : ∀ v, ¬ G.Adj T v)
    (hBL : G.Adj B L) (hDM : G.Adj D M)
    (hseparate : ¬ G.Reachable B D) (hedges : G.edgeFinset.card ≤ 2)
    (hother : ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2) :
    G.edgeFinset = {s(B, L), s(D, M)} ∧
      (Finset.univ \ ({C, B, L, D, M, T} : Finset V)).card = 4 ∧
      ∀ v ∈ Finset.univ \ ({C, B, L, D, M, T} : Finset V),
        weight v = 2 ∧ ∀ w, ¬ G.Adj v w := by
  have h23 (v w : V) (hv : weight v = 2) (hw : weight w = 3) : v ≠ w := by
    intro h
    have hweight := congrArg weight h
    linarith
  have hCB := h23 C B hC hB
  have hCD := h23 C D hC hD
  have hCT := h23 C T hC hT
  have hLD := h23 L D hL hD
  have hLT := h23 L T hL hT
  have hMB := h23 M B hM hB
  have hMT := h23 M T hM hT
  have hCL : C ≠ L := by intro h; subst L; exact hCiso B hBL.symm
  have hCM : C ≠ M := by intro h; subst M; exact hCiso D hDM.symm
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  have hBT : B ≠ T := by intro h; subst T; exact hTiso L hBL
  have hDT : D ≠ T := by intro h; subst T; exact hTiso M hDM
  have hLM : L ≠ M := by
    intro h
    subst M
    exact hseparate (hBL.reachable.trans hDM.reachable.symm)
  have hfixed : ({C, B, L, D, M, T} : Finset V).card = 6 := by
    simp [hCB, hCL, hCD, hCM, hCT, hBL.ne, hBD, Ne.symm hMB,
      hBT, hLD, hLM, hLT, hDM.ne, hDT, hMT]
  have hpair : s(B, L) ≠ s(D, M) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hBD h.1
    · exact hMB h.1.symm
  have hfirst : s(B, L) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hBL
  have hsecond : s(D, M) ∈ G.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hDM
  have hsubset : ({s(B, L), s(D, M)} : Finset (Sym2 V)) ⊆ G.edgeFinset :=
    Finset.insert_subset_iff.mpr ⟨hfirst, Finset.singleton_subset_iff.mpr hsecond⟩
  have hpaircard : ({s(B, L), s(D, M)} : Finset (Sym2 V)).card = 2 := by simp [hpair]
  have heq : G.edgeFinset = {s(B, L), s(D, M)} :=
    (Finset.eq_of_subset_of_card_le hsubset (by rw [hpaircard]; exact hedges)).symm
  refine ⟨heq, ?_, ?_⟩
  · rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, hcard, hfixed]
  · intro v hv
    have hout := (Finset.mem_sdiff.mp hv).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hout
    exact ⟨hother v hout.2.1 hout.2.2.2.1 hout.2.2.2.2.2,
      no_adj_outside_pair_edges G B L D M heq v
        hout.2.1 hout.2.2.1 hout.2.2.2.1 hout.2.2.2.2.1⟩

end KltDP.LinearAlgebra
