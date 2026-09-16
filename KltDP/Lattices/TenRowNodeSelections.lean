import KltDP.Lattices.TenRowPicardExclusions
import KltDP.LinearAlgebra.ABDeterminants
import KltDP.LinearAlgebra.FamilyDSourceReduction
import KltDP.LinearAlgebra.FamilyESourceRows

/-!
# Selecting the actual isolated nodes in the surviving determinant rows

The node index type is the subtype of an actual vertex finset. Its size
comes from the proved complement cardinality in the graph allocation.
The inclusion into the original vertex type is injective by construction.
Weight two, ambient isolation and avoidance of the three marked vertices
produce the full integral node Gram rows through the existing lattice
adapter. The canonical pairings follow from an actual adjunction equation.

The source-facing A statement rejects A1 and forces A2's actual four-node
half-sum. Both the closed and source-facing family-D statements reject both D completions. The E
statement transports the three E2 nodes from the actual induced complement;
the other E rows have nonsquare determinants. No no-even-node theorem or
geometric Picard realization is supplied or assumed as a target premise.

Reuse: pinned/current official Mathlib `Fintype.card_coe`, `Finset.sum_coe_sort`
and induced-graph subtype APIs are sufficient. All determinant, source,
characteristic-parity and actual-index theorems are existing project results.
No source port or dependency change is needed.
-/

namespace KltDP.Lattices.TenRowNodeSelections

open Matrix SimpleGraph KltDP.Codes KltDP.LinearAlgebra
open SmallADEForestLattice TenRowPicardExclusions
open scoped BigOperators

variable {Λ V : Type*} [AddCommGroup Λ] [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem marked_zero (C B D x : V) (hC : x ≠ C) (hB : x ≠ B) (hD : x ≠ D) :
    threeMarkedSource C B D x = (0 : ℚ) := by
  simp [threeMarkedSource, Pi.single_apply, hC, hB, hD, Ne.symm hC, Ne.symm hB, Ne.symm hD]

omit [Fintype V] [DecidableEq V] in
private theorem canonical_pair_zero
    (pairing : LinearMap.BilinForm ℤ Λ) (classes : V → Λ) (weight : V → ℚ) (K : Λ)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = weight x - 2)
    (x : V) (hx : weight x = 2) : pairing K (classes x) = 0 := by
  apply Int.cast_injective (α := ℚ)
  simpa only [hx, sub_self, Int.cast_zero] using hK x

/-- Select the actual finset subtype as the four-node family. The half-sum
is then written back as the sum over that original vertex finset. -/
theorem finset_four_nodes_half
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P : Λ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (C B D : V)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) =
      borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1))
    (hdet : |(borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1)).det| = 576)
    (S : Finset V) (hcard : S.card = 4)
    (hremaining : ∀ x ∈ S, weight x = 2 ∧ ∀ y, ¬ G.Adj x y)
    (havoid : ∀ x ∈ S, x ≠ C ∧ x ≠ B ∧ x ≠ D)
    (K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = weight x - 2) :
    ∃ m : Λ, (2 : ℤ) • m = (∑ x ∈ S, classes x) ∧ pairing m m = -2 ∧ pairing K m = 0 := by
  classical
  let nodes : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hn : Fintype.card S = 4 := (Fintype.card_coe S).trans hcard
  obtain ⟨m, hm, hs, hk⟩ := bordered_graph_determinant576_four_nodes_half
    b pairing hunimod classes P G weight (threeMarkedSource C B D) hGram hdet nodes
    (fun i => (hremaining i.val i.property).2)
    (fun i => (hremaining i.val i.property).1)
    (fun i => marked_zero C B D i.val (havoid i.val i.property).1
      (havoid i.val i.property).2.1 (havoid i.val i.property).2.2)
    K hchar (fun i => canonical_pair_zero pairing classes weight K hK i.val
      (hremaining i.val i.property).1) hn
  change (2 : ℤ) • m = ∑ x : S, classes x.val at hm
  exact ⟨m, hm.trans (Finset.sum_coe_sort S classes), hs, hk⟩

/-- A proved three- or four-element actual isolated vertex finset provides
the node family that excludes the determinant 1296. -/
theorem finset_nodes_determinant1296_impossible
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P : Λ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℚ) (C B D : V)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) =
      borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1))
    (hdet : |(borderedGram (graphWeightMatrix G weight) (threeMarkedSource C B D) (-1)).det| = 1296)
    (S : Finset V) (hcard : S.card = 3 ∨ S.card = 4)
    (hremaining : ∀ x ∈ S, weight x = 2 ∧ ∀ y, ¬ G.Adj x y)
    (havoid : ∀ x ∈ S, x ≠ C ∧ x ≠ B ∧ x ≠ D)
    (K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = weight x - 2) : False := by
  classical
  let nodes : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  exact bordered_graph_determinant1296_impossible
    b pairing hunimod classes P G weight (threeMarkedSource C B D) hGram hdet nodes
    (fun i => (hremaining i.val i.property).2)
    (fun i => (hremaining i.val i.property).1)
    (fun i => marked_zero C B D i.val (havoid i.val i.property).1
      (havoid i.val i.property).2.1 (havoid i.val i.property).2.2)
    K hchar (fun i => canonical_pair_zero pairing classes weight K hK i.val
      (hremaining i.val i.property).1) (by simpa only [Fintype.card_coe] using hcard)

omit [Fintype V] in
private theorem outside_fixed_avoids_marks (fixed : Finset V) (C B D : V)
    (hC : C ∈ fixed) (hB : B ∈ fixed) (hD : D ∈ fixed)
    (x : V) (hx : x ∉ fixed) : x ≠ C ∧ x ≠ B ∧ x ≠ D := by
  exact ⟨fun h => hx (h.symm ▸ hC), fun h => hx (h.symm ▸ hB), fun h => hx (h.symm ▸ hD)⟩

/-- The actual adjacent-extra source branch admits only A2 in a unimodular
integral embedding, and its actual four leftover vertices have a total
integral half-sum. Their cardinality and isolation come from allocation. -/
theorem familyA_source_four_node_half
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (coeff : V → ℚ) (C B D T : V) (hcard : Fintype.card V = 10)
    (hweight : ∀ i, 2 ≤ weight i) (hC : weight C = 2)
    (hB : weight B = 3) (hD : weight D = 3) (hT : weight T = 3)
    (hTB : T ≠ B) (hTD : T ≠ D)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → weight i = 2)
    (hseparate : ¬ G.Reachable B D) (hCT : G.Adj C T)
    (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : ℚ))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : ℚ)) *ᵥ coeff =
      fun i => (weight i : ℚ) - 2)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hell : 0 < 1 - coeff C - coeff B - coeff D)
    (hv : -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (fun i => (weight i : ℚ)) x - 2)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
        (threeMarkedSource C B D) (-1)) :
    ∃ S : Finset V, S.card = 4 ∧
      (∀ x ∈ S, weight x = 2 ∧ ∀ y, ¬ G.Adj x y) ∧
      ∃ m : Λ, (2 : ℤ) • m = (∑ x ∈ S, classes x) ∧ pairing m m = -2 ∧ pairing K m = 0 := by
  classical
  rcases beta_three_adjacent_extra_determinants (𝕜 := ℚ) G weight coeff C B D T hcard
    hweight hC hB hD hT hTB hTD hother hseparate hCT hedges hA hrow hcoeff hell hv with
    ⟨_, _, _, _, hb⟩ | ⟨u, v, _, _, _, _, _, _, hc, hremaining, _, hb⟩
  · exact False.elim (bordered_graph_nonsquare_rows_impossible b pairing hunimod classes P G
      (fun i => (weight i : ℚ)) (threeMarkedSource C B D) hGram
      (Or.inl (by rw [hb]; norm_num)))
  · let fixed : Finset V := {u, v, C, T, B, D}
    let S := Finset.univ \ fixed
    have hrem : ∀ x ∈ S, (weight x : ℚ) = 2 ∧ ∀ y, ¬ G.Adj x y := by
      intro x hx
      obtain ⟨hw, hi⟩ := hremaining x hx
      exact ⟨by simp only [hw, Nat.cast_ofNat], hi⟩
    have havoid : ∀ x ∈ S, x ≠ C ∧ x ≠ B ∧ x ≠ D := by
      intro x hx
      exact outside_fixed_avoids_marks fixed C B D (by simp [fixed]) (by simp [fixed])
        (by simp [fixed]) x (Finset.mem_sdiff.mp hx).2
    refine ⟨S, hc, hremaining, ?_⟩
    exact finset_four_nodes_half b pairing hunimod classes P G (fun i => (weight i : ℚ))
      C B D hGram (by rw [hb]; norm_num) S hc hrem havoid K hchar hK

/-- The actual closed family-D graph data yield D1's four actual nodes or
D2's nonsquare determinant; both contradict the integral lattice embedding.
The displayed Green input is the actual matrix value of this family branch. -/
theorem closed_familyD_lattice_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ)
    (C M B D T U : V) (hcard : Fintype.card V = 10)
    (hC : weight C = 2) (hM : weight M = 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hBD : B ≠ D) (hTB : T ≠ B) (hTD : T ≠ D)
    (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCM : G.Adj C M)
    (hnC : G.neighborFinset C = {M}) (hnM : G.neighborFinset M = {C})
    (hBiso : ∀ v, ¬ G.Adj B v) (hDiso : ∀ v, ¬ G.Adj D v)
    (hTiso : ∀ v, ¬ G.Adj T v) (hUiso : ∀ v, ¬ G.Adj U v)
    (hedges : G.edgeFinset.card ≤ 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2)
    (hA : IsUnit (graphWeightMatrix G (fun i => (weight i : ℚ))))
    (hg : dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
        threeMarkedSource C B D) = (4 : ℚ) / 3)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (fun i => (weight i : ℚ)) x - 2)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
        (threeMarkedSource C B D) (-1)) : False := by
  classical
  rcases familyD_determinants (𝕜 := ℚ) G weight C M B D T U hcard hC hM hB hD hT hU
    hBD hTB hTD hUB hUD hTU hCM hnC hnM hBiso hDiso hTiso hUiso hedges hother hA hg with
    ⟨_, hc, hremaining, _, hb⟩ | ⟨x, y, _, _, _, _, _, _, _, _, _, hb⟩
  · let fixed : Finset V := {C, M, B, D, T, U}
    let S := Finset.univ \ fixed
    have hrem : ∀ x ∈ S, (weight x : ℚ) = 2 ∧ ∀ y, ¬ G.Adj x y := by
      intro x hx
      obtain ⟨hw, hi⟩ := hremaining x hx
      exact ⟨by simp only [hw, Nat.cast_ofNat], hi⟩
    have havoid : ∀ x ∈ S, x ≠ C ∧ x ≠ B ∧ x ≠ D := by
      intro x hx
      exact outside_fixed_avoids_marks fixed C B D (by simp [fixed]) (by simp [fixed])
        (by simp [fixed]) x (Finset.mem_sdiff.mp hx).2
    exact finset_nodes_determinant1296_impossible b pairing hunimod classes P G
      (fun i => (weight i : ℚ)) C B D hGram (by rw [hb]; norm_num)
      S (Or.inr hc) hrem havoid K hchar hK
  · exact bordered_graph_nonsquare_rows_impossible b pairing hunimod classes P G
      (fun i => (weight i : ℚ)) (threeMarkedSource C B D) hGram
      (Or.inr (Or.inr (Or.inl (by rw [hb]; norm_num))))

/-- The actual D source row, budget and projection equations supply the
closed canonical edge, heavy-vertex isolation and Green value used above.
Thus this exclusion has no prescribed determinant, node family or energy
among its hypotheses. The integral realization and characteristic pairing
are explicit algebraic inputs. -/
theorem familyD_source_lattice_impossible
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D T U : V) (hcard : Fintype.card V = 10)
    (hG : G.IsAcyclic) (hedges : G.edgeFinset.card ≤ 2)
    (hA : (graphWeightMatrix G (fun i => (weight i : ℚ))).PosDef)
    (hrow : graphWeightMatrix G (fun i => (weight i : ℚ)) *ᵥ coeff =
      fun i => (weight i : ℚ) - 2)
    (hB : weight B = 3) (hD : weight D = 3)
    (hT : weight T = 3) (hU : weight U = 3)
    (hTB : T ≠ B) (hTD : T ≠ D) (hUB : U ≠ B) (hUD : U ≠ D) (hTU : T ≠ U)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (hBD : ¬ G.Reachable B D)
    (hcanonical : ∀ i, G.Reachable C i → weight i = 2)
    (hBsingle : ∀ i, G.Reachable B i → i ≠ B → weight i = 2)
    (hDsingle : ∀ i, G.Reachable D i → i ≠ D → weight i = 2)
    (hTsingle : ∀ i, G.Reachable T i → i ≠ T → weight i = 2)
    (hUsingle : ∀ i, G.Reachable U i → i ≠ U → weight i = 2)
    (hother : ∀ i, i ≠ B → i ≠ D → i ≠ T → i ≠ U → weight i = 2)
    (hbudget : -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (-1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = (fun i => (weight i : ℚ)) x - 2)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
        (threeMarkedSource C B D) (-1)) : False := by
  classical
  let w : V → ℚ := fun i => weight i
  have hcanonical' : ∀ i, G.Reachable C i → w i = 2 := by
    intro i hi
    simp only [w, hcanonical i hi, Nat.cast_ofNat]
  obtain ⟨hBi, hDi, hTi, hUi, hell, hvol, hgreen⟩ :=
    beta_three_two_extra_source_rigidity G w coeff C B D T U hA hrow
      (by simp only [w, hB, Nat.cast_ofNat]) (by simp only [w, hD, Nat.cast_ofNat])
      (by simp only [w, hT, Nat.cast_ofNat]) (by simp only [w, hU, Nat.cast_ofNat])
      hTB hTD hUB hUD hTU hCB hCD hBD hcanonical'
      (by intro i hi hne; simp only [w, hBsingle i hi hne, Nat.cast_ofNat])
      (by intro i hi hne; simp only [w, hDsingle i hi hne, Nat.cast_ofNat])
      (by intro i hi hne; simp only [w, hTsingle i hi hne, Nat.cast_ofNat])
      (by intro i hi hne; simp only [w, hUsingle i hi hne, Nat.cast_ofNat])
      (by intro i hiB hiD hiT hiU; simp only [w, hother i hiB hiD hiT hiU, Nat.cast_ofNat])
      hbudget hprojection
  obtain ⟨M, hCM, hC, hM, hnC, hnM, _⟩ :=
    graph_canonical_green_two_thirds_closed_edge G w C (isUnit_of_posDef hA)
      hG (by omega) hcanonical' hgreen
  have hg : dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G w)⁻¹ *ᵥ threeMarkedSource C B D) = 4 / 3 := by
    rw [hell, hvol] at hprojection
    nlinarith only [hprojection]
  have hneBD : B ≠ D := by
    intro h
    subst D
    exact hBD (SimpleGraph.Reachable.refl B)
  exact closed_familyD_lattice_impossible G weight C M B D T U hcard
    (by change (weight C : ℚ) = 2 at hC; exact_mod_cast hC)
    (by change (weight M : ℚ) = 2 at hM; exact_mod_cast hM) hB hD hT hU
    hneBD hTB hTD hUB hUD hTU hCM hnC hnM hBi hDi hTi hUi hedges hother
    (isUnit_of_posDef hA) hg b pairing hunimod classes P K hchar hK hGram

/-- All four E source completions contradict an actual unimodular integral
embedding. E2's three nodes are selected in the actual induced complement
and proved isolated in the ambient graph; the other determinants are nonsquares. -/
theorem familyE_source_lattice_impossible
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
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2)
    (b : Basis (V ⊕ Unit) ℤ Λ) (pairing : LinearMap.BilinForm ℤ Λ)
    (hunimod : (BilinForm.toMatrix b pairing).det.natAbs = 1)
    (classes : V → Λ) (P K : Λ) (hchar : IsCharacteristic pairing K)
    (hK : ∀ x, (pairing K (classes x) : ℚ) = weight x - 2)
    (hGram : (familyGram pairing (Sum.elim classes (fun _ : Unit => P))).map
      (fun z => (z : ℚ)) = borderedGram (graphWeightMatrix G weight)
        (threeMarkedSource C B D) (-1)) : False := by
  classical
  obtain ⟨M, _, _, hnB, hnM, _, hCiso, hDiso, hTiso, hUiso, _, _, _, hremaining⟩ :=
    familyE_source_rows G weight coeff C B D T U hcard hA hG hrow hedges hB hD hT hU
      hTB hTD hUB hUD hTU hcanonical hBsingle hDsingle hTsingle hUsingle hother
      hvolume hbudget hprojection
  let fixed : Finset V := {C, B, M, D, T, U}
  let Z := G.induce {v | v ∉ fixed}
  obtain ⟨_, _, hZweights, _, hrows⟩ := hremaining
  rcases hrows with ⟨_, _, hb⟩ | ⟨x, y, _, _, hout, hiso, _, hb⟩ |
    ⟨x, y, z, _, _, _, _, _, _, _, hb⟩ |
    ⟨x, y, z, w, _, _, _, _, _, _, _, _, _, _, hb⟩
  · exact bordered_graph_nonsquare_rows_impossible b pairing hunimod classes P G weight
      (threeMarkedSource C B D) hGram
      (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hb]; norm_num)))))
  · let S : Finset {v | v ∉ fixed} := Finset.univ \ {x, y}
    let nodes : S ↪ V :=
      ⟨fun i => i.val.val, fun i j h => Subtype.ext (Subtype.ext h)⟩
    have hnodesCard : Fintype.card S = 3 := (Fintype.card_coe S).trans hout
    have hnodesIso : ∀ i : S, ∀ j, ¬ G.Adj (nodes i) j := by
      intro i j hadj
      have hi : i.val.val ∉ fixed := i.val.property
      by_cases hj : j ∈ fixed
      · simp only [fixed, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with hj | hj | hj | hj | hj | hj
        · subst j
          exact hCiso _ hadj.symm
        · subst j
          have hm := (G.mem_neighborFinset B i.val.val).mpr hadj.symm
          rw [hnB, Finset.mem_singleton] at hm
          exact hi (by simp [fixed, hm])
        · subst j
          have hm := (G.mem_neighborFinset M i.val.val).mpr hadj.symm
          rw [hnM, Finset.mem_singleton] at hm
          exact hi (by simp [fixed, hm])
        · subst j
          exact hDiso _ hadj.symm
        · subst j
          exact hTiso _ hadj.symm
        · subst j
          exact hUiso _ hadj.symm
      · exact hiso i.val (Finset.mem_sdiff.mp i.property).2 ⟨j, hj⟩ hadj
    have hnodesWeight : ∀ i : S, weight (nodes i) = 2 := fun i => hZweights i.val
    have hnodesContact : ∀ i : S, threeMarkedSource C B D (nodes i) = (0 : ℚ) := by
      intro i
      have hn := outside_fixed_avoids_marks fixed C B D (by simp [fixed])
        (by simp [fixed]) (by simp [fixed]) i.val.val i.val.property
      exact marked_zero C B D _ hn.1 hn.2.1 hn.2.2
    exact bordered_graph_determinant1296_impossible b pairing hunimod classes P G weight
      (threeMarkedSource C B D) hGram (by rw [hb]; norm_num) nodes hnodesIso hnodesWeight
      hnodesContact K hchar
      (fun i => canonical_pair_zero pairing classes weight K hK (nodes i) (hnodesWeight i))
      (Or.inl hnodesCard)
  · exact bordered_graph_nonsquare_rows_impossible b pairing hunimod classes P G weight
      (threeMarkedSource C B D) hGram
      (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hb]; norm_num)))))
  · exact bordered_graph_nonsquare_rows_impossible b pairing hunimod classes P G weight
      (threeMarkedSource C B D) hGram
      (Or.inr (Or.inr (Or.inl (by rw [hb]; norm_num))))

end KltDP.Lattices.TenRowNodeSelections
