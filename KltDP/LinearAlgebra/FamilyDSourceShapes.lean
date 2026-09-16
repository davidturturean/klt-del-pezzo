import KltDP.LinearAlgebra.SeparatedBlockScalars
import KltDP.LinearAlgebra.CanonicalGreenClosedEdge
import KltDP.LinearAlgebra.FamilyDDeterminants

/-!
# The complete family-D graph rows from the source equations

This composition retains the actual canonical neighbor of C, its entire
component, all four isolated higher-weight vertices, and the full graph
allocation along with the source values and both actual determinants.
The neighbor, isolation, edge sets and Green value are conclusions.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete D1/D2 alternatives, including actual connected components
and all source and determinant values. The hypotheses describe the actual
separated source components preceding the manuscript's family-D reduction;
no closed edge, isolated root, or numerical row is supplied. -/
theorem familyD_source_rows
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
      (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    ∃ M, G.Adj C M ∧ weight C = 2 ∧ weight M = 2 ∧
      G.neighborFinset C = {M} ∧ G.neighborFinset M = {C} ∧
      (∀ i, G.Reachable C i ↔ i = C ∨ i = M) ∧
      (∀ i, ¬ G.Adj B i) ∧ (∀ i, ¬ G.Adj D i) ∧
      (∀ i, ¬ G.Adj T i) ∧ (∀ i, ¬ G.Adj U i) ∧
      1 - dotProduct (threeMarkedSource C B D) coeff = 1 / 3 ∧
      -1 + dotProduct (fun i => (weight i : ℚ) - 2) coeff = 1 / 3 ∧
      dotProduct (threeMarkedSource C B D)
        ((graphWeightMatrix G (fun i => (weight i : ℚ)))⁻¹ *ᵥ
          threeMarkedSource C B D) = 4 / 3 ∧
      ((G.edgeFinset = {s(C, M)} ∧
        (Finset.univ \ ({C, M, B, D, T, U} : Finset V)).card = 4 ∧
        (∀ i ∈ Finset.univ \ ({C, M, B, D, T, U} : Finset V),
          weight i = 2 ∧ ∀ j, ¬ G.Adj i j) ∧
        (graphWeightMatrix G (fun i => (weight i : ℚ))).det = 3888 ∧
        (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
          (threeMarkedSource C B D) (-1)).det = 1296) ∨
      (∃ x y, G.Adj x y ∧ x ∉ ({C, M, B, D, T, U} : Finset V) ∧
        y ∉ ({C, M, B, D, T, U} : Finset V) ∧ weight x = 2 ∧ weight y = 2 ∧
        G.edgeFinset = {s(C, M), s(x, y)} ∧
        (Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V)).card = 2 ∧
        (∀ i ∈ Finset.univ \ ({x, y, C, M, B, D, T, U} : Finset V),
          weight i = 2 ∧ ∀ j, ¬ G.Adj i j) ∧
        (graphWeightMatrix G (fun i => (weight i : ℚ))).det = 2916 ∧
        (borderedGram (graphWeightMatrix G (fun i => (weight i : ℚ)))
          (threeMarkedSource C B D) (-1)).det = 972)) := by
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
  obtain ⟨M, hCM, hC, hM, hnC, hnM, hcomponent⟩ :=
    graph_canonical_green_two_thirds_closed_edge G w C (isUnit_of_posDef hA)
      hG (by omega) hcanonical' hgreen
  have hCnat : weight C = 2 := by
    change (weight C : ℚ) = 2 at hC
    exact_mod_cast hC
  have hMnat : weight M = 2 := by
    change (weight M : ℚ) = 2 at hM
    exact_mod_cast hM
  have hg : dotProduct (threeMarkedSource C B D)
      ((graphWeightMatrix G w)⁻¹ *ᵥ threeMarkedSource C B D) = 4 / 3 := by
    rw [hell, hvol] at hprojection
    nlinarith only [hprojection]
  have hneBD : B ≠ D := by
    intro h
    subst D
    exact hBD (SimpleGraph.Reachable.refl B)
  refine ⟨M, hCM, hCnat, hMnat, hnC, hnM, hcomponent,
    hBi, hDi, hTi, hUi, hell, hvol, hg, ?_⟩
  exact familyD_determinants (𝕜 := ℚ) G weight C M B D T U hcard
    hCnat hMnat hB hD hT hU hneBD hTB hTD hUB hUD hTU
    hCM hnC hnM hBi hDi hTi hUi hedges hother (isUnit_of_posDef hA) hg

end KltDP.LinearAlgebra
