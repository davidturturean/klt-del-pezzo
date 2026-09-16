import KltDP.LinearAlgebra.CanonicalComponentSeparation
import KltDP.LinearAlgebra.BetaThreeCoreContact

/-!
# Component hypotheses derived from the candidate-forest source data

The matrix, its inverse coefficients, the marked length, the volume and the
projection identity are those of the actual weighted graph. The canonical
row equation and every one-higher-vertex component predicate are conclusions.
The component of C is either canonical, or beta is three and it reaches the
unique extra weight-three vertex. The latter case is necessary for families
A and B; canonical C cannot be asserted for every source forest.

This composes the proved shortest-path, charge and concavity theorems. It
does not assume rooted-table membership, fixed components, or final rows.
No geometric realization is constructed. The forest/cardinality/valency and
upper-coefficient hypotheses unused by this separation stage are omitted.

Reuse: pinned Mathlib's inverse multiplication and actual Reachable relation
are sufficient. The current official Connected API and the separate
PositiveDefiniteTreeLattice library were also inspected; no source-specific
charge separation theorem or compatible additional port is needed here.
-/

namespace KltDP.LinearAlgebra

open Matrix SimpleGraph

variable {V : Type*}

/-- Actual higher-weight uniqueness supplies the component predicate used
in the scalar and rooted-tree reductions. Natural weights at least two are
essential to conclude equality with two away from the root. -/
theorem single_heavy_component_of_reachable_unique
    (G : SimpleGraph V) (weight : V → ℕ)
    (hweight : ∀ v, 2 ≤ weight v)
    (hunique : ∀ x y, 2 < weight x → 2 < weight y → G.Reachable x y → x = y) :
    ∀ root, 3 ≤ weight root →
      ∀ v, G.Reachable root v → v ≠ root → weight v = 2 := by
  intro root hroot v hreach hne
  have hv := hweight v
  by_contra hnot
  have hvheavy : 2 < weight v := by omega
  exact hne (hunique root v (by omega) hvheavy hreach).symm

/-- Once C is separated from the cores, either its component is canonical
or it contains an actual extra vertex. If any two distinct extras force
canonical C, that extra is the only extra in the entire graph. No list or
cardinality of extras is supplied to this logical adapter. -/
theorem canonical_component_or_unique_extra
    (G : SimpleGraph V) (weight : V → ℕ) (C B D : V)
    (hother : ∀ v, v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hCB : ¬ G.Reachable C B) (hCD : ¬ G.Reachable C D)
    (htwo : (∃ t u, t ≠ u ∧ t ≠ B ∧ t ≠ D ∧ u ≠ B ∧ u ≠ D ∧
      weight t = 3 ∧ weight u = 3) →
        ∀ v, G.Reachable C v → weight v = 2) :
    (∀ v, G.Reachable C v → weight v = 2) ∨
      ∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧ G.Reachable C T ∧
        ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2 := by
  classical
  by_cases hcanonical : ∀ v, G.Reachable C v → weight v = 2
  · exact Or.inl hcanonical
  · push_neg at hcanonical
    obtain ⟨T, hCT, hTnot⟩ := hcanonical
    have hTB : T ≠ B := by intro h; subst T; exact hCB hCT
    have hTD : T ≠ D := by intro h; subst T; exact hCD hCT
    have hT : weight T = 3 := (hother T hTB hTD).resolve_left hTnot
    refine Or.inr ⟨T, hTB, hTD, hT, hCT, ?_⟩
    intro v hvB hvD hvT
    rcases hother v hvB hvD with hv | hv
    · exact hv
    · have hcanonical := htwo ⟨T, v, Ne.symm hvT, hTB, hTD, hvB, hvD, hT, hv⟩
      have hbad := hcanonical T hCT
      omega

section Finite

variable [Fintype V] [DecidableEq V]

/-- The canonical row equation follows from the actual inverse definition
of the coefficients. It is not an independent assumption on a surrogate
matrix or source vector. -/
theorem candidate_graph_source_row
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2)) :
    graphWeightMatrix G (fun v => (weight v : ℚ)) *ᵥ coeff =
      fun v => (weight v : ℚ) - 2 := by
  let A := graphWeightMatrix G (fun v => (weight v : ℚ))
  letI : Invertible A := (isUnit_of_posDef hA).invertible
  change A *ᵥ coeff = fun v => (weight v : ℚ) - 2
  change coeff = A⁻¹ *ᵥ (fun v => (weight v : ℚ) - 2) at hsolve
  rw [hsolve, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The retained component hypotheses of families C, D and E, and the
necessary A/B alternative, are derived from the original graph-matrix
source data. In particular neither canonical C nor single-heavy components
are premises. The last alternative also proves that any noncanonical C
component occurs at beta three and contains the unique global extra. -/
theorem candidate_forest_component_separation
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : V → ℕ) (coeff : V → ℚ)
    (C B D : V) (β : ℕ)
    (hβ : β = 3 ∨ β = 4 ∨ β = 5)
    (hC : weight C = 2) (hB : weight B = 3) (hD : weight D = β)
    (hother : ∀ v, v ≠ C → v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3)
    (hnadjCB : ¬ G.Adj C B) (hnadjCD : ¬ G.Adj C D)
    (hseparate : ¬ G.Reachable B D) (hedges : G.edgeFinset.card ≤ β - 1)
    (hA : (graphWeightMatrix G (fun v => (weight v : ℚ))).PosDef)
    (hsolve : coeff = (graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
      (fun v => (weight v : ℚ) - 2))
    (hcoeff : ∀ v, 0 ≤ coeff v)
    (hvolume : 0 < 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff)
    (hbudget : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - dotProduct (threeMarkedSource C B D) coeff)
    (hprojection :
      (2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
        (dotProduct (threeMarkedSource C B D)
          ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
            threeMarkedSource C B D) - 1) =
        (1 - dotProduct (threeMarkedSource C B D) coeff)^2) :
    (∀ root, 3 ≤ weight root →
      ∀ v, G.Reachable root v → v ≠ root → weight v = 2) ∧
    ¬ G.Reachable C B ∧ ¬ G.Reachable C D ∧
    (β = 5 → ∀ v, G.Reachable C v → weight v = 2) ∧
    ((∃ t u, t ≠ u ∧ t ≠ B ∧ t ≠ D ∧ u ≠ B ∧ u ≠ D ∧
      weight t = 3 ∧ weight u = 3) →
        ∀ v, G.Reachable C v → weight v = 2) ∧
    ((∀ v, G.Reachable C v → weight v = 2) ∨
      (β = 3 ∧ ∃ T, T ≠ B ∧ T ≠ D ∧ weight T = 3 ∧ G.Reachable C T ∧
        ∀ v, v ≠ B → v ≠ D → v ≠ T → weight v = 2)) := by
  have hβlower : 3 ≤ β := by rcases hβ with h | h | h <;> omega
  have hother' : ∀ v, v ≠ B → v ≠ D → weight v = 2 ∨ weight v = 3 := by
    intro v hvB hvD
    by_cases hvC : v = C
    · exact Or.inl (by simpa only [hvC] using hC)
    · exact hother v hvC hvB hvD
  have hweight : ∀ v, 2 ≤ weight v := by
    intro v
    by_cases hvB : v = B
    · simpa only [hvB, hB] using (by decide : 2 ≤ (3 : ℕ))
    by_cases hvD : v = D
    · rw [hvD, hD]
      omega
    rcases hother' v hvB hvD with h | h <;> omega
  have hBD : B ≠ D := by
    intro h
    subst D
    exact hseparate (SimpleGraph.Reachable.refl B)
  have hrow := candidate_graph_source_row G weight coeff hA hsolve
  have hlength : 0 < 1 - dotProduct (threeMarkedSource C B D) coeff :=
    lt_of_lt_of_le hvolume hbudget
  have hell : 0 < 1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hlength
    linarith only [hlength]
  have hv : 2 - (β : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
      1 - coeff C - coeff B - coeff D := by
    rw [threeMarkedSource_dotProduct] at hbudget
    linarith only [hbudget]
  obtain ⟨hcore, hcharge⟩ := graph_charge_budgets_of_source_budgets
    (fun v => (weight v : ℚ)) coeff C B D (β : ℚ) hBD
      (by change (weight B : ℚ) = 3; simp only [hB, Nat.cast_ofNat])
      (by change (weight D : ℚ) = (β : ℚ); rw [hD]) (hcoeff C) hell hv
  have hunique := heavy_vertices_eq_of_graph_charge G weight coeff B D β hβ
    hweight hB hD hother' hseparate hA hrow hcoeff hcore hcharge
  have hsingle := single_heavy_component_of_reachable_unique G weight hweight hunique
  obtain ⟨hfour, hfive, htwo⟩ :=
    canonical_component_exclusions_of_source_budgets G weight coeff C B D β
      hβ hweight hB hD hother' hseparate hedges hA hrow hcoeff hell hv
  have hcores : ¬ G.Reachable C B ∧ ¬ G.Reachable C D := by
    rcases hβ with h3 | h4 | h5
    · have hD3 : weight D = 3 := by simpa only [h3] using hD
      have hedges3 : G.edgeFinset.card ≤ 2 := by simpa only [h3] using hedges
      have hv3 : -1 + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
          1 - coeff C - coeff B - coeff D := by
        norm_num only [h3, Nat.cast_ofNat, show (2 : ℚ) - 3 = -1 by norm_num] at hv
        exact hv
      have hp3 :
          (-1 + dotProduct (fun v => (weight v : ℚ) - 2) coeff) *
            (dotProduct (threeMarkedSource C B D)
              ((graphWeightMatrix G (fun v => (weight v : ℚ)))⁻¹ *ᵥ
                threeMarkedSource C B D) - 1) =
            (1 - dotProduct (threeMarkedSource C B D) coeff)^2 := by
        simpa only [h3, Nat.cast_ofNat, show (2 : ℚ) - 3 = -1 by norm_num]
          using hprojection
      have hCB := beta_three_core_not_reachable G weight coeff C B D hweight hC hB hD3
        hother' hseparate hnadjCB hedges3 hA hrow hcoeff hell hv3 hp3
      have hmark : threeMarkedSource (𝕜 := ℚ) C D B = threeMarkedSource C B D := by
        unfold threeMarkedSource
        abel
      have hCD := beta_three_core_not_reachable G weight coeff C D B hweight hC hD3 hB
        (fun v hvD hvB => hother' v hvB hvD)
        (fun h => hseparate h.symm) hnadjCD hedges3 hA hrow hcoeff
        (by linarith only [hell]) (by linarith only [hv3])
        (by rw [hmark]; exact hp3)
      exact ⟨hCB, hCD⟩
    · exact hfour (by omega)
    · exact hfour (by omega)
  refine ⟨hsingle, hcores.1, hcores.2, hfive, htwo, ?_⟩
  rcases canonical_component_or_unique_extra G weight C B D hother'
      hcores.1 hcores.2 htwo with hcanonical | ⟨T, hTB, hTD, hT, hCT, hrest⟩
  · exact Or.inl hcanonical
  · have hthree : β = 3 := by
      rcases hβ with h3 | h4 | h5
      · exact h3
      · have hD4 : weight D = 4 := by simpa only [h4] using hD
        have hedges4 : G.edgeFinset.card ≤ 3 := by simpa only [h4] using hedges
        have hv4 : 2 - (4 : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff ≤
            1 - coeff C - coeff B - coeff D := by
          simpa only [h4, Nat.cast_ofNat] using hv
        have hpos4 : 0 < 2 - (4 : ℚ) + dotProduct (fun v => (weight v : ℚ) - 2) coeff := by
          simpa only [h4, Nat.cast_ofNat] using hvolume
        exact (beta_four_single_extra_not_reachable G weight coeff C B D T
          hweight hB hD4 hTB hTD hT hrest hseparate hedges4 hA hrow hcoeff
          hell hv4 hpos4 hCT).elim
      · have hbad := hfive h5 T hCT
        omega
    exact Or.inr ⟨hthree, T, hTB, hTD, hT, hCT, hrest⟩

end Finite

end KltDP.LinearAlgebra
